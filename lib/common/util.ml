(* Shared utilities.  In order:
   - fixed-width bit-vector arithmetic on non-negative [Z.t] values, with
     SMT-LIB's total semantics (division and remainder by zero, and a
     shift by the width or more, have the values the standard fixes);
   - [ExtFile] and [MakeExtFile], the configuration-loading protocol: a
     config field is either a file name or an instance, and every [Config]
     module states how to load its nested configs (a leaf writes
     [Or_error.return]);
   - [Command], external processes run through [bash -c], preferring a tool
     in the working directory to one on the PATH; [sync_command] closes and
     reaps the child whatever its reader raises, and turns an interrupt into
     [Sys_unix.Break] and any other failure into [Shell_error];
   - [Task], a copy of Domainslib's task pool whose promises keep the
     backtrace of a worker's exception;
   - small list-based vectors, matrices, bit vectors, graphs (strongly
     connected components), partial orders, permutations and combinations;
   - [ALMap], a sorted association list compared by polymorphic equality,
     whose [find_exn] raises [Stdlib.Not_found] (not Base's [Not_found_s]). *)
open Core
open Ext

let bvnot n x =
  let mask = Z.(shift_left one n - one) in
  Z.logand (Z.lognot x) mask

let bvand n x y =
  let mask = Z.(shift_left one n - one) in
  Z.logand (Z.logand x y) mask

let bvor n x y =
  let mask = Z.(shift_left one n - one) in
  Z.logand (Z.logor x y) mask

let bvxor n x y =
  let mask = Z.(shift_left one n - one) in
  Z.logand (Z.logxor x y) mask

let bvneg n x =
  let mask = Z.(shift_left one n - one) in
  Z.(logand (lognot x + one) mask)

let bvadd n x y =
  let mask = Z.(shift_left one n - one) in
  Z.((x + y) land mask)

let bvsub n x y =
  let mask = Z.(shift_left one n - one) in
  Z.((x + bvneg n y) land mask)

let bvmul n x y =
  let mask = Z.(shift_left one n - one) in
  Z.(x * y land mask)

let bvsdiv n x y =
  let two_n = Z.shift_left Z.one n in
  let half = Z.shift_left Z.one (n - 1) in
  let to_signed z = if Z.geq z half then Z.sub z two_n else z in
  let from_signed z = Z.erem z two_n in
  let sx = to_signed x in
  let sy = to_signed y in
  if Z.equal sy Z.zero then
    (* SMT-LIB: bvsdiv s #b0 = all-ones if msb s = 0, else #b1 *)
    if Z.sign sx >= 0 then Z.pred two_n else Z.one
  else from_signed (Z.div sx sy)

let bvudiv n x y =
  let two_n = Z.shift_left Z.one n in
  if Z.equal y Z.zero then Z.pred two_n (* SMT-LIB: bvudiv s #b0 = all-ones *)
  else Z.erem (Z.div x y) two_n

let bvsrem n x y =
  let two_n = Z.shift_left Z.one n in
  let half = Z.shift_left Z.one (n - 1) in
  let to_signed z = if Z.geq z half then Z.sub z two_n else z in
  let from_signed z = Z.erem z two_n in
  let sx = to_signed x in
  let sy = to_signed y in
  if Z.equal sy Z.zero then x (* SMT-LIB: bvsrem s #b0 = s *)
  else from_signed (Z.rem sx sy)

let bvurem _n x y =
  if Z.equal y Z.zero then x (* SMT-LIB: bvurem s #b0 = s *) else Z.rem x y

let bvshl n x y =
  let mask = Z.(shift_left one n - one) in
  (* SMT-LIB: a shift of the width or more gives 0 *)
  if Z.geq y (Z.of_int n) then Z.zero
  else Z.(shift_left x (Z.to_int y) land mask)

(* A shift by at least the number of bits of a non-negative [x] gives 0, which
   is answered without narrowing [y]: the shift amount is a term's value and
   can exceed a native int. *)
let bvlshr x y =
  if Z.sign x >= 0 && Z.geq y (Z.of_int (Z.numbits x)) then Z.zero
  else Z.(shift_right x (Z.to_int y))

let bvashr n x y =
  let mask = Z.(shift_left one n - one) in
  (* SMT-LIB: a shift of the width or more gives all sign bits *)
  if Z.geq y (Z.of_int n) then if Z.testbit x (n - 1) then mask else Z.zero
  else
    let i = Z.(shift_right x (Z.to_int y)) in
    let i' =
      if Z.testbit x (n - 1) then Z.logor i (Z.shift_left mask (n - Z.to_int y))
      else i
    in
    Z.logand i' mask

let int2bv n x =
  let two_n = Z.shift_left Z.one n in
  Z.erem x two_n

let z_to_bin_string_fixed n (x : Z.t) : string =
  let raw = Z.format "%b" x in
  let len = String.length raw in
  if len >= n then String.sub raw ~pos:(len - n) ~len:n
  else String.make (n - len) '0' ^ raw

let required_bits (z : Z.t) : int =
  if Z.equal z Z.zero then 1
  else if Z.sign z > 0 then
    (* minimum bits needed to represent positive z in binary (unsigned) *)
    Z.numbits z
  else
    (* minimum bits needed to represent z in 2's complement, using
     abs(z + 1) since 2's complement encodes -z as ~z + 1 *)
    Z.numbits (Z.abs (Z.add z Z.one)) + 1

let min_num2s bits is_signed =
  if is_signed then
    let bits = bits - 1 in
    Z.(one lsl bits)
  else Z.zero

let max_num2s bits is_signed =
  if is_signed then
    let bits = bits - 1 in
    Z.((one lsl bits) - one)
  else Z.((one lsl bits) - one)

let min_num bits is_signed =
  if is_signed then
    let bits = bits - 1 in
    Z.(-(one lsl bits))
  else Z.zero

let max_num bits is_signed = max_num2s bits is_signed

module ExtFile = struct
  type 'a t = Filename of string | Instance of 'a [@@deriving yojson]

  let unwrap = function
    | Filename name ->
        Error
          (Error.of_thunk (fun () -> sprintf "Filename %s cannot unwrap" name))
    | Instance a -> Ok a

  let unwrap_or_abort = function
    | Filename name ->
        ignore (printf "Filename %s cannot unwrap" name);
        assert false
    | Instance a -> a
end

type 'a ext_file = 'a ExtFile.t [@@deriving yojson]

(* The value a config reader builds from a JSON literal, for a field's
   [@default] whose value is not a constant: [config_default reader "{}"] is a
   nested record with every field at its own default, and a variant carrying a
   record is written the way a config file writes it.  Going through the reader
   makes the default mean exactly what the same text in a config file means.
   Raises when the literal does not read, which the first load of any config of
   the enclosing type exercises. *)
let config_default (reader : Yojson.Safe.t -> ('a, string) result)
    (json : string) : 'a =
  match reader (Yojson.Safe.from_string json) with
  | Ok x -> x
  | Error msg -> failwith (sprintf "config_default %s: %s" json msg)

(* The config-loading protocol -- [Filename] -> parse the JSON -> recurse into
   the nested configs -> [Instance] -- was hand-copied into 62 [Config] modules,
   and eight of the copies left the recursion out.  All
   eight were leaves, so nothing was broken; what was missing was the
   *distinction* between "a leaf, the recursion is unnecessary" and "the
   recursion was forgotten", since adding one nested [ext_file] field to such a
   module compiles cleanly and then fails at run time with [Filename ... cannot
   unwrap], far from the edit.  A module built through this functor has to state
   the answer: a leaf writes [let instantiate = Or_error.return]. *)
(* Every config module built through [MakeExtFile] registers itself here when
   its module is initialised: a loader that reads a file, instantiates its
   nested configs and prints the instantiated value back as JSON, and a reader
   that parses JSON without instantiating anything and prints it back.  Nothing
   on the solving path reads this; it exists so that a self-check can print the
   configuration a binary builds from every file under [config/] and compare
   two binaries, which is how a change to a field's default, or a config file
   rewritten to state only what differs from the defaults, is shown to leave
   every instantiated configuration as it was.  Names are not unique (two
   template modules share one), so the list keeps every registration. *)
module ConfigRegistry = struct
  type entry = {
    name : string;
    load : string -> Yojson.Safe.t Or_error.t;
    reparse : Yojson.Safe.t -> (Yojson.Safe.t, string) result;
  }

  let entries : entry list ref = ref []
end

module MakeExtFile (X : sig
  type t

  val of_yojson : Yojson.Safe.t -> (t, string) result
  val to_yojson : t -> Yojson.Safe.t

  val name : string
  (** the module's name as it appears in "Invalid <name> Configuration", the
      only diagnostic a user gets for a bad config *)

  val instantiate : t -> t Or_error.t
  (** load the nested configs; a leaf writes [Or_error.return] *)
end) : sig
  val load_ext_file : X.t ExtFile.t -> X.t ExtFile.t Or_error.t
end = struct
  (* An [Instance] is instantiated too, not passed through: a config written
     inline (a batch driver's composed chain, a [config_default] literal) can
     leave out a nested-config field, whose default is a [Filename], and that
     file has to be loaded like one the text names.  Passing an [Instance]
     through left such a field a [Filename] that fails at its first use.
     Instantiating is idempotent: a value with no [Filename] left in it comes
     back as it was. *)
  let load_ext_file = function
    | ExtFile.Instance x ->
        Or_error.map (X.instantiate x) ~f:(fun x -> ExtFile.Instance x)
    | ExtFile.Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match X.of_yojson raw_json with
        | Ok x -> X.instantiate x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid %s Configuration (%s): %s" X.name filename msg)

  let () =
    let load filename =
      Or_error.bind (load_ext_file (ExtFile.Filename filename)) ~f:(function
        | ExtFile.Instance x -> Ok (X.to_yojson x)
        | ExtFile.Filename _ -> Or_error.error_string "not instantiated")
    in
    let reparse json = Result.map (X.of_yojson json) ~f:X.to_yojson in
    ConfigRegistry.entries :=
      { ConfigRegistry.name = X.name; load; reparse } :: !ConfigRegistry.entries
end

module LexingHelper = struct
  let get_position_string (lexbuf : Lexing.lexbuf) =
    let pos = lexbuf.lex_curr_p in
    sprintf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

  let print_error_information lexbuf =
    let st = Lexing.lexeme_start_p lexbuf in
    let en = Lexing.lexeme_end_p lexbuf in
    Printf.fprintf stderr "File \"%s\", line %d, characters %d-%d:\n"
      st.Lexing.pos_fname st.Lexing.pos_lnum
      (st.Lexing.pos_cnum - st.Lexing.pos_bol)
      (en.Lexing.pos_cnum - en.Lexing.pos_bol)
end

let rec map_channel_lines (f : string -> 'a) (chan : In_channel.t) : 'a list =
  match In_channel.input_line chan with
  | None -> []
  | Some line -> f line :: map_channel_lines f chan

let input_lines ch = String.concat ~sep:"\n" @@ map_channel_lines Fn.id ch

let output_lines ch lines =
  List.iter lines ~f:(fun line -> Out_channel.output_string ch (line ^ "\n"));
  Out_channel.flush ch

module Command : sig
  exception Shell_error of string

  val resolve_tool : string -> string
  val async_command : string -> string list -> Core_unix.Process_channels.t

  val read_process :
    string -> f:(In_channel.t -> 'a) -> 'a * Core_unix.Exit_or_signal.t

  val sync_command : string -> string list -> string list -> string list
end = struct
  exception Shell_error of string

  (* README tells users to place external binaries in the current directory;
     prefer [./tool] when it is there and fall back to [tool] on PATH, so every
     wrapper resolves a tool the same way *)
  let resolve_tool tool =
    let local = "./" ^ tool in
    if Sys_unix.is_file_exn local then local else tool

  let async_command (name : string) (arguments : string list) :
      Core_unix.Process_channels.t =
    Core_unix.open_process_full
      (sprintf "bash -c '%s %s 2>&1'" name (String.concat ~sep:" " arguments))
      ~env:(Core_unix.environment ())

  (* close_process_in owns both channel closure and waiting for the shell.
     Reading (including a raising signal handler) must stay inside its scope. *)
  let read_process command ~f =
    let status = ref None in
    let channel = Core_unix.open_process_in command in
    let value =
      Exn.protect
        ~f:(fun () -> f channel)
        ~finally:(fun () -> status := Some (Core_unix.close_process_in channel))
    in
    (value, Option.value_exn !status)

  let sync_command (name : string) (arguments : string list)
      (input : string list) : string list =
    let pcs = async_command name arguments in
    let status = ref None in
    (* Failed buffered writes still need stdin closed before close/wait. *)
    let out =
      Exn.protect
        ~f:(fun () ->
          output_lines pcs.stdin input;
          map_channel_lines Fn.id pcs.stdout)
        ~finally:(fun () ->
          Out_channel.close_no_err pcs.stdin;
          status := Some (Core_unix.close_process_full pcs))
    in
    match Option.value_exn !status with
    | Ok _ -> out
    | Error (`Signal x) when Signal.equal x Signal.int -> raise Sys_unix.Break
    | Error _ -> raise (Shell_error (String.concat ~sep:"\n" out))
end

module Task = struct
  (* Copied from Domainslib.Task*)

  type 'a task = unit -> 'a

  (* A task that raised keeps the backtrace of the raise, and [await] re-raises
     with it, so that an exception escaping a worker domain is reported where
     it was raised rather than where it was awaited. *)
  type 'a promise = ('a, exn * Stdlib.Printexc.raw_backtrace) result option Atomic.t

  exception TasksActive

  type task_msg = Task : 'a task * 'a promise -> task_msg | Quit : task_msg

  type pool = {
    domains : unit Domain.t array;
    task_chan : task_msg Domainslib__Multi_channel.t;
  }

  let do_task f p =
    try
      let res = f () in
      Atomic.set p (Some (Ok res))
    with e -> (
      let bt = Stdlib.Printexc.get_raw_backtrace () in
      Atomic.set p (Some (Error (e, bt)));
      match e with TasksActive -> raise e | _ -> ())

  let setup_pool ~num_additional_domains =
    let task_chan =
      Domainslib__Multi_channel.make (num_additional_domains + 1)
    in
    (* backtrace recording is per domain in OCaml 5 and a spawned domain
       starts without it, so a worker records exactly when the domain that
       made the pool does *)
    let record = Stdlib.Printexc.backtrace_status () in
    let rec worker () =
      match Domainslib__Multi_channel.recv task_chan with
      | Quit -> Domainslib__Multi_channel.clear_local_state task_chan
      | Task (t, p) ->
          do_task t p;
          worker ()
    in
    let domains =
      Array.init num_additional_domains ~f:(fun _ ->
          Domain.spawn (fun () ->
              Stdlib.Printexc.record_backtrace record;
              worker ()))
    in
    { domains; task_chan }

  let async pool task =
    let p = Atomic.make None in
    Domainslib__Multi_channel.send pool.task_chan (Task (task, p));
    p

  let rec await pool promise =
    match Atomic.get promise with
    | None ->
        (try
           match Domainslib__Multi_channel.recv_poll pool.task_chan with
           | Task (t, p) -> do_task t p
           | Quit -> raise TasksActive
         with Exit -> Domain.cpu_relax ());
        await pool promise
    | Some (Ok v) -> v
    | Some (Error (e, bt)) -> Stdlib.Printexc.raise_with_backtrace e bt

  let teardown_pool pool =
    for _i = 1 to Array.length pool.domains do
      Domainslib__Multi_channel.send pool.task_chan Quit
    done;
    Domainslib__Multi_channel.clear_local_state pool.task_chan;
    Array.iter ~f:Domain.join pool.domains

  let parallel_for_reduce ?(chunk_size = 0) ~start ~finish ~body pool reduce_fun
      init =
    let chunk_size =
      if chunk_size > 0 then chunk_size
      else
        let n_domains = Array.length pool.domains + 1 in
        let n_tasks = finish - start + 1 in
        if n_domains = 1 then n_tasks else max 1 (n_tasks / (8 * n_domains))
    in
    let rec work s e =
      if e - s < chunk_size then
        let rec loop i acc =
          if i > e then acc else loop (i + 1) (reduce_fun acc (body i))
        in
        loop s init
      else
        let d = s + ((e - s) / 2) in
        let p = async pool (fun _ -> work s d) in
        let right = work (d + 1) e in
        let left = await pool p in
        reduce_fun left right
    in
    work start finish

  let parallel_for ?(chunk_size = 0) ~start ~finish ~body pool =
    let chunk_size =
      if chunk_size > 0 then chunk_size
      else
        let n_domains = Array.length pool.domains + 1 in
        let n_tasks = finish - start + 1 in
        if n_domains = 1 then n_tasks else max 1 (n_tasks / (8 * n_domains))
    in
    let rec work pool fn s e =
      if e - s < chunk_size then
        for i = s to e do
          fn i
        done
      else
        let d = s + ((e - s) / 2) in
        let left = async pool (fun _ -> work pool fn s d) in
        work pool fn (d + 1) e;
        await pool left
    in
    work pool body start finish

  let parallel_scan pool op elements =
    let scan_part op elements prefix_sum start finish =
      assert (Array.length elements > finish - start);
      for i = start + 1 to finish do
        prefix_sum.(i) <- op prefix_sum.(i - 1) elements.(i)
      done
    in
    let add_offset op prefix_sum offset start finish =
      assert (Array.length prefix_sum > finish - start);
      for i = start to finish do
        prefix_sum.(i) <- op offset prefix_sum.(i)
      done
    in
    let n = Array.length elements in
    let p = Array.length pool.domains + 1 in
    let prefix_s = Array.copy elements in
    parallel_for pool ~chunk_size:1 ~start:0 ~finish:(p - 1) ~body:(fun i ->
        let s = i * n / p in
        let e = ((i + 1) * n / p) - 1 in
        scan_part op elements prefix_s s e);
    (if p > 2 then
       let x = ref prefix_s.((n / p) - 1) in
       for i = 2 to p do
         let ind = (i * n / p) - 1 in
         x := op prefix_s.(ind) !x;
         prefix_s.(ind) <- !x
       done);
    parallel_for pool ~chunk_size:1 ~start:1 ~finish:(p - 1) ~body:(fun i ->
        let s = i * n / p in
        let e = ((i + 1) * n / p) - 2 in
        let offset = prefix_s.(s - 1) in
        add_offset op prefix_s offset s e);
    prefix_s

  (* new functions *)
  let rec await_any_promise pool (promises : 'a promise list) =
    ignore @@ Core_unix.nanosleep 0.1;
    Domain.cpu_relax ();
    match
      List.find_map promises ~f:(fun promise ->
          match Atomic.get promise with None -> None | a -> a)
    with
    | None -> await_any_promise pool promises
    | Some (Ok v) -> v
    | Some (Error (v, bt)) -> Stdlib.Printexc.raise_with_backtrace v bt
end

module Array2D = struct
  let remove_column a idx = Array.map a ~f:(fun a' -> Array.remove a' idx)
  let num_columns a = if Array.is_empty a then 0 else Array.length a.(0)
  let column_of a idx = Array.map a ~f:(fun a' -> a'.(idx))
end

module ListSet = struct
  let cup cmp s1 s2 =
    List.dedup_and_sort ~compare:cmp @@ List.merge ~compare:cmp s1 s2

  let sub cmp s1 s2 =
    let rec rep cmp s1 s2 res =
      match s1 with
      | [] -> res
      | h1 :: t1 -> (
          match s2 with
          | [] -> List.rev s1 @ res
          | h2 :: t2 ->
              let r = cmp h1 h2 in
              if r < 0 then rep cmp t1 s2 (h1 :: res)
              else if r > 0 then rep cmp s1 t2 res
              else rep cmp t1 s2 res)
    in
    List.rev @@ rep cmp s1 s2 []

  let cap cmp s1 s2 =
    let rec rep cmp s1 s2 res =
      match s1 with
      | [] -> res
      | h1 :: t1 -> (
          match s2 with
          | [] -> res
          | h2 :: t2 ->
              let r = cmp h1 h2 in
              if r < 0 then rep cmp t1 s2 res
              else if r > 0 then rep cmp s1 t2 res
              else rep cmp t1 s2 (h1 :: res))
    in
    List.rev @@ rep cmp s1 s2 []
end

(** Vectors *)
module Vector = struct
  type 'a t = 'a list

  let make v n = List.duplicate v n
  let pr_float = List.pr Float.pr " "
  let pr_bool = List.pr Bool.pr " "
  let map f = List.map f
  let dot xs ys = List.sum_float @@ List.map2_exn xs ys ~f:(fun x y -> x *. y)
  let array_of = Array.of_list
  let of_array = Array.to_list

  (** [multiply [x1; ... ; xm] [y1; ... ; yn]] returns
      [[f x1 y1; ... ; f x1 yn; ... ; f xm y1; ... ; f xm yn]] *)
  let multiply f xs ys = List.concat_map ~f:(fun x -> List.map ~f:(f x) ys) xs

  (** [product f [[1; 2; 3]; [4]; [5; 6]]] returns
      [[f [1; 4; 5]; f [1; 4; 6]; f [2; 4; 5]; f [2; 4; 6]; f [3; 4; 5]; f [3;
       4; 6]]] *)
  let product f xss = List.map ~f (List.n_cartesian_product xss)

  let producti f xss =
    let cnt = ref 0 in
    let rec aux ac xss =
      match xss with
      | [] ->
          let res = [ f !cnt ac ] in
          cnt := !cnt + 1;
          res
      | xs :: xss -> xs |> List.concat_map ~f:(fun x -> aux (ac @ [ x ]) xss)
    in
    aux [] xss

  (** [product_ f \[xs1; ...; xsn\]] returns
      [multiply f (...multiply f (multiply f xs1 xs2) xs3...) xsn]
      @require n > 0 *)
  let product_ f = function
    | [] -> assert false
    | xs :: xss -> List.fold_left ~f:(multiply f) ~init:xs xss
end

(** Matrices *)
module Matrix = struct
  type 'a t = 'a Vector.t list

  let make v m n = List.duplicate (List.duplicate v n) m

  let pr_float ppf m =
    Format.fprintf ppf "@[<v>%a@]" (List.pr Vector.pr_float "@,") m

  let rec transpose xss =
    if List.for_all ~f:List.is_empty xss then []
    else
      let xs, xss =
        xss
        |> List.map ~f:(function x :: xs -> (x, xs) | _ -> assert false)
        |> List.unzip
      in
      xs :: transpose xss

  let cols = List.length
  let rows xss = xss |> List.hd_exn |> List.length
  let elem i j xss = List.nth_exn (List.nth_exn xss i) j

  let replace i j v xss =
    let ys = List.nth_exn xss i in
    List.take xss i
    @ [ List.take ys j @ [ v ] @ List.drop ys (j + 1) ]
    @ List.drop xss (i + 1)

  let thread xss =
    let minlength = Integer.min_list (List.map ~f:List.length xss) in
    List.map
      (List.range ~stop:`inclusive 0 (minlength - 1))
      ~f:(fun k -> List.map ~f:(fun ys -> List.nth ys k) xss)

  let row i xss = List.nth xss i

  let column i xss =
    List.nth (thread (*@todo replace this with transpose*) xss) i

  let diag_rd (i, j) xss =
    let n = List.length xss in
    List.range ~stop:`inclusive (-n) n
    |> List.filter ~f:(fun k ->
        i + k >= 0 && i + k < n && j + k >= 0 && j + k < n)
    |> List.map ~f:(fun k -> List.nth_exn (List.nth_exn xss (i + k)) (j + k))

  let diag_ld (i, j) xss =
    let n = List.length xss in
    List.range ~stop:`inclusive (-n) n
    |> List.filter ~f:(fun k ->
        i + k >= 0 && i + k < n && j - k >= 0 && j - k < n)
    |> List.map ~f:(fun k -> List.nth_exn (List.nth_exn xss (i + k)) (j - k))

  let map f = List.map ~f:(List.map ~f)

  let id one zero n =
    List.init n ~f:(fun i ->
        List.init n ~f:(fun j -> if i = j then one else zero))

  let array_of xss = Array.of_list (List.map ~f:Array.of_list xss)
  let of_array ar = Array.to_list (Array.map ~f:Array.to_list ar)
end

(** Bit vectors *)
module BitVector = struct
  let not =
    List.map ~f:(fun n ->
        if n = 0 then 1 else if n = 1 then 0 else assert false)

  let inc =
    let rec aux = function
      | [] -> assert false
      | 0 :: bv -> 1 :: bv
      | 1 :: bv -> 0 :: aux bv
      | _ -> assert false
    in
    let open Combinator in
    List.rev >> aux >> List.rev

  let dec =
    let rec aux = function
      | [] -> assert false
      | 0 :: bv -> 1 :: aux bv
      | 1 :: bv -> 0 :: bv
      | _ -> assert false
    in
    let open Combinator in
    List.rev >> aux >> List.rev

  let of_nat n =
    assert (n >= 0);
    let rec aux bv n = if n = 0 then bv else aux ((n mod 2) :: bv) (n / 2) in
    if n = 0 then [ 0 ] else aux [] n

  let of_int _bits _n = assert false
  (*
  if n >= 0 then of_nat bits n else inc (not (of_nat bits (-n)))
*)

  let nat_of = List.fold_left ~f:(fun x y -> (x * 2) + y) ~init:0

  let int_of bv =
    if List.hd_exn bv = 0 then nat_of bv
    else if List.hd_exn bv = 1 then -nat_of (not (dec bv))
    else assert false
end

(** Graphs *)
module Graph0 = struct
  (* @todo
     walk can be of the length 0
     trail: walk with no repetition of an edge
     path: walk with no repetition of a vertex

     path <: trail <: walk

     path can be of the length 0
     # a single node is connected

     circuit: trail with the length >= 1 that starts and ends with the same vertex
     cycle: path with the length >= 1 that starts and ends with the same vertex

     cycle <: circuit

     trail/circuit is Eulerian if it contains every edge of the graph
     path/cycle is Hamitonian if it contains every vertex of the graph
  *)

  (** @todo there is a bug related to vertices? *)
  let save_graphviz filename vertices edges =
    let oc = Stdlib.open_out filename in
    let ocf =
      Format.make_formatter (Stdlib.output_substring oc) (fun () ->
          Stdlib.flush oc)
    in
    Format.fprintf ocf "@[<v>digraph flow {@ ";

    List.iter vertices ~f:(fun (vertex, attribute) ->
        Format.fprintf ocf "  \"%s\" %s@ " vertex attribute);
    List.iter edges ~f:(fun (vertex1, vertex2, attribute) ->
        Format.fprintf ocf "  \"%s\" -> \"%s\" %s@ " vertex1 vertex2 attribute);

    Format.fprintf ocf "}@]@?";
    Stdlib.close_out oc

  let succs es v =
    List.filter_map ~f:(fun (v1, v2) -> if v1 = v then Some v2 else None) es

  let preds es v =
    List.filter_map ~f:(fun (v1, v2) -> if v2 = v then Some v1 else None) es

  let rec assign es assigned v root =
    if List.Assoc.mem ~equal:Stdlib.( = ) assigned v then assigned
    else
      List.fold_left (preds es v) ~init:((v, root) :: assigned)
        ~f:(fun assigned v -> assign es assigned v root)

  (** Kosaraju's algorithm *)
  let rec visit es visited l v =
    if List.mem ~equal:Stdlib.( = ) visited v then (visited, l)
    else
      let visited, l =
        List.fold_left (succs es v)
          ~init:(v :: visited, l)
          ~f:(Tuple2.uncurry (visit es))
      in
      (visited, v :: l)

  let scc es =
    let vs = List.map ~f:fst es @ List.map ~f:snd es |> List.dedup_keep_last in
    let _, l =
      List.fold_left vs ~init:([], []) ~f:(Tuple2.uncurry (visit es))
    in
    List.fold_left ~f:(fun assigned v -> assign es assigned v v) ~init:[] l
end

(** Partial orders *)
module PartOrd = struct
  let is_initial ord p =
    Set.for_all ord ~f:(fun (p1, p2) -> Stdlib.(p1 <> p || p1 = p2))

  let preds ord p =
    Set.Poly.filter_map ord ~f:(fun (p1, p2) ->
        if Stdlib.(p2 = p && p1 <> p2) then Some p1 else None)

  let succs ord p =
    Set.Poly.filter_map ord ~f:(fun (p1, p2) ->
        if Stdlib.(p1 = p && p1 <> p2) then Some p1 else None)

  let reflexive_closure_of brel =
    Set.concat_map brel ~f:(fun (e1, e2) ->
        Set.Poly.of_list [ (e1, e1); (e1, e2); (e2, e2) ])

  let rec transitive_closure_of edges =
    let new_edges =
      Set.fold ~init:edges edges ~f:(fun acc (x, y) ->
          Set.fold ~init:acc edges ~f:(fun acc' (a, b) ->
              if Stdlib.(b = x) then Set.add acc' (a, y) else acc'))
    in
    if Set.length edges = Set.length new_edges then edges
    else transitive_closure_of new_edges

  let reflexive_transitive_closure_of brel =
    brel |> transitive_closure_of |> reflexive_closure_of
end

(** Permutations *)
module Permutation = struct
  let permutations n =
    let rec aux = function
      | [] -> []
      | xs ->
          List.concat
          @@ List.init (List.length xs) ~f:(fun i ->
              match List.split_n xs i with
              | xs1, x :: xs2 -> xs1 @ xs2 |> aux |> List.map ~f:(List.cons x)
              | _ -> failwith "")
    in
    aux (List.init n ~f:Fn.id)

  let maps n1 n2 =
    let xs = List.init n1 ~f:Fn.id in
    permutations n2 |> List.map ~f:(List.zip xs)

  let rec perm xs n =
    if n <= 0 then [ [] ]
    else
      xs
      |> List.mapc (fun f x -> List.map ~f:(List.cons x) (perm (f []) (n - 1)))
      |> List.concat
end

(** Combinations *)
module Combination = struct
  let comb2 xs =
    List.concat_mapi xs ~f:(fun i x ->
        List.map ~f:(Tuple2.create x) (List.drop xs (i + 1)))
end

(** Map implemented with asocc list ( Stdlib.(=) can be used for equality check
    ) *)
module ALMap = struct
  type ('k, 'd) t = ('k * 'd) list

  let empty = []
  let is_empty = List.is_empty
  let length = List.length

  let rec add_exn ~key ~data = function
    | [] -> [ (key, data) ]
    | (k, d) :: tl as l ->
        if Stdlib.(key = k) then failwith "key already exists"
        else if Stdlib.(key < k) then (key, data) :: l
        else (k, d) :: add_exn ~key ~data tl

  let rec add_force_exn ~key ~data = function
    | [] -> [ (key, data) ]
    | (k, d) :: tl as l ->
        if Stdlib.(key = k) then
          if Stdlib.(data = d) then l else failwith "key already exists"
        else if Stdlib.(key < k) then (key, data) :: l
        else (k, d) :: add_force_exn ~key ~data tl

  let singleton key data = add_exn ~key ~data empty
  let find_exn = Stdlib.List.assoc
  let to_alist m = m

  let of_alist_exn l =
    List.fold l ~init:empty ~f:(fun acc (key, data) -> add_exn ~key ~data acc)

  let data m = snd @@ List.unzip m
  let map ~f m = List.map m ~f:(fun (k, d) -> (k, f d))
  let mapi ~f m = List.map m ~f:(fun (k, d) -> (k, f k d))

  let force_merge m1 m2 =
    List.fold m2 ~init:m1 ~f:(fun acc (key, data) ->
        add_force_exn ~key ~data acc)

  let force_merge_list = List.fold ~init:empty ~f:force_merge

  let split_lbr m1 m2 =
    let rec aux m1 m2 lefts boths rights =
      match (m1, m2) with
      | [], m2 -> (lefts, boths, m2 @ rights)
      | m1, [] -> (m1 @ lefts, boths, rights)
      | (k1, d1) :: tl1, (k2, d2) :: tl2 ->
          if Stdlib.(k1 = k2) then
            aux tl1 tl2 lefts ((k1, (d1, d2)) :: boths) rights
          else if Stdlib.(k1 < k2) then
            aux tl1 m2 ((k1, d1) :: lefts) boths rights
          else aux m1 tl2 lefts boths ((k2, d2) :: rights)
    in
    aux m1 m2 [] [] []
end
