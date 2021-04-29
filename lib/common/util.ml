open Core

let log2 x = log x /. log 2.

let rand_int () = let n = Random.bits () in if Random.bool () then -n else n

let id x = x

let const c () = c

let ( >> ) f g x = g (f x)

let ( >>= ) x f = match x with None -> None | Some x -> f x

let flip f x y = f y x

let uncurry f (x, y) = f x y
let uncurry3 f (x, y, z) = f x y z

let argmax xs ~f =
  let x_0 = List.hd_exn xs in
  List.fold (List.tl_exn xs)
    ~init:(x_0, f x_0)
    ~f:(fun (x, fx) x' ->
        let fx' = f x' in
        if Stdlib.( > ) fx' fx then (x', fx') else (x, fx))
  |> fst

let argmin xs ~f =
  let x_0 = List.hd_exn xs in
  List.fold (List.tl_exn xs)
    ~init:(x_0, f x_0)
    ~f:(fun (x, fx) x' ->
        let fx' = f x' in
        if Stdlib.( < ) fx' fx then (x', fx') else (x, fx))
  |> fst

(** [fix f eq x] computes the fixed point of [f] modulo [eq] from [x] *)
let rec fix ~f ~equal x =
  let x' = f x in
  if equal x x' then x else fix ~f ~equal x'

let hook enabled before after main =
  if enabled then begin
    before ();
    let ret = main () in
    after ret;
    ret
  end else main ()

module ExtFile = struct
  type 'a t = Filename of string | Instance of 'a [@@deriving yojson]

  let unwrap = function
    | Filename name ->
      Error
        (Error.of_thunk (fun () ->
             Printf.sprintf "Filename %s cannot unwrap" name))
    | Instance a -> Ok a

  let unwrap_or_abort = function
    | Filename name ->
      ignore (Printf.printf "Filename %s cannot unwrap" name);
      assert false
    | Instance a -> a
end

type 'a ext_file = 'a ExtFile.t [@@deriving yojson]
(** type alias for convinience *)

module Ordinal = struct
  type t = int

  let make n = n

  let string_of n =
    if n = 11 || n = 12 || n = 13 then Printf.sprintf "%dth" n
    else
      Printf.sprintf
        ( match n mod 10 with
          | 1 -> "%dst"
          | 2 -> "%dnd"
          | 3 -> "%drd"
          | _ -> "%dth" )
        n
end

module Pair = struct
  let map_fst f (x, y) = (f x, y)

  let map_snd f (x, y) = (x, f y)

  let map f g (x, y) = (f x, g y)
end

module List = struct
  include List

  let rec classify eqrel = function
    | [] -> []
    | x :: xs ->
      let t, f = List.partition_tf ~f:(eqrel x) xs in
      (x :: t) :: classify eqrel f

  let rec power f = function
    | [] -> [ [] ]
    | x :: xs ->
      power f xs
      |> List.map ~f:(fun ys -> f x |> List.map ~f:(fun y -> y :: ys))
      |> List.concat


  let zip3_exn lst1 lst2 lst3 = 
    let rec aux lst1 lst2 lst3 ret =
      match lst1, lst2, lst3 with
      | (hd1::tl1), (hd2::tl2), (hd3::tl3) -> aux tl1 tl2 tl3 ((hd1, hd2, hd3)::ret)
      | [], [], [] -> ret
      | _ -> assert false
    in aux (List.rev lst1) (List.rev lst2) (List.rev lst3) []

  (*let unzip4 = List.fold_right ~f:(fun (a, b, c, d) (al, bl, cl, dl) -> (a::al, b::bl, c::cl, d::dl)) ~init:([], [], [], []) in*)
  let unzip4 lst =
    let rec aux (ws, xs, ys, zs) = function
      | [] -> (ws, xs, ys, zs)
      | (w, x, y, z) :: lst -> aux (w :: ws, x :: xs, y :: ys, z :: zs) lst
    in
    List.rev lst |> aux ([], [], [], [])

  let unzip5 lst =
    let rec aux (vs, ws, xs, ys, zs) = function
      | [] -> (vs, ws, xs, ys, zs)
      | (v, w, x, y, z) :: lst ->
        aux (v :: vs, w :: ws, x :: xs, y :: ys, z :: zs) lst
    in
    List.rev lst |> aux ([], [], [], [], [])

  let unzip6 lst =
    let rec aux (us, vs, ws, xs, ys, zs) = function
      | [] -> (us, vs, ws, xs, ys, zs)
      | (u, v, w, x, y, z) :: lst ->
        aux (u :: us, v :: vs, w :: ws, x :: xs, y :: ys, z :: zs) lst
    in
    List.rev lst |> aux ([], [], [], [], [], [])

  let unzip7 lst =
    let rec aux (ts, us, vs, ws, xs, ys, zs) = function
      | [] -> (ts, us, vs, ws, xs, ys, zs)
      | (t, u, v, w, x, y, z) :: lst ->
        aux (t :: ts, u :: us, v :: vs, w :: ws, x :: xs, y :: ys, z :: zs) lst
    in
    List.rev lst |> aux ([], [], [], [], [], [], [])

  let partition2_map t ~f =
    let rec loop t fst snd =
      match t with
      | [] -> rev fst, rev snd
      | x :: t ->
        (match f x with
         | `Fst y -> loop t (y :: fst) snd
         | `Snd y -> loop t fst (y :: snd))
    in
    loop t [] []

  let cartesian_map ?(init = []) ~f l1 l2 =
    List.fold l1 ~init ~f:(fun acc x1 ->
        List.fold l2 ~init:acc ~f:(fun acc x2 -> f x1 x2 :: acc))
end

module Set = struct
  include Set

  let of_map m = Set.Poly.of_list @@ Map.Poly.to_alist m

  let cartesian_map ?(init = Set.Poly.empty) ~f s1 s2 =
    Set.Poly.fold s1 ~init ~f:(fun acc x1 ->
        Set.Poly.fold s2 ~init:acc ~f:(fun acc x2 -> Set.Poly.add acc (f x1 x2)))

  let fold_distinct_pairs ?(init = Set.Poly.empty) ~f s =
    Set.Poly.fold s ~init ~f:(fun acc x1 ->
        Set.Poly.fold s ~init:acc ~f:(fun acc x2 ->
            if Stdlib.compare x1 x2 = 0 then acc else Set.Poly.add acc (f x1 x2)))

  let unzip s = (Set.Poly.map s ~f:fst, Set.Poly.map s ~f:snd)

  let concat s = Set.Poly.union_list @@ Set.Poly.to_list s
  let concat_map s ~f =
    Set.Poly.fold s ~init:Set.Poly.empty ~f:(fun acc x -> Set.Poly.union acc (f x))

  let partition_map s ~f =
    Set.Poly.fold s ~init:(Set.Poly.empty, Set.Poly.empty) ~f:(fun (s1, s2) x ->
        match f x with
        | First y -> Set.Poly.add s1 y, s2
        | Second y -> s1, Set.Poly.add s2 y)

  let representatives s ~equiv =
    Set.Poly.group_by s ~equiv
    |> List.map ~f:Set.Poly.choose_exn
    |> Set.Poly.of_list
end

module Map = struct
  include Map

  let of_set s = Map.Poly.of_alist_exn @@ Set.Poly.to_list s
  let to_set m = Set.Poly.of_list @@ Map.Poly.to_alist m

  let cartesian_map ?(init = Map.Poly.empty) ~f m1 m2 =
    Map.Poly.fold m1 ~init ~f:(fun ~key:key1 ~data:data1 acc ->
        Map.Poly.fold m2 ~init:acc ~f:(fun ~key:key2 ~data:data2 acc -> f acc key1 data1 key2 data2))

  let rename_keys map ~f =
    Map.Poly.fold map ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
        match f key with
        | None -> Map.Poly.add_exn acc ~key ~data
        | Some key' -> Map.Poly.add_exn acc ~key:key' ~data)
  let rename_keys_map rename_map map =
    rename_keys map ~f:(Map.Poly.find rename_map)

  let change_keys map ~f =
    Map.Poly.fold map ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
        let newkey = f key in
        if Map.Poly.mem acc newkey then assert false
        else Map.Poly.add_exn acc ~key:newkey ~data)

  let force_merge map1 map2 = Map.Poly.merge map1 map2 ~f:(fun ~key:_ -> function
      | `Left data | `Right data -> Some data
      | `Both (data1, data2) -> if Stdlib.(=) data1 data2 then Some data1 else assert false)

  let force_merge_list ms = List.fold ms ~init:Map.Poly.empty ~f:force_merge
end

module Array = struct
  include Array

  let remove a idx = Array.filteri a ~f:(fun i _ -> i <> idx)
end

module Array2D = struct
  let remove_column a idx = Array.map a ~f:(fun a' -> Array.remove a' idx)
  let num_columns a = if Array.is_empty a then 0 else Array.length a.(0)
  let column_of a idx = Array.map a ~f:(fun a' -> a'.(idx))
end

module Command : sig
  exception Shell_error of string

  val async_command : string -> string list -> Unix.Process_channels.t

  val sync_command : string -> string list -> string list -> string list

  val output_lines : string list -> Out_channel.t -> unit

  val input_lines : In_channel.t -> string list
end = struct
  exception Shell_error of string

  let output_lines (output : string list) (chan : Out_channel.t) : unit =
    List.iter
      ~f:(fun line -> Out_channel.output_string chan (line ^ "\n"))
      output;
    Out_channel.flush chan

  let rec do_channel_lines (f : string -> 'a) (chan : In_channel.t) : 'a list =
    match In_channel.input_line chan with
    | None -> []
    | Some line -> f line :: do_channel_lines f chan

  let input_lines = do_channel_lines (fun x -> x)

  let unlines : string list -> string = String.concat ~sep:"\n"

  let async_command (name : string) (arguments : string list) :
    Unix.Process_channels.t =
    Unix.open_process_full
      (Printf.sprintf "bash -c '%s %s 2>&1'" name
         (String.concat ~sep:" " arguments))
      ~env:(Unix.environment ())

  let sync_command (name : string) (arguments : string list)
      (input : string list) : string list =
    let pcs = async_command name arguments in
    output_lines input pcs.stdin;
    let out = input_lines pcs.stdout in
    let status = Unix.close_process_full pcs in
    match status with
    | Ok _ -> out
    | Error (`Exit_non_zero _) -> raise (Shell_error (unlines out))
    | Error (`Signal x) ->
      if Signal.equal x Signal.int then raise Sys.Break else out
end

module Timer = struct
  (** {6 Timer} *)

  let timers = ref []

  let make () =
    let st = Unix.times () in
    (fun () ->
       let en = Unix.times () in
       (en.Unix.tms_utime -. st.Unix.tms_utime) +.
       (en.Unix.tms_cutime -. st.Unix.tms_cutime))

  let start () = timers := make () :: !timers

  let stop () =
    match !timers with
    | [] -> assert false
    | tm :: tms -> timers := tms; tm ()

  exception Timeout

  let sigalrm_catched = ref false
  let disable_timeout f arg =
    sigalrm_catched := false;
    let reset_sigalrm_handler =
      let old_handler =
        let sigalrm_delayed_handler =
          Caml.Sys.Signal_handle
            (fun _ -> (* Format.printf "Timeout!@,"; *) sigalrm_catched := true) in
        Caml.Sys.signal Caml.Sys.sigalrm sigalrm_delayed_handler in
      fun () -> Caml.Sys.set_signal Caml.Sys.sigalrm old_handler
    in
    try
      let ret = f arg in
      reset_sigalrm_handler ();
      if !sigalrm_catched then
        raise Timeout (* @todo may differ from the behavior of [old_handler] *)
      else ret
    with exc -> reset_sigalrm_handler (); raise exc

  (** Set timeout for a function.
      E.g. Set 1 second time out to [hoge ()]
      {[ enable_timeout 1 ident ident
          (fun () -> hoge ())
          (fun time ret -> Format.printf "Fast (time = %f)" time)
          (fun time ret -> Format.printf "Too slow (time = %f)" time)
      ]}
      Setting timeout to 0 ignore timeout.
      Please note some counterintuitive points:
      {ul
        {- If the function call is nested, the previous timeout is masked }
        {- [Unix.sleep] do not tick [Unix.times] }
        {- The signal is delayed if [hoge ()] do not allocate memory (True?) }
      } *)
  let already_set = ref false
  (* if enable_timer is invoked from the call to main, it is just ignored *)

  let enable_timeout timeout before after main normal_handler exc_handler =
    (* Reset to restart the previous counter *)
    hook true before after
      (fun () ->
         if !already_set then main ()
         else
           let finish =
             let old_handler =
               let sigalrm_handler =
                 Caml.Sys.Signal_handle
                   (fun _ -> (* Format.printf "Timeout!@,";  *)raise Timeout) in
               Caml.Sys.signal Caml.Sys.sigalrm sigalrm_handler in
             fun () ->
               ignore @@ Unix.alarm 0;
               already_set := false;
               Caml.Sys.set_signal Caml.Sys.sigalrm old_handler
           in
           start ();
           already_set := true;
           ignore @@ Unix.alarm timeout;
           (*print_endline (string_of_float timeout);*)
           match main () with
           | ret ->
             finish ();
             normal_handler (stop ()) ret
           | exception exc ->
             finish ();
             exc_handler (stop ()) exc)

  (** {6 Interval Timer} *)

  let start_time = ref (Unix.times ())(*dummy*)
  let start_interval () = start_time := Unix.times ()
  let stop_interval () =
    let en = Unix.times () in
    (en.Unix.tms_utime -. !start_time.Unix.tms_utime) +.
    (en.Unix.tms_cutime -. !start_time.Unix.tms_cutime)
end

module IncrArray = struct
  include Array

  let grow_to t dim =
    assert(Array.length t < dim);
    let new_arr = create ~len:dim t.(0) in
    blito ~src:t ~dst:new_arr ();
    new_arr

  let grow t i =
    let rec aux length =
      if length > i then length
      else aux @@ (length + 1) * 2
    in
    grow_to t (aux @@ length t)

  let auto_set t i e =
    let t' = if i < length t then t else grow t i in
    set t' i e; t'

end

module IncrBigArray2 = struct
  include Bigarray.Array2

  let auto_blit src dst =
    for i = 0 to dim1 src - 1 do
      let slice_dst = Bigarray.Array1.sub (slice_left dst i) 0 (dim2 src) in
      let slice_src = slice_left src i in
      Bigarray.Array1.blit slice_src slice_dst
    done

  let grow_to t dim_x dim_y =
    assert(dim1 t <= dim_x && dim2 t <= dim_y);
    let new_arr = create (kind t) (layout t) dim_x dim_y in
    auto_blit t @@ new_arr;
    new_arr

  let rec grow_aux length i=
    if length > i then length
    else grow_aux ((length + 1) * 2) i

  let grow_x_y t x y = grow_to t (grow_aux (dim1 t) x) (grow_aux (dim2 t) y)
  let grow_x t x = grow_to t (grow_aux (dim1 t) x) (dim2 t)
  let grow_y t y = grow_to t (dim1 t) (grow_aux (dim2 t) y)

  let auto_set t x y e =
    let t' =
      if x >= dim1 t && y >= dim2 t then grow_x_y t x y
      else if x >= dim1 t then grow_x t x
      else if y >= dim2 t then grow_y t y
      else t
    in set t' x y e; t'

end
