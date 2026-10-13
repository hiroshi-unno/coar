open Core
open Common.Ext

(** Term variables *)

type tvar = Tvar of string

let tvar_count = Atomic.make 0
let default_tvar_prefix = "#tvar"

(* This domain's replay of fresh names, set only inside
   [with_replayed_fresh_names]: the prefix of the names drawn there and the
   counter they are numbered by. *)
let replay_key : (string * int ref) option Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> None)

let mk_fresh_tvar ?(prefix = None) () =
  match (prefix, Stdlib.Domain.DLS.get replay_key) with
  | None, Some (rp, n) ->
      let id = !n in
      incr n;
      Tvar (rp ^ string_of_int id)
  | _ ->
      let id = Atomic.fetch_and_add tvar_count 1 in
      let prefix = match prefix with None -> default_tvar_prefix | Some n -> n in
      Tvar (prefix ^ string_of_int id)

(* Whether this domain is inside [with_replayed_fresh_names], where an
   unprefixed draw does not move [tvar_count]: a caller that tells "drew no
   fresh name" by comparing [tvar_count] before and after must also ask this. *)
let replaying_fresh_names () = Option.is_some (Stdlib.Domain.DLS.get replay_key)

(* [with_replayed_fresh_names ~scope f] is [f ()] with every unprefixed
   [mk_fresh_tvar] of this domain drawn as [scope] followed by a counter that
   starts at 0 at each call, instead of from the process-global counter; the
   global counter does not move, and draws with a prefix and draws of other
   domains are unaffected.
   Contract: inside one call the names drawn are pairwise distinct, and
   distinct from every name not spelled with [scope] as its prefix -- so they
   are fresh for anything [f] builds, PROVIDED that nothing outside the
   calls with this [scope] spells a name with that prefix; the caller draws
   [scope] fresh ([fresh_replay_scope]) to make that hold.  Two calls with one
   [scope] draw the SAME names in the same order: that is the point, so that
   two builds of one computation over inputs that differ only in a part they
   reach late name what they build alike.  A name of one call may therefore
   denote something else in another call; a caller may combine results of two
   calls into one formula only where that is sound for free variables meaning
   different things under one name (a validity question over a conjunction or
   disjunction of formulas each valid on its own is).  Calls do not nest: an
   inner call replaces the outer replay until it returns. *)
let with_replayed_fresh_names ~scope f =
  let saved = Stdlib.Domain.DLS.get replay_key in
  Stdlib.Domain.DLS.set replay_key (Some (scope, ref 0));
  Exn.protect ~f ~finally:(fun () -> Stdlib.Domain.DLS.set replay_key saved)

(* This domain's replay position: the scope of the enclosing
   [with_replayed_fresh_names] and the number of names its call has drawn so
   far, so that the next unprefixed draw is [scope] followed by that number;
   [None] outside a replay. *)
let replay_position () =
  match Stdlib.Domain.DLS.get replay_key with
  | Some (scope, n) -> Some (scope, !n)
  | None -> None

(* [skip_replayed_fresh_names k] moves this domain's replay on by [k] names,
   so that the next draws are those that would follow [k] unprefixed draws.
   For a memo that stands in for a computation whose draws were all replayed:
   with the replay moved on, every later draw gives the name it would have
   given had the computation been run.  Raises outside a replay. *)
let skip_replayed_fresh_names k =
  match Stdlib.Domain.DLS.get replay_key with
  | Some (_, n) -> n := !n + k
  | None -> invalid_arg "Ident.skip_replayed_fresh_names: no replay"

(* a prefix for [with_replayed_fresh_names] that no other name of this process
   spells: the default prefix's draw is unique, and the trailing [r] keeps it
   apart from [is_generated_tvar]'s names *)
let fresh_replay_scope () =
  sprintf "%s%dr" default_tvar_prefix (Atomic.fetch_and_add tvar_count 1)

(* [mk_fresh_tvar_avoiding ~prefix ~taken ()] is [mk_fresh_tvar ~prefix ()]
   drawn again for as long as [taken] holds of the result.
   Contract: the result satisfies [not (taken v)]; when the first draw is not
   taken it is returned, so on an input without a collision the name and the
   counter advance are exactly those of one [mk_fresh_tvar] call.
   Why it exists: a prefixed name is the prefix followed by a process-global
   counter, fresh against the names this process has drawn and NOT against
   the names an input spells -- a program variable [z1] and a drawn selector
   [z1] became one variable in a clause's environment, and the clause became
   vacuous.  [taken] is the scope the name is inserted into: the environment
   it is added to and, where a formula over that scope is renamed or extended,
   that formula's free variables. *)
let mk_fresh_tvar_avoiding ~prefix ~taken () =
  let rec draw () =
    let v = mk_fresh_tvar ~prefix:(Some prefix) () in
    if taken v then draw () else v
  in
  draw ()

let name_of_tvar (Tvar name) = name
let str_of_tvar x = (*if is_dontcare x then "_" else*) name_of_tvar x
let str_of_tvars = String.concat_map_set ~f:name_of_tvar
let str_of_tvar_list = String.concat_map_list ~f:str_of_tvar
let tvar_compare (Tvar var1) (Tvar var2) = String.compare var1 var2
let tvar_equal (Tvar var1) (Tvar var2) = String.equal var1 var2

(*val str_of_tenv: (tvar, 'b) t -> string*)
let str_of_tenv tenv =
  String.concat_map_list ~sep:", " tenv ~f:(fun (Tvar x, _) -> x)

let dontcare_prefix = "$"
let dontcare_count = Atomic.make 0
let mk_dontcare x = Tvar (dontcare_prefix ^ x)

let mk_fresh_dontcare x =
  let id = Atomic.fetch_and_add dontcare_count 1 in
  Tvar (dontcare_prefix ^ x ^ "@" ^ string_of_int id)

let is_dontcare (Tvar x) = String.is_prefix ~prefix:dontcare_prefix x

(* Is this a name this process mints for itself?  [mk_fresh_tvar] with no prefix
   writes the default prefix followed by a counter, so an input that happens to
   declare one of those is asking for a variable the tool will also invent, and
   the two become one name for two things -- a lambda binder renamed apart
   collided with a declared [#tvar2] and made the identity function compare
   equal to a constant one.  A reader cannot stop the collision on the
   generating side, because SMT-LIB's quoted symbols admit every spelling, so it
   has to recognise the intruder on the way in. *)
let is_generated_tvar (Tvar x) =
  String.is_prefix ~prefix:default_tvar_prefix x
  &&
  let rest =
    String.subo x ~pos:(String.length default_tvar_prefix)
  in
  (not (String.is_empty rest)) && String.for_all rest ~f:Char.is_digit

(* Keep the counter clear of a name the input already uses.  Nothing can be
   renamed here -- the declaration's name is how the rest of the file refers to
   it -- so the tool steps around it instead, which costs nothing on an input
   that does not use these spellings and is the whole fix on one that does.
   Declarations are read before the assertions that make the tool draw names,
   which is what makes stepping around them in this direction enough. *)
let avoid_tvar x =
  if is_generated_tvar x then
    let (Tvar name) = x in
    match
      int_of_string_opt
      @@ String.subo name ~pos:(String.length default_tvar_prefix)
    with
    | Some n ->
        let rec bump () =
          let cur = Atomic.get tvar_count in
          if cur > n then ()
          else if Atomic.compare_and_set tvar_count cur (n + 1) then ()
          else bump ()
        in
        bump ()
    | None -> ()
let divide_flag = "_"
let uninterp (Tvar pid) = Tvar ("U" ^ divide_flag ^ pid ^ divide_flag)
let wfpred (Tvar pid) = Tvar ("WF" ^ divide_flag ^ pid ^ divide_flag)
let fnpred (Tvar pid) = Tvar ("FN" ^ divide_flag ^ pid ^ divide_flag)

(* [is_related_tvar var key]: is [var] one of the pfwCSP predicate names the
   muCLP reduction derives from the muCLP predicate [key] — [U_key_]
   ([uninterp]), [WF_key_] ([wfpred]) or [FN_key_] ([fnpred])?  Exact
   membership, not a substring test for [_key_], which would also relate
   [U_a_b_] to [a] and [U_state_main_bb1_] to [main_bb1] — predicate names
   with underscores are the norm, so the over-match would be real.  The
   shapes are the ones [MuCLP.Reducer] builds. *)
let is_related_tvar (Tvar var) (Tvar key) =
  String.equal var ("U" ^ divide_flag ^ key ^ divide_flag)
  || String.equal var ("WF" ^ divide_flag ^ key ^ divide_flag)
  || String.equal var ("FN" ^ divide_flag ^ key ^ divide_flag)

let is_size_fun_var (Tvar var) = String.is_prefix ~prefix:"SizeOf_" var
let ne_split_char = '_'
let mk_ne_tvar (Tvar p) = Tvar (sprintf "NE%c%s" ne_split_char p)

let is_ne_tvar (Tvar p) =
  String.is_prefix p ~prefix:(sprintf "NE%c" ne_split_char)

let mk_nwf_tvar (Tvar p) (Tvar l) (Tvar r) = Tvar (sprintf "%s_{%s,%s}" p l r)

(*let is_nwf_tvar (Tvar p) =
  let reg = Str.regexp "_N{[0-9]+,[0-9]+}" in
  Str.string_match reg p 0*)

let mk_parity_tvar = mk_nwf_tvar

let src_tvar_of_ne (Tvar p) =
  assert (is_ne_tvar @@ Tvar p);
  (* strip the prefix rather than splitting on [ne_split_char]: predicate
     names routinely contain '_' *)
  Tvar (String.chop_prefix_exn p ~prefix:(sprintf "NE%c" ne_split_char))

let dummy_tvar_count = Atomic.make 0

let mk_fresh_dummy_tvar sort_name =
  let id = Atomic.fetch_and_add dummy_tvar_count 1 in
  Atomic.incr dummy_tvar_count;
  Tvar (sprintf "#dummy_%s_%d" sort_name id)

(** Sort variables *)

type svar = Svar of string

let svar_count = Atomic.make 0

let mk_fresh_svar () =
  let id = Atomic.fetch_and_add svar_count 1 in
  Svar ("#svar" ^ string_of_int id)

let name_of_svar (Svar name) = name
let svar_compare (Svar var1) (Svar var2) = String.compare var1 var2
let svar_equal (Svar var1) (Svar var2) = String.equal var1 var2

(** Effect variables *)

type evar = Evar of string

let evar_count = Atomic.make 0

let mk_fresh_evar () =
  let id = Atomic.fetch_and_add evar_count 1 in
  Evar ("#evar" ^ string_of_int id)

let name_of_evar (Evar name) = name
let evar_compare (Evar var1) (Evar var2) = String.compare var1 var2
let evar_equal (Evar var1) (Evar var2) = String.equal var1 var2

(** row variables *)

type rvar = Rvar of string

let rvar_count = Atomic.make 0

let mk_fresh_rvar () =
  let id = Atomic.fetch_and_add rvar_count 1 in
  Rvar ("#rvar" ^ string_of_int id)

let name_of_rvar (Rvar name) = name
let rvar_compare (Rvar var1) (Rvar var2) = String.compare var1 var2
let rvar_equal (Rvar var1) (Rvar var2) = String.equal var1 var2

(** Predicate variables *)

type pvar = Pvar of string

let pvar_count = Atomic.make 0
let default_pvar_prefix = "#pvar"

let mk_fresh_pvar ?(prefix = None) () =
  let id = Atomic.fetch_and_add pvar_count 1 in
  let prefix = match prefix with None -> default_pvar_prefix | Some n -> n in
  Pvar (prefix ^ string_of_int id)

let name_of_pvar (Pvar name) = name
let pvar_compare (Pvar var1) (Pvar var2) = String.compare var1 var2
let pvar_equal (Pvar var1) (Pvar var2) = String.equal var1 var2
let uninterp_pvar (Pvar pid) = Pvar ("U" ^ divide_flag ^ pid ^ divide_flag)
let wfpred_pvar (Pvar pid) = Pvar ("WF" ^ divide_flag ^ pid ^ divide_flag)
let fnpred_pvar (Pvar pid) = Pvar ("FN" ^ divide_flag ^ pid ^ divide_flag)
let pvar_to_tvar = function Pvar ident -> Tvar ident
let tvar_to_pvar = function Tvar ident -> Pvar ident
let str_of_pvar = name_of_pvar
let str_of_pvars ~sep pvs = String.concat_map_set ~sep ~f:name_of_pvar pvs

(*val str_of_penv: (pvar, 'b) t -> string*)
let str_of_penv tenv =
  String.concat_map_list ~sep:", " tenv ~f:(fun (Pvar x, _) -> x)

(** Template-based constraint solving *)

let parameter_prefix = "#paramvar"
let parameter_cout = Atomic.make 0

let mk_fresh_parameter () =
  let id = Atomic.fetch_and_add parameter_cout 1 in
  Tvar (parameter_prefix ^ string_of_int id)

let is_parameter (Tvar x) = String.is_prefix ~prefix:parameter_prefix x

(** Others *)

let head_arg_count = Atomic.make 0

let mk_fresh_head_arg () =
  let id = Atomic.fetch_and_add head_arg_count 1 in
  Tvar ("#head_arg" ^ string_of_int id)

type tvar_map = (tvar, tvar) Map.Poly.t
type pvar_map = (pvar, pvar) Map.Poly.t
type tvar_set = tvar Set.Poly.t
type pvar_set = pvar Set.Poly.t
type svar_set = svar Set.Poly.t
type evar_set = evar Set.Poly.t
type rvar_set = rvar Set.Poly.t

(* [fresh_stamp ()]: a number that every fresh-name draw of this process
   (any counter above, or this domain's replay) increases and nothing else
   changes.  Two equal stamps around a computation mean it drew no fresh
   name -- in this domain, and in no other domain meanwhile -- which is what
   a memo needs before it may stand in for that computation without changing
   the names later draws give. *)
let fresh_stamp () =
  Atomic.get tvar_count + Atomic.get dontcare_count
  + Atomic.get dummy_tvar_count + Atomic.get svar_count
  + Atomic.get evar_count + Atomic.get rvar_count + Atomic.get pvar_count
  + Atomic.get parameter_cout + Atomic.get head_arg_count
  +
  match Stdlib.Domain.DLS.get replay_key with
  | Some (_, n) -> !n
  | None -> 0
