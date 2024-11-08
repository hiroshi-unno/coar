open Core
open Common.Ext

(** Term variables *)

type tvar = Tvar of string

let tvar_count = Atomic.make 0
let default_tvar_prefix = "#tvar"

let mk_fresh_tvar ?(prefix = None) () =
  let id = Atomic.fetch_and_add tvar_count 1 in
  let prefix = match prefix with None -> default_tvar_prefix | Some n -> n in
  Tvar (prefix ^ string_of_int id)

let name_of_tvar (Tvar name) = name
let str_of_tvar x = (*if is_dontcare x then "_" else*) name_of_tvar x
let str_of_tvars ~sep tvs = String.concat_map_set ~sep ~f:name_of_tvar tvs
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
let divide_flag = "_"
let uninterp (Tvar pid) = Tvar ("U" ^ divide_flag ^ pid ^ divide_flag)
let wfpred (Tvar pid) = Tvar ("WF" ^ divide_flag ^ pid ^ divide_flag)
let fnpred (Tvar pid) = Tvar ("FN" ^ divide_flag ^ pid ^ divide_flag)

let is_related_tvar (Tvar var) (Tvar key) =
  String.is_substring var ~substring:(divide_flag ^ key ^ divide_flag)

let is_size_fun_var (Tvar var) = String.is_prefix ~prefix:"SizeOf_" var
let ne_split_char = '_'
let mk_ne_tvar (Tvar p) = Tvar (sprintf "NE%c%s" ne_split_char p)

let is_ne_tvar (Tvar p) =
  String.is_prefix p ~prefix:(sprintf "NE%c" ne_split_char)

let mk_nwf_tvar (Tvar p) (Tvar l) (Tvar r) = Tvar (sprintf "%s_{%s,%s}" p l r)

let is_nwf_tvar (Tvar p) =
  let reg = Str.regexp "_N{[0-9]+,[0-9]+}" in
  Str.string_match reg p 0

let src_tvar_of_ne (Tvar p) =
  assert (is_ne_tvar @@ Tvar p);
  Tvar (List.nth_exn (String.split ~on:ne_split_char p) 1)

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
