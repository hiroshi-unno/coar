open Core

type tvar = Tvar of string (* term variable *)
type pvar = Pvar of string (* predicate variable *)
type svar = Svar of string (* sort variable *)

let tvar_count = ref 0
let mk_fresh_tvar ?(prefix = None) () =
  incr tvar_count;
  let prefix =
    match prefix with
    | None -> "#tvar"
    | Some n -> n
  in
  Tvar (prefix ^ string_of_int !tvar_count)

let dummy_tvar_count = ref 0
let mk_fresh_dummy_tvar sort_name =
  incr dummy_tvar_count;
  Tvar (sprintf "#dummy_%s_%d" sort_name !dummy_tvar_count)

let svar_count = ref 0
let mk_fresh_svar () =
  incr svar_count;
  Svar ("#svar" ^ string_of_int !svar_count)

let pvar_count = ref 0
let mk_fresh_pvar () =
  incr pvar_count;
  Pvar ("#pvar" ^ string_of_int !pvar_count)

let parameter_prefix = "#paramvar"
let parameter_cout = ref 0
let mk_fresh_parameter () =
  incr parameter_cout;
  Tvar (parameter_prefix ^ string_of_int !parameter_cout)
let is_parameter (Tvar x) = String.is_prefix ~prefix:parameter_prefix x

let head_arg_count = ref 0
let mk_fresh_head_arg () =
  incr head_arg_count;
  Tvar ("#head_arg" ^ string_of_int !head_arg_count)

let dontcare_prefix = "$"
let dontcare_count = ref 0
let mk_dontcare x = Tvar (dontcare_prefix ^ x)
let mk_fresh_dontcare x =
  incr dontcare_count;
  Tvar (dontcare_prefix ^ x ^ "@" ^ string_of_int !dontcare_count)
let is_dontcare (Tvar x) = String.is_prefix ~prefix:dontcare_prefix x

let name_of_tvar = function Tvar name -> name
let name_of_pvar = function Pvar name -> name
let name_of_svar = function Svar name -> name
let str_of_tvar x = (*if is_dontcare x then "_" else*) name_of_tvar x

let tvar_compare (Tvar var1) (Tvar var2) =
  String.compare var1 var2

let pvar_compare (Pvar var1) (Pvar var2) =
  String.compare var1 var2
