(* The empty qualifier domain: generates no qualifier, so a predicate's
   qualifiers are the extracted ones only. *)
open Common.Ext

let qualifiers_of _ _ _ _ = Set.Poly.empty
let str_of_domain = "Null"
