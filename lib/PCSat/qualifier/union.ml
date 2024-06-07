open Core
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

module type Q = sig
  val qualifiers_of :
    Ident.pvar ->
    Sort.t list ->
    (ExAtom.t * int) Set.Poly.t ->
    sort_env_map * VersionSpace.examples ->
    (sort_env_list * Formula.t) Set.Poly.t

  val str_of_domain : string
end

module Make (Config : sig
  val domains : (module Q) list
end) =
struct
  let qualifiers_of pvar sorts labeled_atoms examples =
    let params = LogicOld.sort_env_list_of_sorts sorts in
    Set.Poly.union_list
    @@ List.map Config.domains ~f:(fun (module Q) ->
           Set.Poly.map ~f:(fun (params', phi) ->
               ( params,
                 let map =
                   Map.Poly.of_alist_exn
                   @@ List.map2_exn params' params ~f:(fun (x, _) (y, s) ->
                          (x, Term.mk_var y s))
                 in
                 Formula.subst map phi ))
           @@ Q.qualifiers_of pvar sorts labeled_atoms examples)

  let str_of_domain =
    "Union of ["
    ^ (String.concat ~sep:","
      @@ List.map Config.domains ~f:(fun (module Q) -> Q.str_of_domain))
    ^ "]"
end
