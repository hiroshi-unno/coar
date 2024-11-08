open Core
open Common.Ext

type info = Dummy

module Formula : sig
  type unop = Neg
  type binop = And | Or

  type t =
    | True of info
    | False of info
    | Atom of string * info
    | UnaryOp of unop * t * info
    | BinaryOp of binop * t * t * info

  val mk_true : ?info:info -> unit -> t
  val mk_false : ?info:info -> unit -> t
  val mk_atom : ?info:info -> string -> t
  val mk_neg : ?info:info -> t -> t
  val mk_and : ?info:info -> t -> t -> t
  val mk_or : ?info:info -> t -> t -> t
  val and_of : ?info:info -> t list -> t
  val or_of : ?info:info -> t list -> t
  val str_of : t -> string
  val let_atom : t -> string * info
  val name_of_atom : t -> string
  val bool_of_exn : t -> bool
  val size : t -> int
  val height : t -> int
  val occurs_in : t -> t -> bool
  val neg_atoms_of_clause : t -> t list
  val pos_atoms_of_clause : t -> t list
  val eval : t -> bool
  val subst : (string, bool) Map.Poly.t -> t -> t
  val cnf_of : t -> (string list * string list) list
  val nnf_of : t -> t
  val tseitinize : t -> (string Set.Poly.t * string Set.Poly.t) Set.Poly.t
end = struct
  type unop = Neg
  type binop = And | Or

  type t =
    | True of info
    | False of info
    | Atom of string * info
    | UnaryOp of unop * t * info
    | BinaryOp of binop * t * t * info

  let mk_true ?(info = Dummy) () = True info
  let mk_false ?(info = Dummy) () = False info
  let mk_atom ?(info = Dummy) ident = Atom (ident, info)
  let mk_neg ?(info = Dummy) t = UnaryOp (Neg, t, info)
  let mk_and ?(info = Dummy) t1 t2 = BinaryOp (And, t1, t2, info)
  let mk_or ?(info = Dummy) t1 t2 = BinaryOp (Or, t1, t2, info)

  let and_of ?(info = Dummy) =
    List.fold ~init:(mk_true ~info ()) ~f:(mk_and ~info)

  let or_of ?(info = Dummy) =
    List.fold ~init:(mk_false ~info ()) ~f:(mk_or ~info)

  let rec str_of = function
    | True _ -> "True"
    | False _ -> "False"
    | Atom (id, _) -> id
    | UnaryOp (_, t, _) -> sprintf "not (%s)" (str_of t)
    | BinaryOp (And, t1, t2, _) ->
        String.paren @@ sprintf "%s /\\ %s" (str_of t1) (str_of t2)
    | BinaryOp (Or, t1, t2, _) ->
        String.paren @@ sprintf "%s \\/ %s" (str_of t1) (str_of t2)

  let let_atom = function
    | Atom (name, info) -> (name, info)
    | phi -> failwith @@ sprintf "%s is not an atom" (str_of phi)

  let name_of_atom phi = fst @@ let_atom phi

  let bool_of_exn = function
    | True _ -> true
    | False _ -> false
    | _ -> failwith "cannot convert into bool."

  let rec size = function
    | True _ | False _ | Atom _ -> 1
    | UnaryOp (_, phi, _) -> 1 + size phi
    | BinaryOp (_, phi1, phi2, _) -> 1 + size phi1 + size phi2

  let rec height = function
    | True _ | False _ | Atom _ -> 1
    | UnaryOp (_, phi, _) -> 1 + height phi
    | BinaryOp (_, phi1, phi2, _) -> 1 + max (height phi1) (height phi2)

  let rec occurs_in phi1 phi2 =
    if Stdlib.(phi1 = phi2) then true
    else
      match phi2 with
      | True _ | False _ | Atom (_, _) -> false
      | UnaryOp (_, phi21, _) -> occurs_in phi1 phi21
      | BinaryOp (_, phi21, phi22, _) ->
          occurs_in phi1 phi21 || occurs_in phi1 phi22

  let rec neg_atoms_of_clause = function
    | UnaryOp (Neg, Atom (id, Dummy), _) -> [ Atom (id, Dummy) ]
    | Atom (_, _) | True _ | False _ -> []
    | BinaryOp (Or, phi1, phi2, _) ->
        neg_atoms_of_clause phi1 @ neg_atoms_of_clause phi2
    | phi -> failwith @@ sprintf "The formula %s is not of clause" (str_of phi)

  let rec pos_atoms_of_clause = function
    | UnaryOp (Neg, Atom (_, _), _) | True _ | False _ -> []
    | Atom (id, Dummy) -> [ Atom (id, Dummy) ]
    | BinaryOp (Or, phi1, phi2, _) ->
        pos_atoms_of_clause phi1 @ pos_atoms_of_clause phi2
    | _ -> failwith "This formula is not of clause"

  let eval formula =
    let rec inner = function
      | True _ -> Set.Poly.singleton true
      | False _ -> Set.Poly.singleton false
      | Atom _ -> Set.Poly.of_list [ true; false ]
      | UnaryOp (Neg, phi, _) -> Set.Poly.map (inner phi) ~f:not
      | BinaryOp (And, phi1, phi2, _) ->
          Set.concat_map (inner phi1) ~f:(fun tf ->
              Set.Poly.map (inner phi2) ~f:(( && ) tf))
      | BinaryOp (Or, phi1, phi2, _) ->
          Set.concat_map (inner phi1) ~f:(fun tf ->
              Set.Poly.map (inner phi2) ~f:(( || ) tf))
    in
    if Set.for_all (inner formula) ~f:(Stdlib.( = ) true) then true
    else if Set.for_all (inner formula) ~f:(Stdlib.( = ) false) then false
    else failwith @@ sprintf "formula %s cannot be evaluated" @@ str_of formula

  let rec subst map = function
    | True info -> True info
    | False info -> False info
    | Atom (name, info) -> (
        match Map.Poly.find map name with
        | None -> Atom (name, info)
        | Some true -> True info
        | Some false -> False info)
    | UnaryOp (op, phi, info) -> UnaryOp (op, subst map phi, info)
    | BinaryOp (op, phi1, phi2, info) ->
        BinaryOp (op, subst map phi1, subst map phi2, info)

  let rec cnf_of = function
    | True _ | UnaryOp (Neg, False _, _) -> []
    | False _ | UnaryOp (Neg, True _, _) -> [ ([], []) ]
    | Atom (name, _) -> [ ([], [ name ]) ]
    | UnaryOp (Neg, Atom (name, _), _) -> [ ([ name ], []) ]
    | UnaryOp (Neg, UnaryOp (Neg, phi, _), _) -> cnf_of phi
    | BinaryOp (And, phi1, phi2, _) -> cnf_of phi1 @ cnf_of phi2
    | BinaryOp (Or, phi1, phi2, _) ->
        List.cartesian_product (cnf_of phi1) (cnf_of phi2)
        |> List.map ~f:(fun ((ns1, ps1), (ns2, ps2)) -> (ns1 @ ns2, ps1 @ ps2))
    | phi -> failwith @@ sprintf "fail @ cnf_of %s " @@ str_of phi

  let rec nnf_of = function
    | UnaryOp (Neg, True Dummy, _) -> False Dummy
    | UnaryOp (Neg, False Dummy, _) -> True Dummy
    | UnaryOp (Neg, UnaryOp (Neg, phi, _), _) -> nnf_of phi
    | UnaryOp (Neg, BinaryOp (And, phi1, phi2, _), _) ->
        BinaryOp
          ( Or,
            nnf_of (UnaryOp (Neg, phi1, Dummy)),
            nnf_of (UnaryOp (Neg, phi2, Dummy)),
            Dummy )
    | UnaryOp (Neg, BinaryOp (Or, phi1, phi2, _), _) ->
        BinaryOp
          ( And,
            nnf_of (UnaryOp (Neg, phi1, Dummy)),
            nnf_of (UnaryOp (Neg, phi2, Dummy)),
            Dummy )
    | BinaryOp (And, phi1, phi2, _) ->
        BinaryOp (And, nnf_of phi1, nnf_of phi2, Dummy)
    | BinaryOp (Or, phi1, phi2, _) ->
        BinaryOp (Or, nnf_of phi1, nnf_of phi2, Dummy)
    | phi -> phi

  let strue cnf_or_dnf =
    if cnf_or_dnf then Set.Poly.empty
    else Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty)

  let sfalse cnf_or_dnf =
    if cnf_or_dnf then Set.Poly.singleton (Set.Poly.empty, Set.Poly.empty)
    else Set.Poly.empty

  let satom name = Set.Poly.singleton (Set.Poly.empty, Set.Poly.singleton name)

  let snegatom name =
    Set.Poly.singleton (Set.Poly.singleton name, Set.Poly.empty)

  let sand_cnf = Set.Poly.union_list
  let sor_dnf = Set.Poly.union_list

  let rec tseitinize cnf_or_dnf = function
    | True _ | UnaryOp (Neg, False _, _) -> (strue cnf_or_dnf, strue true)
    | False _ | UnaryOp (Neg, True _, _) -> (sfalse cnf_or_dnf, strue true)
    | Atom (name, _) -> (satom name, strue true)
    | UnaryOp (Neg, Atom (name, _), _) -> (snegatom name, strue true)
    | UnaryOp (Neg, UnaryOp (Neg, formula', _), _) ->
        tseitinize cnf_or_dnf formula'
    | UnaryOp (Neg, BinaryOp (Or, formula_0, formula_1, _), _) ->
        tseitinize cnf_or_dnf @@ mk_and (mk_neg formula_0) (mk_neg formula_1)
    | UnaryOp (Neg, BinaryOp (And, formula_0, formula_1, _), _) ->
        tseitinize cnf_or_dnf @@ mk_or (mk_neg formula_0) (mk_neg formula_1)
    | BinaryOp (And, formula_0, formula_1, _) ->
        let s0, c0 = tseitinize true formula_0 in
        let s1, c1 = tseitinize true formula_1 in
        if Set.equal s0 (sfalse true) || Set.equal s1 (sfalse true) then
          (sfalse true, strue true)
        else
          let s = sand_cnf [ s0; s1 ] in
          let c = sand_cnf [ c0; c1 ] in
          if cnf_or_dnf then (s, c)
          else
            let names, cc =
              Set.unzip
              @@ Set.Poly.map s ~f:(fun (n, p) ->
                     if Set.length n = 1 && Set.is_empty p then
                       (Second (Set.choose_exn n), strue true)
                     else if Set.length p = 1 && Set.is_empty n then
                       (First (Set.choose_exn p), strue true)
                     else
                       let name =
                         Ident.mk_fresh_pvar () |> function
                         | Ident.Pvar name -> name
                       in
                       ( First name,
                         Set.add
                           (Set.union
                              (Set.Poly.map n ~f:(fun atm ->
                                   ( Set.Poly.empty,
                                     Set.Poly.of_list [ name; atm ] )))
                              (Set.Poly.map p ~f:(fun atm ->
                                   ( Set.Poly.singleton atm,
                                     Set.Poly.singleton name ))))
                           (Set.add n name, p) ))
            in
            let ps, ns = Set.partition_map names ~f:Fn.id in
            (Set.Poly.singleton (ns, ps), Set.union c (Set.concat cc))
    | BinaryOp (Or, formula_0, formula_1, _) ->
        let s0, c0 = tseitinize false formula_0 in
        let s1, c1 = tseitinize false formula_1 in
        if Set.equal s0 (strue false) || Set.equal s1 (strue false) then
          (strue false, strue true)
        else
          let s = sor_dnf [ s0; s1 ] in
          let c = sand_cnf [ c0; c1 ] in
          if cnf_or_dnf then
            let names, cc =
              Set.unzip
              @@ Set.Poly.map s ~f:(fun (n, p) ->
                     if Set.length n = 1 && Set.is_empty p then
                       (Second (Set.choose_exn n), strue true)
                     else if Set.length p = 1 && Set.is_empty n then
                       (First (Set.choose_exn p), strue true)
                     else
                       let name =
                         Ident.mk_fresh_pvar () |> function
                         | Ident.Pvar name -> name
                       in
                       ( First name,
                         Set.add
                           (Set.union
                              (Set.Poly.map n ~f:(fun atm ->
                                   ( Set.Poly.of_list [ name; atm ],
                                     Set.Poly.empty )))
                              (Set.Poly.map p ~f:(fun atm ->
                                   ( Set.Poly.singleton name,
                                     Set.Poly.singleton atm ))))
                           (p, Set.add n name) ))
            in
            let ps, ns = Set.partition_map names ~f:Fn.id in
            (Set.Poly.singleton (ns, ps), Set.union c (Set.concat cc))
          else (s, c)

  let tseitinize phi =
    let s, c = tseitinize true phi in
    sand_cnf [ s; c ]
end

let str_of_model =
  String.concat_map_list ~sep:", " ~f:(function
    | phi, None -> sprintf "%s -> *" (Formula.str_of phi)
    | phi, Some value ->
        sprintf "%s -> %s" (Formula.str_of phi) (Formula.str_of value))
