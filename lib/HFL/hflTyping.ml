(* Simple-type inference for an HES by unification, as ReTHFL's
   [Raw_hflz.Typing] does it.

   Assumes: the HES as the reader builds it (parameters and lambdas
   untyped).  Guarantees, or raises [Error] naming the offence:
   - every parameter and lambda carries its simple type, none a variable
     (an unconstrained variable defaults to [Prop] in result position and to
     [int] elsewhere, the type of an unused integer argument; what an unused
     argument's type is cannot matter);
   - every equation body has type [Prop]: a body that is a lambda has its
     binders moved into the parameters, and a body of function type is
     eta-expanded;
   - the integer variables free in the main (first) equation become its
     leading parameters, recorded in [closure] (the main equation must then
     not be referenced, since its references would lack those arguments);
   - no recursive simple type, no integer in result position, no free
     variable outside the main equation.
   Equation names are global and may be used before their definition. *)

open Core
open HflSyntax

exception Error of string

let error fmt = ksprintf (fun s -> raise (Error s)) fmt

type ty = P | I | Arr of ty * ty | TV of tv ref
and tv = Unbound of int | Link of ty

let cnt = ref 0

let fresh () =
  incr cnt;
  TV (ref (Unbound !cnt))

let rec repr = function
  | TV ({ contents = Link t } as r) ->
      let t' = repr t in
      r := Link t';
      t'
  | t -> t

let rec occurs r t =
  match repr t with
  | TV r' -> phys_equal r r'
  | Arr (a, b) -> occurs r a || occurs r b
  | P | I -> false

let rec str_of_ty t =
  match repr t with
  | P -> "prop"
  | I -> "int"
  | TV _ -> "'a"
  | Arr (a, b) -> sprintf "(%s -> %s)" (str_of_ty a) (str_of_ty b)

let rec unify ~where a b =
  match (repr a, repr b) with
  | P, P | I, I -> ()
  | TV r, TV r' when phys_equal r r' -> ()
  | TV r, t | t, TV r ->
      if occurs r t then error "%s: a recursive simple type" where;
      r := Link t
  | Arr (a1, b1), Arr (a2, b2) ->
      unify ~where a1 a2;
      unify ~where b1 b2
  | t1, t2 ->
      error "%s: type mismatch between %s and %s" where (str_of_ty t1)
        (str_of_ty t2)

let rec sty_of_ty t =
  match repr t with
  | P -> TProp
  | I | TV _ -> TInt
  | Arr (a, b) -> (
      (* an unconstrained result is a predicate's: default it to [Prop]
         rather than to [int], which no result may be *)
      (match repr b with TV r -> r := Link P | _ -> ());
      match sty_of_ty b with
      | TInt -> error "an integer in result position"
      | b' -> TArrow (sty_of_ty a, b'))

(* Before any type is read back: every unconstrained result of a function
   type is a predicate's, so it becomes [Prop].  Done over all the types of
   the system first, since one variable can be an argument type in one place
   and a result in another ([fun k -> k] passed where [bool -> bool] is
   expected). *)
let rec default_results t =
  match repr t with
  | Arr (a, b) ->
      default_results a;
      (match repr b with TV r -> r := Link P | _ -> ());
      default_results b
  | P | I | TV _ -> ()

let rec ty_of_sty = function
  | TProp -> P
  | TInt -> I
  | TArrow (a, b) -> Arr (ty_of_sty a, ty_of_sty b)

(* The inferred types of the binders, keyed by physical position: a lambda's
   annotation is written back by a second traversal in the same order. *)
let infer_term ~where env t =
  let abs_tys = ref [] in
  let rec go env t =
    match t with
    | Var x -> (
        match Map.find env x with
        | Some ty -> ty
        | None -> error "%s: unbound variable %s" where x)
    | Int _ -> I
    | Bool _ -> P
    | Op (_, a, b) ->
        unify ~where (go env a) I;
        unify ~where (go env b) I;
        I
    | Neg a ->
        unify ~where (go env a) I;
        I
    | Pred (_, a, b) ->
        unify ~where (go env a) I;
        unify ~where (go env b) I;
        P
    | And (a, b) | Or (a, b) ->
        unify ~where (go env a) P;
        unify ~where (go env b) P;
        P
    | Forall (x, a) | Exists (x, a) ->
        unify ~where (go (Map.set env ~key:x ~data:I) a) P;
        P
    | Abs (x, ann, a) ->
        let tx =
          match ann with Some s -> ty_of_sty s | None -> fresh ()
        in
        abs_tys := tx :: !abs_tys;
        let tb = go (Map.set env ~key:x ~data:tx) a in
        (match repr tb with I -> error "%s: a lambda returning an integer" where | _ -> ());
        Arr (tx, tb)
    | App (f, a) ->
        let tf = go env f in
        let ta = go env a in
        let tr = fresh () in
        unify ~where tf (Arr (ta, tr));
        tr
  in
  let ty = go env t in
  (ty, List.rev !abs_tys)

let rec annotate tys t =
  match t with
  | Var _ | Int _ | Bool _ -> t
  | Neg a -> Neg (annotate tys a)
  | Forall (x, a) -> Forall (x, annotate tys a)
  | Exists (x, a) -> Exists (x, annotate tys a)
  (* left to right, the order [infer_term] met the lambdas in *)
  | Op (o, a, b) ->
      let a = annotate tys a in
      Op (o, a, annotate tys b)
  | Pred (p, a, b) ->
      let a = annotate tys a in
      Pred (p, a, annotate tys b)
  | And (a, b) ->
      let a = annotate tys a in
      And (a, annotate tys b)
  | Or (a, b) ->
      let a = annotate tys a in
      Or (a, annotate tys b)
  | App (a, b) ->
      let a = annotate tys a in
      App (a, annotate tys b)
  | Abs (x, _, a) -> (
      match !tys with
      | ty :: rest ->
          tys := rest;
          let s = sty_of_ty ty in
          Abs (x, Some s, annotate tys a)
      | [] -> assert false)

(* Leading lambdas of a body become parameters. *)
let rec split_lambdas params = function
  | Abs (x, ann, b) -> split_lambdas (params @ [ (x, ann) ]) b
  | b -> (params, b)

let infer (hes : hes) : hes =
  cnt := 0;
  let eqns =
    List.map hes.eqns ~f:(fun e ->
        let params, body = split_lambdas e.params e.body in
        { e with params; body })
  in
  (match
     List.find_a_dup eqns ~compare:(fun a b -> String.compare a.name b.name)
   with
  | Some e -> error "equation %s is defined twice" e.name
  | None -> ());
  let names = String.Set.of_list (List.map eqns ~f:(fun e -> e.name)) in
  (* the universal closure of the main formula *)
  let eqns, closure =
    match eqns with
    | [] -> error "an HES with no equation"
    | main :: rest ->
        let bound =
          Set.union names
            (String.Set.of_list (List.map main.params ~f:fst))
        in
        let fvs =
          List.fold (free_vars bound main.body) ~init:[] ~f:(fun acc x ->
              if List.mem acc x ~equal:String.equal then acc else acc @ [ x ])
        in
        let closure = hes.closure @ fvs in
        if
          (not (List.is_empty fvs))
          && List.exists rest ~f:(fun e ->
              List.mem
                (free_vars String.Set.empty e.body)
                main.name ~equal:String.equal)
        then
          error
            "the main equation %s has free variables (%s) and is referenced"
            main.name
            (String.concat ~sep:", " fvs);
        ( { main with params = List.map fvs ~f:(fun x -> (x, Some TInt)) @ main.params }
          :: rest,
          closure )
  in
  let eqn_tys =
    List.map eqns ~f:(fun e ->
        let ptys =
          List.map e.params ~f:(fun (_, ann) ->
              match ann with Some s -> ty_of_sty s | None -> fresh ())
        in
        (e, ptys, fresh ()))
  in
  let genv =
    List.fold eqn_tys ~init:String.Map.empty ~f:(fun env (e, ptys, rt) ->
        Map.set env ~key:e.name
          ~data:(List.fold_right ptys ~init:rt ~f:(fun a b -> Arr (a, b))))
  in
  let results =
    List.map eqn_tys ~f:(fun (e, ptys, rt) ->
        let where = "equation " ^ e.name in
        let env =
          List.fold2_exn e.params ptys ~init:genv ~f:(fun env (x, _) ty ->
              Map.set env ~key:x ~data:ty)
        in
        let ty, abs_tys = infer_term ~where env e.body in
        unify ~where ty rt;
        (e, ptys, rt, abs_tys))
  in
  List.iter results ~f:(fun (_, ptys, rt, abs_tys) ->
      List.iter ((rt :: ptys) @ abs_tys) ~f:default_results);
  Map.iter genv ~f:default_results;
  let eqns =
    List.map results ~f:(fun (e, ptys, rt, abs_tys) ->
        let tys = ref abs_tys in
        let body = annotate tys e.body in
        let params =
          List.map2_exn e.params ptys ~f:(fun (x, _) ty -> (x, Some (sty_of_ty ty)))
        in
        (* eta-expansion of a body of function type *)
        let extra = args_of_sty (sty_of_ty rt) in
        let extra_params =
          List.mapi extra ~f:(fun i ty -> (sprintf "eta_%s_%d" e.name i, Some ty))
        in
        let body =
          apps body (List.map extra_params ~f:(fun (x, _) -> Var x))
        in
        { e with params = params @ extra_params; body })
  in
  List.iter results ~f:(fun (e, _, _, _) ->
      if not (Char.is_uppercase e.name.[0]) then
        error "equation %s: an equation name starts with an upper-case letter"
          e.name);
  (match eqns with
  | main :: _ ->
      List.iter closure ~f:(fun x ->
          match List.Assoc.find main.params x ~equal:String.equal with
          | Some (Some TInt) -> ()
          | _ ->
              error "the free variable %s of the main formula is not an integer"
                x)
  | [] -> ());
  { hes with eqns; closure }

(** the simple types of the equation names and of every parameter of [e]:
    the environment a consumer needs to tell an integer variable from a
    predicate *)
let env_of_eqn (hes : hes) (e : eqn) =
  let genv =
    List.fold hes.eqns ~init:String.Map.empty ~f:(fun env e ->
        Map.set env ~key:e.name ~data:(sty_of_eqn e))
  in
  List.fold e.params ~init:genv ~f:(fun env (x, ty) ->
      Map.set env ~key:x ~data:(Option.value ty ~default:TInt))
