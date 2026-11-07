(* Fair enumerations of a stated hypothesis space, for the mode of MuStrat in
   which every member of that space is eventually offered to the strategy
   check ([relative_completeness]).

   Why: the refinement proposes only terms and rankings fitted to the plays it
   has seen, and on a game whose winning Skolem function lies outside every
   such fit (for [forall x. exists y. 2y <= x <= 2y + 1] the function is
   [x div 2], and every refinement fitted one more constant) the loop never
   wins a check.  Offering the members of a fixed countable space one by one,
   in finite layers, makes the loop answer whenever a winning strategy lies in
   that space, whatever the refinement does: a check is monotone in its term
   sets (more alternatives are more choices for the checked side), so once
   the offered terms contain the winning ones, the check of the winning
   rankings with the current term sets is won.  That is the same argument by
   which a template-based synthesiser that grows its template layer by layer
   eventually reaches every template instance.

   The space.
   - Terms ([Ints], [Reals]): for integer parameters, the closure of the
     parameters and integer literals under [+], multiplication by a literal and
     division by a literal [d >= 2] ([div] with a positive divisor is the
     floor, in SMT-LIB's Euclidean reading); modulo is derived
     ([t mod d = t - d * (t div d)]).  Layer [l] holds the terms whose syntax
     tree has at most [l] nodes with every literal in [[-l, l]] and no
     operator applied to a subterm without a parameter (such a subterm is a
     literal, in the layer of its magnitude; so the constants of layer [l]
     are exactly [[-l, l]]).  For real
     parameters, the affine terms with at most [l] nonzero coefficients, each
     coefficient and the constant a fraction [p/q] with [|p| <= l],
     [1 <= q <= l].  Each layer is finite, layers increase, and every term
     of the space is in some layer.  Layer [l]'s list extends layer [l - 1]'s
     list as a prefix, which is what lets an index stand for a term across
     layers.
   - Rankings ([Rankings]): for a ranking key over an earlier and a later
     state, the relation [W_r(c, y)] of a tuple [r = (r_1, .., r_k)] of
     component functions of the state:
       OR_j ( AND_{i<j} r_i(c) = r_i(y)  /\  r_j(c) - r_j(y) >= 1  /\  r_j(c) >= 0 ).
     Every such relation is well-founded and transitive whatever the
     components are, so a check won with it is an answer as a check won with
     a ranking proved transitive is.  A component is a decision list
     [if g_1 >= 0 then t_1 else .. else t_p] of terms of the layer, with
     [k <= l] components and [p <= l] pieces in layer [l].
   - Tuples ([Tuples]): one term per key of a side, offered as one vector, so
     that under joint term alternatives every combination of offered terms is
     eventually a row; layer [l] holds the tuples whose components all lie in
     layer [l].

   Enumeration.  Each layer is walked in shells (all component indices at
   most [b], some equal to [b], for [b = 0, 1, ..]), skipping the items of
   the layer before; so every item of every layer is reached after finitely
   many steps, and small indices (small terms) come first.  Nothing here asks
   a solver: the module is pure apart from its cursors' state. *)

open Core
open Ast
open Ast.LogicOld

(* ------------------------------------------------------------------ *)
(* Integer terms, in a linear normal form over atoms                     *)
(* ------------------------------------------------------------------ *)

module Ints = struct
  (* A term is [const + sum_i k_i * a_i] over pairwise distinct atoms, sorted,
     every [k_i] nonzero; an atom is a parameter (by position) or
     [floor (s / d)] with [d >= 2] and [s] not a constant.  Two terms with the
     same normal form denote the same function; the converse need not hold
     ([floor (2x / 2)] and [x] are kept apart), which only means a function
     may be offered twice. *)
  type atom = Var of int | Floor of t * Z.t
  and t = { const : Z.t; lin : (atom * Z.t) list }

  let rec compare_atom a b =
    match (a, b) with
    | Var i, Var j -> Int.compare i j
    | Var _, Floor _ -> -1
    | Floor _, Var _ -> 1
    | Floor (s, d), Floor (s', d') ->
        let c = compare s s' in
        if c <> 0 then c else Z.compare d d'

  and compare a b =
    let c = Z.compare a.const b.const in
    if c <> 0 then c
    else
      List.compare
        (fun (x, k) (y, k') ->
          let c = compare_atom x y in
          if c <> 0 then c else Z.compare k k')
        a.lin b.lin

  let const c = { const = c; lin = [] }
  let var i = { const = Z.zero; lin = [ (Var i, Z.one) ] }

  let add a b =
    let rec merge l1 l2 =
      match (l1, l2) with
      | [], l | l, [] -> l
      | (x, k) :: r1, (y, k') :: r2 ->
          let c = compare_atom x y in
          if c < 0 then (x, k) :: merge r1 l2
          else if c > 0 then (y, k') :: merge l1 r2
          else
            let s = Z.(k + k') in
            if Z.equal s Z.zero then merge r1 r2 else (x, s) :: merge r1 r2
    in
    { const = Z.(a.const + b.const); lin = merge a.lin b.lin }

  let scale k a =
    if Z.equal k Z.zero then const Z.zero
    else
      {
        const = Z.(k * a.const);
        lin = List.map a.lin ~f:(fun (x, c) -> (x, Z.(k * c)));
      }

  (* Pre: [d >= 1]. *)
  let floor a d =
    if Z.equal d Z.one then a
    else if List.is_empty a.lin then const (Z.fdiv a.const d)
    else { const = Z.zero; lin = [ (Floor (a, d), Z.one) ] }

  (* [eval env t]: the value of [t] with parameter [i] at [env.(i)]. *)
  let rec eval env t =
    List.fold t.lin ~init:t.const ~f:(fun acc (x, k) ->
        Z.(acc + (k * eval_atom env x)))

  and eval_atom env = function
    | Var i -> env.(i)
    | Floor (s, d) -> Z.fdiv (eval env s) d

  let rec to_string t =
    let atom = function
      | Var i -> sprintf "p%d" i
      | Floor (s, d) -> sprintf "(%s div %s)" (to_string s) (Z.to_string d)
    in
    let parts =
      List.map t.lin ~f:(fun (x, k) ->
          if Z.equal k Z.one then atom x
          else sprintf "%s*%s" (Z.to_string k) (atom x))
    in
    let parts =
      if Z.equal t.const Z.zero && not (List.is_empty parts) then parts
      else parts @ [ Z.to_string t.const ]
    in
    String.concat ~sep:" + " parts

  (* [to_term params t]: [t] over the integer variables [params] (parameter
     [i] is [params.(i)]). *)
  let rec to_term (params : Ident.tvar array) t =
    let atom = function
      | Var i -> Term.mk_var params.(i) T_int.SInt
      | Floor (s, d) ->
          T_int.mk_div Value.Euclidean (to_term params s) (T_int.mk_int d)
    in
    let mono (x, k) =
      if Z.equal k Z.one then atom x else T_int.mk_mul (T_int.mk_int k) (atom x)
    in
    match t.lin with
    | [] -> T_int.mk_int t.const
    | m :: ms ->
        let s = List.fold ms ~init:(mono m) ~f:(fun acc m -> T_int.mk_add acc (mono m)) in
        if Z.equal t.const Z.zero then s else T_int.mk_add s (T_int.mk_int t.const)

  (* The terms of tree size exactly [n] over [arity] parameters with literals
     in [[-l, l]], for [n = 1 .. l] (index [n - 1]). *)
  let by_size ~arity l =
    let lits = List.init ((2 * l) + 1) ~f:(fun i -> Z.of_int (i - l)) in
    let mults = List.filter lits ~f:(fun k -> not (Z.equal k Z.zero || Z.equal k Z.one)) in
    let divs = List.init (Int.max 0 (l - 1)) ~f:(fun i -> Z.of_int (i + 2)) in
    let s = Array.create ~len:(Int.max l 1) [] in
    if l >= 1 then
      s.(0) <- List.map lits ~f:const @ List.init arity ~f:var;
    for n = 2 to l do
      let prev = s.(n - 2) in
      (* an operator is never applied to a constant-only subterm: such a
         subterm is a literal, of the layer its value's magnitude gives *)
      let nonconst t = not (List.is_empty t.lin) in
      let unary =
        List.concat_map (List.filter prev ~f:nonconst) ~f:(fun t ->
            List.map mults ~f:(fun k -> scale k t)
            @ List.map divs ~f:(fun d -> floor t d))
      in
      let binary =
        List.concat_map (List.init (n - 2) ~f:(fun i -> i + 1)) ~f:(fun i ->
            List.concat_map s.(i - 1) ~f:(fun a ->
                List.filter_map s.(n - 1 - i - 1) ~f:(fun b ->
                    if nonconst a || nonconst b then Some (add a b) else None)))
      in
      s.(n - 1) <- unary @ binary
    done;
    if l = 0 then [] else Array.to_list s

  let layers : (int * int, t array) Hashtbl.t = Hashtbl.Poly.create ()

  (* [layer ~arity l]: layer [l] as an array that extends layer [l - 1]'s
     array as a prefix, each term once; layer 0 is empty. *)
  let rec layer ~arity l =
    match Hashtbl.find layers (arity, l) with
    | Some a -> a
    | None ->
        let a =
          if l <= 0 then [||]
          else
            let prev = layer ~arity (l - 1) in
            let seen = Hash_set.create (module String) in
            Array.iter prev ~f:(fun t -> Hash_set.add seen (to_string t));
            (* within a layer, the terms over a parameter first, each size
               before the next, then the new literals *)
            let fresh =
              (let sized = List.concat (by_size ~arity l) in
               List.filter sized ~f:(fun t -> not (List.is_empty t.lin))
               @ List.filter sized ~f:(fun t -> List.is_empty t.lin))
              |> List.filter ~f:(fun t ->
                     let k = to_string t in
                     if Hash_set.mem seen k then false
                     else (
                       Hash_set.add seen k;
                       true))
            in
            Array.append prev (Array.of_list fresh)
        in
        Hashtbl.set layers ~key:(arity, l) ~data:a;
        a
end

(* ------------------------------------------------------------------ *)
(* Real affine terms                                                    *)
(* ------------------------------------------------------------------ *)

module Reals = struct
  (* [const + sum coeffs.(i) * p_i]. *)
  type t = { const : Q.t; coeffs : Q.t array }

  let to_string t =
    String.concat ~sep:" + "
      (Array.to_list
         (Array.mapi t.coeffs ~f:(fun i q -> sprintf "%s*p%d" (Q.to_string q) i))
      @ [ Q.to_string t.const ])

  let eval env t =
    Array.foldi t.coeffs ~init:t.const ~f:(fun i acc q -> Q.(acc + (q * env.(i))))

  let to_term (params : Ident.tvar array) t =
    let monos =
      Array.to_list t.coeffs
      |> List.filter_mapi ~f:(fun i q ->
             if Q.equal q Q.zero then None
             else
               let v = Term.mk_var params.(i) T_real.SReal in
               Some
                 (if Q.equal q Q.one then v
                  else T_real.mk_rmul (T_real.mk_real q) v))
    in
    match monos with
    | [] -> T_real.mk_real t.const
    | m :: ms ->
        let s = List.fold ms ~init:m ~f:T_real.mk_radd in
        if Q.equal t.const Q.zero then s
        else T_real.mk_radd s (T_real.mk_real t.const)

  (* the fractions [p/q], [|p| <= l], [1 <= q <= l], each once, in order of
     [max(|p|, q)] and then first appearance *)
  let fractions l =
    let seen = Hash_set.create (module String) in
    List.concat_map (List.init (l + 1) ~f:Fn.id) ~f:(fun m ->
        List.concat_map (List.init (m + 1) ~f:Fn.id) ~f:(fun q ->
            List.concat_map [ m; -m ] ~f:(fun p ->
                List.filter_map [ (p, q); (q, m) ] ~f:(fun (p, q) ->
                    if q < 1 || Int.abs p > l || q > l then None
                    else
                      let x = Q.of_ints p q in
                      let k = Q.to_string x in
                      if Hash_set.mem seen k then None
                      else (
                        Hash_set.add seen k;
                        Some x)))))
    |> fun xs ->
    if Hash_set.mem seen "0" then xs
    else Q.zero :: xs

  let layers : (int * int, t array) Hashtbl.t = Hashtbl.Poly.create ()

  let rec layer ~arity l =
    match Hashtbl.find layers (arity, l) with
    | Some a -> a
    | None ->
        let a =
          if l <= 0 then [||]
          else
            let prev = layer ~arity (l - 1) in
            let seen = Hash_set.create (module String) in
            Array.iter prev ~f:(fun t -> Hash_set.add seen (to_string t));
            let fr = fractions l in
            let nonzero = List.filter fr ~f:(fun q -> not (Q.equal q Q.zero)) in
            (* coefficient vectors with at most [l] nonzero entries *)
            let rec vectors i nz =
              if i = arity then [ [] ]
              else
                let rest_zero =
                  List.map (vectors (i + 1) nz) ~f:(fun v -> Q.zero :: v)
                in
                if nz >= l then rest_zero
                else
                  rest_zero
                  @ List.concat_map nonzero ~f:(fun q ->
                        List.map (vectors (i + 1) (nz + 1)) ~f:(fun v -> q :: v))
            in
            let fresh =
              List.concat_map (vectors 0 0) ~f:(fun v ->
                  List.map fr ~f:(fun c -> { const = c; coeffs = Array.of_list v }))
              |> List.filter ~f:(fun t ->
                     let k = to_string t in
                     if Hash_set.mem seen k then false
                     else (
                       Hash_set.add seen k;
                       true))
            in
            Array.append prev (Array.of_list fresh)
        in
        Hashtbl.set layers ~key:(arity, l) ~data:a;
        a
end

(* ------------------------------------------------------------------ *)
(* A slot: the terms one position of an enumerated item ranges over     *)
(* ------------------------------------------------------------------ *)

(* The term space of one position: integer terms over [int_params] or real
   terms over [real_params], read as old terms.  [size l] is the length of
   layer [l]'s list; [term l i] its [i]-th term ([i < size l]); the lists
   extend each other as prefixes, so [term l i = term l' i] whenever both
   are defined. *)
type slot = { size : int -> int; term : int -> int -> Term.t }

let int_slot (params : Ident.tvar array) =
  let arity = Array.length params in
  {
    size = (fun l -> Array.length (Ints.layer ~arity l));
    term = (fun l i -> Ints.to_term params (Ints.layer ~arity l).(i));
  }

let real_slot (params : Ident.tvar array) =
  let arity = Array.length params in
  {
    size = (fun l -> Array.length (Reals.layer ~arity l));
    term = (fun l i -> Reals.to_term params (Reals.layer ~arity l).(i));
  }

(* ------------------------------------------------------------------ *)
(* Shell enumeration of index vectors                                   *)
(* ------------------------------------------------------------------ *)

(* An odometer over the index vectors [v] with [v.(i) < bounds.(i)] whose
   largest entry is exactly [b] and which are not all below [old.(i)]; the
   vectors of one shell, in a fixed order.  [next] returns [None] once the
   shell is exhausted. *)
module Shell = struct
  type t = {
    bounds : int array;
    old : int array;
    b : int;
    cur : int array;
    mutable started : bool;
    mutable finished : bool;
  }

  let create ~bounds ~old b =
    let n = Array.length bounds in
    {
      bounds;
      old;
      b;
      cur = Array.create ~len:n 0;
      started = false;
      finished = n = 0 && b > 0;
    }

  let limit t i = Int.min t.b (t.bounds.(i) - 1)

  (* advance the odometer over the box [0 .. limit i]; [false] when it wraps *)
  let step t =
    let n = Array.length t.cur in
    let rec go i =
      if i >= n then false
      else if t.cur.(i) < limit t i then (
        t.cur.(i) <- t.cur.(i) + 1;
        true)
      else (
        t.cur.(i) <- 0;
        go (i + 1))
    in
    go 0

  let valid t =
    let n = Array.length t.cur in
    Array.for_alli t.cur ~f:(fun i v -> v <= limit t i)
    && (n = 0 || Array.exists t.cur ~f:(fun v -> v = t.b))
    && not (n > 0 && Array.for_alli t.cur ~f:(fun i v -> v < t.old.(i)))

  let rec next t =
    if t.finished then None
    else if Array.exists (Array.init (Array.length t.bounds) ~f:Fn.id) ~f:(fun i -> limit t i < 0)
    then (
      t.finished <- true;
      None)
    else (
      if not t.started then t.started <- true
      else if not (step t) then t.finished <- true;
      if t.finished then None
      else if valid t then Some (Array.copy t.cur)
      else next t)
end

(* ------------------------------------------------------------------ *)
(* Layered enumeration of fixed-length vectors of slot terms            *)
(* ------------------------------------------------------------------ *)

(* A cursor over the vectors of terms of [slots] (one per slot), layer by
   layer and shell by shell within a layer; each vector of each layer is
   returned exactly once, after finitely many calls.  [layer_done l] tells
   whether every vector of layers [<= l] has been returned. *)
module Vectors = struct
  type t = {
    slots : slot array;
    mutable layer : int;
    mutable shell : Shell.t option;
    mutable b : int;
    mutable completed : int;  (** the largest layer wholly returned *)
  }

  let create slots = { slots; layer = 1; shell = None; b = 0; completed = 0 }

  let bounds t l = Array.map t.slots ~f:(fun s -> s.size l)

  let rec next t =
    let l = t.layer in
    let bounds = bounds t l in
    let old = bounds_old t l in
    let maxb = Array.fold bounds ~init:0 ~f:Int.max - 1 in
    match t.shell with
    | None ->
        if Array.is_empty t.slots then (
          (* one empty vector, in layer 1 *)
          if t.completed >= 1 then None
          else (
            t.completed <- Int.max_value;
            Some [||]))
        else (
          t.shell <- Some (Shell.create ~bounds ~old t.b);
          next t)
    | Some sh -> (
        match Shell.next sh with
        | Some v -> Some (Array.mapi v ~f:(fun i j -> t.slots.(i).term l j))
        | None ->
            if t.b < maxb then (
              t.b <- t.b + 1;
              t.shell <- Some (Shell.create ~bounds ~old t.b);
              next t)
            else (
              t.completed <- l;
              t.layer <- l + 1;
              t.b <- 0;
              t.shell <- None;
              next t))

  and bounds_old t l = if l <= 1 then Array.map t.slots ~f:(fun _ -> 0) else bounds t (l - 1)

  let layer_done t l = t.completed >= l
end

(* ------------------------------------------------------------------ *)
(* Ranking-function relations                                           *)
(* ------------------------------------------------------------------ *)

module Rankings = struct
  (* The state space of one ranking key: the variables of its earlier state
     [earlier] and of its later state [later] (same length, position by
     position), and the slot its component terms are drawn from, over
     [earlier].  A key whose state is all real takes real affine terms; any
     other takes integer terms over its integer positions (a real position of
     a mixed state is then not read by any component: the space for such a
     key is the integer part only). *)
  type key = {
    earlier : (Ident.tvar * Sort.t) array;
    later : (Ident.tvar * Sort.t) array;
    slot : slot;
    real : bool;
  }

  let key_of ~earlier ~later =
    let earlier = Array.of_list earlier and later = Array.of_list later in
    let is_real (_, s) = Stdlib.(s = T_real.SReal) in
    let is_int (_, s) = Stdlib.(s = T_int.SInt) in
    if (not (Array.is_empty earlier)) && Array.for_all earlier ~f:is_real then
      { earlier; later; slot = real_slot (Array.map earlier ~f:fst); real = true }
    else
      let ints = Array.filter earlier ~f:is_int in
      { earlier; later; slot = int_slot (Array.map ints ~f:fst); real = false }

  (* A component: a decision list, [guards] one shorter than [terms]. *)
  type component = { guards : Term.t list; terms : Term.t list }

  let zero k = if k.real then T_real.mk_real Q.zero else T_int.mk_int Z.zero
  let one k = if k.real then T_real.mk_real Q.one else T_int.mk_int Z.one
  let sub k a b = if k.real then T_real.mk_rsub a b else T_int.mk_sub a b

  (* the value of [c] at the earlier state *)
  let value k c =
    let rec go gs ts =
      match (gs, ts) with
      | [], [ t ] -> t
      | g :: gs, t :: ts -> T_bool.ifte (Formula.geq g (zero k)) t (go gs ts)
      | _ -> failwith "RelComplete.Rankings.value: a guard count not one less than the term count"
    in
    go c.guards c.terms

  let at_later k t =
    let map =
      Map.Poly.of_alist_exn
        (Array.to_list
           (Array.map2_exn k.earlier k.later ~f:(fun (x, _) (y, s) ->
                (x, Term.mk_var y s))))
    in
    Term.subst map t

  (* [relation k comps]: [W_r(c, y)] with [c] the earlier and [y] the later
     state.  Pre: [comps] nonempty.  Post: a formula over the two states that
     is well-founded and transitive as a relation from [c] to [y], whatever
     the components (each disjunct asks the first differing component to
     drop by at least 1 from a value at least 0, the earlier ones equal). *)
  let relation k comps =
    let vals =
      List.map comps ~f:(fun c ->
          let v = value k c in
          (v, at_later k v))
    in
    Formula.or_of
      (List.mapi vals ~f:(fun j (vc, vy) ->
           Formula.and_of
             (List.filteri vals ~f:(fun i _ -> i < j)
              |> List.map ~f:(fun (uc, uy) -> Formula.eq uc uy))
           |> fun eqs ->
           Formula.and_of
             [ eqs; Formula.geq (sub k vc vy) (one k); Formula.geq vc (zero k) ]))

  (* A shape for a side: per key, the piece count of each component. *)
  let shapes ~keys l =
    let per_key =
      List.concat_map (List.init l ~f:(fun k -> k + 1)) ~f:(fun k ->
          (* the piece-count vectors of length [k] with entries in [1 .. l] *)
          let rec vecs n =
            if n = 0 then [ [] ]
            else
              List.concat_map (List.init l ~f:(fun p -> p + 1)) ~f:(fun p ->
                  List.map (vecs (n - 1)) ~f:(fun v -> p :: v))
          in
          vecs k)
    in
    let rec prod n = if n = 0 then [ [] ] else List.concat_map per_key ~f:(fun s -> List.map (prod (n - 1)) ~f:(fun r -> s :: r)) in
    prod keys

  let fits l shape = List.for_all shape ~f:(fun comps -> List.length comps <= l && List.for_all comps ~f:(fun p -> p <= l))

  (* A cursor over the rankings of a side (one relation per key), layer by
     layer: within layer [l], shape by shape (shapes in a fixed order), shell
     by shell, skipping what layer [l - 1] returned.  Each ranking tuple of
     each layer is returned once.  [layer_done l] as for [Vectors]. *)
  type cursor = {
    keys : key array;
    mutable layer : int;
    mutable entered : bool;
    mutable shapes_left : int list list list;
    mutable shape : int list list option;
    mutable b : int;
    mutable shell : Shell.t option;
    mutable completed : int;
  }

  let cursor keys =
    {
      keys = Array.of_list keys;
      layer = 1;
      entered = false;
      shapes_left = [];
      shape = None;
      b = 0;
      shell = None;
      completed = 0;
    }

  let slots_of c shape =
    List.concat_mapi shape ~f:(fun ki comps ->
        List.concat_map comps ~f:(fun p ->
            List.init ((2 * p) - 1) ~f:(fun _ -> c.keys.(ki).slot)))
    |> Array.of_list

  let build c l shape (v : int array) =
    let pos = ref 0 in
    let take ki =
      let t = c.keys.(ki).slot.term l v.(!pos) in
      incr pos;
      t
    in
    List.mapi shape ~f:(fun ki comps ->
        let k = c.keys.(ki) in
        let comps =
          List.map comps ~f:(fun p ->
              let guards = List.init (p - 1) ~f:(fun _ -> take ki) in
              let terms = List.init p ~f:(fun _ -> take ki) in
              { guards; terms })
        in
        relation k comps)

  let shell_of c l shape b =
    let slots = slots_of c shape in
    let bounds = Array.map slots ~f:(fun s -> s.size l) in
    let old =
      if l > 1 && fits (l - 1) shape then
        Array.map slots ~f:(fun s -> s.size (l - 1))
      else Array.map slots ~f:(fun _ -> 0)
    in
    Shell.create ~bounds ~old b

  (* Post: [Some r] is a list with one relation per key, in [keys] order. *)
  let rec next c =
    if Array.is_empty c.keys then
      if c.completed >= 1 then None
      else (
        c.completed <- Int.max_value;
        Some [])
    else
      match (c.shape, c.shell) with
      | Some shape, Some sh -> (
          match Shell.next sh with
          | Some v -> Some (build c c.layer shape v)
          | None ->
              let maxb =
                Array.fold (slots_of c shape) ~init:0 ~f:(fun m s ->
                    Int.max m (s.size c.layer))
                - 1
              in
              if c.b < maxb then (
                c.b <- c.b + 1;
                c.shell <- Some (shell_of c c.layer shape c.b))
              else (
                c.shape <- None;
                c.shell <- None);
              next c)
      | _ -> (
          match c.shapes_left with
          | shape :: rest ->
              c.shapes_left <- rest;
              c.shape <- Some shape;
              c.b <- 0;
              c.shell <- Some (shell_of c c.layer shape 0);
              next c
          | [] ->
              if c.entered then (
                c.completed <- c.layer;
                c.layer <- c.layer + 1);
              c.entered <- true;
              c.shapes_left <- shapes ~keys:(Array.length c.keys) c.layer;
              next c)

  let layer_done c l = c.completed >= l
end
