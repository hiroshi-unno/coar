open Core
open Common.Ext
open Ast
open Ast.Logic

(* Dropping, from a clause that defines an unknown, the premises that every
   use of that unknown already has.

   The shape it is for.  A program verifier that gives the result of each
   call an unknown over the variables in scope emits, per basic block, a
   clause whose premises apply the unknown of every earlier call, each over
   its own copy of the live variables, tied to the rest of the clause by
   equations:

     p1(y1) /\ ... /\ p(k-1)(y(k-1)) /\ phi_k -> pk(x)

   and every later clause applies [pk] beside [p1 .. p(k-1)] again.  Inlining
   [pk]'s least solution into a use (what predicate elimination does) brings
   along a copy of [p1 .. p(k-1)] that the use already has, with private
   names, so each unknown is copied once per later use and the inlined
   formula is exponential in the length of the chain.  With the premises
   dropped from the definition, [pk] is defined by [phi_k] alone -- the
   callee's contract and the equations -- which is what the verifier emits
   when it types the call's result by the callee's contract directly, and
   the uses keep the facts through their own atoms.

   Which premises are dropped.  For an unknown [p], let [req p] be the
   unknowns other than [p] that the body of EVERY clause applying [p] in its
   body also applies (undefined when no clause applies [p] in its body).  From
   every clause whose head is the single atom [p(..)] and whose body does not
   apply [p], every body atom of an unknown in [req p] is dropped.  The test
   is computed once, on the given clauses.

   Contract.  Assumes: [clauses] are in clausal form (heads [ps], premises
   [ns], pure part [phi]).  Guarantees: the result is the given list with some
   clauses' premise sets made subsets of the given ones and nothing else
   changed, in the same order; [dropped] counts the atoms removed and
   [clauses] the clauses that lost one.

   Why a [sat] of the result is a [sat] of the input, and nothing else is.
   A clause is the implication from its premises to its head; removing a
   premise gives a clause that implies the original under every
   interpretation of the unknowns.  So every solution of the result, in every
   model of the background theory, is a solution of the input: the unknowns,
   their sorts and kinds are the same, and each clause of the input is
   implied by its counterpart.  The converse fails -- the dropped premise may
   be what makes the definition hold -- so an [unsat] (or any other outcome)
   of the result says nothing about the input.  Nothing here depends on the
   test above, which only chooses premises the uses are likely to supply
   themselves. *)

type stats = { clauses : int; dropped : int; unknowns : int }

let strengthen (clauses : Clause.t list) : Clause.t list * stats =
  let body_pvs = List.map clauses ~f:Clause.neg_pvars in
  (* [req p], as the intersection of the body unknowns of the clauses using
     [p] *)
  let req = Hashtbl.Poly.create () in
  List.iter body_pvs ~f:(fun pvs ->
      Set.iter pvs ~f:(fun p ->
          let others = Set.remove pvs p in
          Hashtbl.update req p ~f:(function
            | None -> others
            | Some acc -> Set.inter acc others)));
  let touched_unknowns = Hash_set.Poly.create () in
  let changed = ref 0 and dropped = ref 0 in
  let clauses =
    List.map2_exn clauses body_pvs
      ~f:(fun ((senv, ps, ns, phi) as cl) bpvs ->
        match Set.to_list (Clause.pos_pvars cl) with
        | [ p ] when Set.length ps = 1 && not (Set.mem bpvs p) -> (
            match Hashtbl.find req p with
            | None -> cl
            | Some r when Set.is_empty r -> cl
            | Some r ->
                let ns' =
                  Set.filter ns ~f:(fun a ->
                      not (Set.mem r (Term.pvar_of_atom a)))
                in
                let n = Set.length ns - Set.length ns' in
                if n = 0 then cl
                else (
                  incr changed;
                  dropped := !dropped + n;
                  Hash_set.add touched_unknowns p;
                  Clause.canon (senv, ps, ns', phi)))
        | _ -> cl)
  in
  ( clauses,
    {
      clauses = !changed;
      dropped = !dropped;
      unknowns = Hash_set.length touched_unknowns;
    } )
