open Core
open Common.Ext
open Ast.LogicOld

type t =
  (* valid sequent *)
  | Valid of Sequent.t
  (* invalid sequent *)
  | InValid of Sequent.t * model
  (* abort proof search for invalid sequent *)
  | Abort of Sequent.t
  (* unfold an atom *)
  | Unfold of Sequent.t * (Atom.t * Sequent.guard) * t list
  (* fold atoms *)
  | Fold of Sequent.t * (Atom.t * Sequent.guard) list * t
  (* perform induction on the derivation of an atom & introduce an induction hypothesis *)
  | Induct of Sequent.t * (Atom.t * Sequent.guard) * Lemma.t * t
  (* apply induction hypotheses or lemmas *)
  | Apply of Sequent.t * Lemma.t list * t

(** {6 Inspectors} *)

let rec is_valid = function
  | Valid _ -> true
  | InValid _ -> false
  | Abort _ -> false
  | Unfold (_, _, ts) -> List.for_all ~f:is_valid ts
  | Fold (_, _, t) -> is_valid t
  | Induct (_, _, _, t) -> is_valid t
  | Apply (_, _, t) -> is_valid t

let rec is_failure = function
  | Valid _ -> false
  | InValid _ -> false
  | Abort _ -> true
  | Unfold (_, _, ts) -> List.exists ~f:is_failure ts
  | Fold (_, _, t) -> is_failure t
  | Induct (_, _, _, t) -> is_failure t
  | Apply (_, _, t) -> is_failure t

let rec size = function
  | Valid _ -> 1
  | InValid _ -> 1
  | Abort _ -> assert false (*ToDo*)
  | Unfold (_, _, ts) -> List.fold_left ~f:( + ) ~init:1 @@ List.map ~f:size ts
  | Fold (_, _, t) -> 1 + size t
  | Induct (_, _, _, t) -> size t
  | Apply (_, _, t) -> 1 + size t

(** {6 Printers} *)

let pr_judgement ppf
    ((defs : MuCLP.Pred.t list), (lemmas : Lemma.t list), (sequent : Sequent.t))
    =
  Format.fprintf ppf "----------------------------@.";
  Format.fprintf ppf "@[<v 2>[D]:@;%a@.@]" MuCLP.Pred.pr_list defs;
  Format.fprintf ppf "@[<v 2>[Gamma]:@;%a@.@]"
    (Lemma.pr_list ~wo_guard:false)
    lemmas;
  Format.fprintf ppf "@[<v 2>[Sequent]:@;%a@.@]"
    (Sequent.pr ~wo_guard:false)
    sequent;
  Format.fprintf ppf "----------------------------@."

(*
let logpr_pvam (pva, m) =
  Logger.printf "(%a * " Pva.pr pva;
  Logger.printf0 "{";
  List.iter (Logger.printf "_a%a, " Integer.pr) m;
  Logger.printf0 "})"

let rec logpr_pvams = function
  | [] -> Logger.printf0 "@."
  | a::rest ->
    logpr_pvam a;
    Logger.printf0 ";@.";
    logpr_pvams rest

let logpr_phi phi =
  Logger.printf "%a@." Formula.pr phi

let logpr_guard = function
  | None -> ()
  | Some (pv, m) ->
    Logger.printf "(_a%a * " Integer.pr m;
    Logger.printf "%a)" Pvar.pr pv

let rec logpr_gamma gamma =
  Logger.printf "[Gamma]:  %a@." Lemma.pr gamma

let logpr_judgement (J(dcs, gamma, ent)) =
  Logger.printf0 "----------------------------@.";
  Logger.printf  "[D]: @,%a@." HCCS.pr dcs;
  Logger.printf  "[Gamma]: @,%a@." Lemma.pr gamma;
  Logger.printf  "[Sequent]: @,%a@." Sequent.pr ent;
  Logger.printf0 "----------------------------@."

let pr_judgement_tex (J(dcs, gamma, ent)) =
  Format.printf "@.\\begin{matrix}@.";
  Format.printf "\\left[phi\\right]:\\\\ @,";
  HCCS.pr_tex Format.std_formatter dcs;
  Format.printf "@.\\end{matrix}@.";

  Format.printf "@.\\begin{matrix}@.";
  Format.printf "@.\\left[Gamma\\right]:\\\\  @,";
  Lemma.pr_tex Format.std_formatter gamma;
  Format.printf "@.\\end{matrix}@.";
  Format.printf "@.\\begin{matrix}@.";
  Format.printf "\\left[A\\right]:\\\\ @,";
  Format.printf "@.\\end{matrix}@.";

  Format.printf "@.\\begin{matrix}@.";
  Format.printf "@.\\left[h\\right]:\\\\ @,";
  Lemma.pr_tex Format.std_formatter dcs;
  Format.printf "@.\\end{matrix}@."

let rec pr depth = function
  | Node(j, ptree) ->
    pr_judgement j;
    pr depth ptree
  | Unfold(pvam, ptrees) ->
    Format.printf "<rule(Unfold)>: Unfolded %a@.@." Pvam.pr pvam;
    List.iteri
      (fun i pt ->
         let depth' = i::depth in
         Format.printf "Unfold(Case %a): %a@."
           (List.pr Integer.pr "-") (List.rev depth') Pvam.pr pvam;
         pr depth' pt)
      ptrees
  | Induct(pvam, gam, ptree) ->
    Format.printf "<rule(Induct)>:@.%a" Pvam.pr pvam;
    Format.printf "@.added hypothesis: @.%a@." Lemma.pr_elem gam;
    pr depth ptree
  | Fold(newla, ptree) ->
    Format.printf "<rule(Fold)>:@.";
    Format.printf "added A:@.%a" Pvam.pr_list newla;
    pr depth ptree
  | Apply (gamma, ptree) ->
    Format.printf "<rule(Apply)>:@.";
    Format.printf "applied hypothesis of lemma:@.%a@." Lemma.pr gamma;
    pr depth ptree
  | Valid ent ->
    Format.printf "<rule(Valid)>:@.";
    Format.printf "%a@." Sequent.pr ent;
    Format.printf "is Valid!(end)@,@."
  | InValid(ent,m) ->
    Format.printf
      "!! Invalid !!@.:: Invalid goal: %a@.:: Counterexample: %a@."
      Sequent.pr ent
      TermSubst.pr m
  (*| Failure s -> Format.printf "Failure (%a)" String.pr s*)
  | Abort j -> pr_judgement j

let pr = pr []

let pr_all =
  List.iteri
    (fun i pt ->
       Format.printf "@.[Theorem proving(No.%a)]@." Integer.pr i;
       pr pt;
       Format.printf "---------QED(No.%a)----------@." Integer.pr i)

let buff_lems = ref []
let pr_tex pt =
  let name_count = ref 0 in
  let fresh_name () =
    name_count:=(!name_count + 1);
    !name_count
  in
  (* inner : t -> string list *)
  let rec inner depth = function
    | Node(j, ptree) ->
      let rule_name =
        begin
          match ptree with
          | Node    _ -> ""
          | Unfold  _ -> "unfold"
          | Induct  _ -> "induct"
          | Fold    _ -> "fold"
          | Apply   _ -> "apply"
          | Valid   _ -> "valid"
          | InValid _ -> "invalid"
          | Abort   _ -> "abort"
        end
      in
      let p_name = sprintf "P%d" (fresh_name()) in
      Format.printf "\\infer[%s]{%s}@." rule_name p_name;
      buff_lems := (p_name, Node(j, ptree))::(!buff_lems);
      (* print_judgement_tree j;*)
      inner depth ptree
    | Unfold(pvam, ptrees) ->
      Format.printf "{@.";
      List.iteri
        (fun i pt ->
           let depth' = i::depth in
           Format.printf "@.";
           inner depth' pt)
        ptrees;
      Format.printf "}@."
    | Induct(_, _, ptree) ->
      Format.printf "{@.";
      inner depth ptree;
      Format.printf "}@."
    | Fold(newla, ptree) ->
      Format.printf "{@.";
      inner depth ptree;
      Format.printf "}@."
    | Apply (_, ptree) ->
      Format.printf "{@.";
      inner depth ptree;
      Format.printf "}@."
    | Valid ent ->
      Format.printf "{@.";
      Format.printf "%a@." Sequent.pr_tex ent;
      Format.printf "is Valid!(end)@,@.";
      Format.printf "}@."
    | InValid(ent,m) ->
      Format.printf
        "!! Invalid !!@.invalid subgoal: %a@.counterexample: %a@"
        Sequent.pr_tex ent
        TermSubst.pr m
    (*| Failure s -> Format.printf "Failure (%a)" String.pr s*)
    | Abort j -> ()
  in
  Format.printf "@.$$@.";
  inner [] pt

let pr_all_tex =
  List.iteri
    (fun i pt ->
       Format.printf "@.Theorem proving(No.%a)@." Integer.pr i;
       pr_tex pt;
       Format.printf "QED(No.%a)@." Integer.pr i;
       Format.printf "where@.";
       buff_lems := List.rev (!buff_lems);
       List.iter
         (function
             (name, Node (j, _)) ->
             Format.printf "\\section{%s}@." name;
             pr_judgement_tex j
           | _ -> failwith "unmatch prooftree in ProofTree.pr_all_tex") !buff_lems)

let rec pr_outline ppf pt =
  match pt with
  | Node(_, t)       -> pr_outline tppf
  | Fold(_, t)       -> Format.fprintf ppf "@[<v 3>Fold@;%a@]" pr_outline t
  | Apply(_, t)   -> Format.fprintf ppf "@[<v 3>Apply@;%a@]" pr_outline t
  | Valid _          -> Format.fprintf ppf "Valid"
  | InValid _        -> Format.fprintf ppf "InValid"
  | Induct(_, _, t)  -> pr_outline t ppf (* Omit Induct *)
  | Unfold(_, tl) ->
    let pr_branch ppf pt = pr_outline pt ppf in
    Format.fprintf ppf "@[<v 3>Unfold@;%a@]" (List.pr pr_branch "@;") tl
  (*| Failure s -> Format.printf "Failure (%a)" String.pr s*)
  | Abort _           -> Format.fprintf ppf "Abort"

let pr_json ppf pt =
  if is_failure pt then
    match pt with
    | Failure "Failure(\"do not fit in goal clause\")" ->
      Format.fprintf ppf "  {\"is_valid\": \"failure_pdr\", \"size\": 0}"
    | Failure "Fpat.Timer.Timeout" ->
      Format.fprintf ppf "  {\"is_valid\": \"failure_timeout\", \"size\": 0}"
    | Failure s ->
      Format.fprintf ppf "  {\"is_valid\": \"failure_indsolver\", \"size\": 0}"
    | _ -> assert false
  else
    Format.fprintf ppf "  {\"is_valid\": %b, \"size\": %d}" (is_valid pt) (size pt)
let pr_json_list ppf pts =
  Format.fprintf ppf "[@.%a@.]" (List.pr pr_json ",@.") pts

*)

(** Live ProofTree (make and print incomplete proof tree overview) *)

module LivePT = struct
  type t =
    | ToProve (* Frontier of the proof *)
    | Valid
    | InValid
    | Unfold of (Atom.t * Sequent.guard) * t list
    | Fold of t
    | Induct of t
    | Apply of Sequent.guard * t

  let mk_root () = ToProve

  let rec insert_new_node mk_node =
    let rec insert_to_branch = function
      | [] -> []
      | ToProve :: tl -> mk_node () :: tl
      | hd :: tl ->
          let hd' = insert_new_node mk_node hd in
          if Stdlib.(hd = hd') then hd :: insert_to_branch tl else hd' :: tl
    in
    function
    | ToProve -> mk_node ()
    | Valid -> Valid
    | InValid -> InValid
    | Unfold (p, l) -> Unfold (p, insert_to_branch l)
    | Fold t -> Fold (insert_new_node mk_node t)
    | Induct t -> Induct (insert_new_node mk_node t)
    | Apply (l, t) -> Apply (l, insert_new_node mk_node t)

  let mk_valid = insert_new_node (fun () -> Valid)
  let mk_invalid = insert_new_node (fun () -> InValid)
  let mk_induct = insert_new_node (fun () -> Induct ToProve)
  let mk_apply l = insert_new_node (fun () -> Apply (l, ToProve))
  let mk_fold = insert_new_node (fun () -> Fold ToProve)

  let mk_unfold p n =
    insert_new_node (fun () -> Unfold (p, List.gen n (fun _ -> ToProve)))

  let rec pr ppf (pt, depth) =
    for _ = 1 to depth do
      Format.fprintf ppf "|  "
    done;
    match pt with
    | ToProve -> Format.fprintf ppf "[To be proved]"
    | Valid -> Format.fprintf ppf "Valid"
    | InValid -> Format.fprintf ppf "InValid"
    | Unfold ((atm, _), tl) ->
        Format.fprintf ppf "Unfold %s@;%a" (Atom.str_of atm) (List.pr pr "@;")
          (List.map tl ~f:(fun t -> (t, depth + 1)))
    | Fold t -> Format.fprintf ppf "Fold@;%a" pr (t, depth + 1)
    | Induct t -> Format.fprintf ppf "Induct@;%a" pr (t, depth + 1)
    | Apply (guard, t) ->
        let epr ppf (_, i) = Format.fprintf ppf "[%d]" i in
        Format.fprintf ppf "Apply %a@;%a" (List.pr_aux epr "," 0)
          (Set.to_list guard) pr
          (t, depth + 1)

  let pr ppf pt = Format.fprintf ppf "@[<v>%a@]" pr (pt, 0)
end
