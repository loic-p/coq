(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Declarations

let rec arg_pattern_of_constr t = kind t |> function
  | Rel _ -> APHole
  | App (f, args) -> APApp (arg_pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Ind (ind, _) -> APInd ind
  | Construct (c, _) -> APConstr c
  | Int i -> APInt i
  | Float f -> APFloat f
  | _ -> assert false

let rec pattern_of_constr t = kind t |> function
  | Const (c, _) -> PConst c
  | App (f, args) -> PApp (pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Case (ci, _, _, p, _, c, brs) -> PCase (ci.ci_ind, arg_pattern_of_constr (snd p), pattern_of_constr c, Array.map (fun (_, br) -> arg_pattern_of_constr br) brs)
  | Proj (p, c) -> PProj (p, pattern_of_constr c)
  | _ -> assert false

let rec safe_arg_pattern_of_constr nvar t = kind t |> function
  | Rel i ->
      if nvar <> i then CErrors.anomaly Pp.(str "Variable " ++ Constr.debug_print t ++ str" not used at the right place, expected "++ Constr.debug_print (of_kind (Rel nvar)) ++str".");
      (succ nvar, APHole)
  | App (f, args) ->
      let nvar, pf = safe_arg_pattern_of_constr nvar f in
      let nvar, pargs = Array.fold_left_map safe_arg_pattern_of_constr nvar args in
      nvar, APApp (pf, pargs)
  | Ind (ind, _) -> nvar, APInd ind
  | Construct (c, _) -> nvar, APConstr c
  | Int i -> nvar, APInt i
  | Float f -> nvar, APFloat f
  | _ -> CErrors.anomaly Pp.(str "Subterm not recognised as arg_pattern" ++ Constr.debug_print t)

let rec safe_pattern_of_constr env nvar t = kind t |> function
  | Const (c, _) ->
      (match (Environ.lookup_constant c env).const_body with
      | Def _ | OpaqueDef _ | Primitive _ ->
          CErrors.anomaly Pp.(str "Constant " ++ Constant.print c ++ str" used in pattern has a body.")
      | Undef _ -> ());
      nvar, PConst c
  | App (f, args) ->
      let nvar, pf = safe_pattern_of_constr env nvar f in
      let nvar, pargs = Array.fold_left_map safe_arg_pattern_of_constr nvar args in
      nvar, PApp (pf, pargs)
  | Case (ci, _, _, (_, ret), _, c, brs) ->
      let nvar, pc = safe_pattern_of_constr env nvar c in
      let nvar, pret = safe_arg_pattern_of_constr nvar ret in
      let nvar, pbrs = Array.fold_left_map (fun nvar (_, br) -> safe_arg_pattern_of_constr nvar br) nvar brs in
      nvar, PCase (ci.ci_ind, pret, pc, pbrs)
  | Proj (p, c) ->
      let nvar, pc = safe_pattern_of_constr env nvar c in
      nvar, PProj (p, pc)
  | _ -> CErrors.anomaly Pp.(str "Subterm not recognised as pattern" ++ Constr.debug_print t)

let rec head_constant = function
  | PConst c -> c
  | PApp (h, _) -> head_constant h
  | PCase (_, _, c, _) -> head_constant c
  | PProj (_, c) -> head_constant c

let rule_of_constant env c =
  let cb = Environ.lookup_constant c env in
  match cb.const_universes with
  | Polymorphic _ ->
    CErrors.user_err Pp.(str "Universe polymophic rewrite rules not supported yet.")
  | Monomorphic ->
    match kind cb.const_type with
    (* XXX should be checking that the head is eq not some arbitrary inductive
       Maybe by registering eq in retroknowledge *)
    | App (hd, [|_;lhs;rhs|]) when isInd hd ->
      let lhs_pat = pattern_of_constr lhs in
      head_constant lhs_pat, { lhs_pat = lhs_pat; rhs; }
    | _ ->
      CErrors.user_err
        Pp.(str "Cannot declare as rewrite rule: doesn't look like a proof of equality.")
