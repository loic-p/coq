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

let app_pattern_of_constr n t =
  let f, args = decompose_appvect t in
  let nargs = Array.length args in
  assert (nargs >= n);
  let remargs, usedargs = Array.chop (nargs - n) args in
  let pusedargs = Array.map (kind %> function Rel _ -> APHoleIgnored | _ -> assert false) usedargs in
  let t' = mkApp (f, remargs) in
  let p' = arg_pattern_of_constr t' in
  match p' with APApp (pf, pargs) -> APApp (pf, Array.append pargs pusedargs) | _ -> APApp (p', pusedargs)

let app_pattern_of_constr' p = app_pattern_of_constr (Array.length (fst p)) (snd p)

let rec pattern_of_constr t = kind t |> function
  | Const (c, _) -> PConst c
  | App (f, args) -> PApp (pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Case (ci, _, _, p, _, c, brs) ->
      PCase (ci.ci_ind, app_pattern_of_constr' p, pattern_of_constr c, Array.map app_pattern_of_constr' brs)
  | Proj (p, c) -> PProj (p, pattern_of_constr c)
  | _ -> assert false

let rec safe_arg_pattern_of_constr remvar t = kind t |> function
  | Rel i ->
      if remvar <> i then CErrors.anomaly Pp.(str "Variable " ++ Constr.debug_print t ++ str" not used at the right place, expected "++ Constr.debug_print (of_kind (Rel remvar)) ++str".");
      (pred remvar, APHole)
  | App (f, args) ->
      let remvar, pf = safe_arg_pattern_of_constr remvar f in
      let remvar, pargs = Array.fold_left_map safe_arg_pattern_of_constr remvar args in
      remvar, APApp (pf, pargs)
  | Ind (ind, _) -> remvar, APInd ind
  | Construct (c, _) -> remvar, APConstr c
  | Int i -> remvar, APInt i
  | Float f -> remvar, APFloat f
  | _ -> CErrors.anomaly Pp.(str "Subterm not recognised as arg_pattern" ++ Constr.debug_print t)

let safe_app_pattern_of_constr remvar n t =
  let f, args = decompose_appvect t in
  let nargs = Array.length args in
  if not (nargs >= n) then CErrors.anomaly Pp.(str "Subterm not recognised as pattern under binders" ++ Constr.debug_print t);
  let remargs, usedargs = Array.chop (nargs - n) args in
  let pusedargs = Array.map
    (kind %> function
      | Rel i when i <= n -> APHoleIgnored
      | t -> CErrors.anomaly Pp.(str "Subterm not recognised as pattern under binders" ++ Constr.debug_print (of_kind t)))
    usedargs
  in
  let t' = mkApp (f, remargs) in
  let (remvar, p') = safe_arg_pattern_of_constr (remvar + n) t' in
  remvar - n, match p' with APApp (pf, pargs) -> APApp (pf, Array.append pargs pusedargs) | _ -> APApp (p', pusedargs)

let safe_app_pattern_of_constr' remvar p = safe_app_pattern_of_constr remvar (Array.length (fst p)) (snd p)


let rec safe_pattern_of_constr env remvar t = kind t |> function
  | Const (c, _) ->
      (match (Environ.lookup_constant c env).const_body with
      | Def _ | OpaqueDef _ | Primitive _ ->
          CErrors.anomaly Pp.(str "Constant " ++ Constant.print c ++ str" used in pattern has a body.")
      | Undef _ -> ());
      remvar, PConst c
  | App (f, args) ->
      let remvar, pf = safe_pattern_of_constr env remvar f in
      let remvar, pargs = Array.fold_left_map safe_arg_pattern_of_constr remvar args in
      remvar, PApp (pf, pargs)
  | Case (ci, _, _, ret, _, c, brs) ->
      let remvar, pc = safe_pattern_of_constr env remvar c in
      let remvar, pret = safe_app_pattern_of_constr' remvar ret in
      let remvar, pbrs = Array.fold_left_map safe_app_pattern_of_constr' remvar brs in
      remvar, PCase (ci.ci_ind, pret, pc, pbrs)
  | Proj (p, c) ->
      let remvar, pc = safe_pattern_of_constr env remvar c in
      remvar, PProj (p, pc)
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
    let ctx, eq_rule = Term.decompose_prod_decls cb.const_type in
    match kind eq_rule with
    (* XXX should be checking that the head is eq not some arbitrary inductive
       Maybe by registering eq in retroknowledge *)
    | App (hd, [|_;lhs;rhs|]) when isInd hd ->
      let rem_hyps, lhs_pat = safe_pattern_of_constr env (Context.Rel.nhyps ctx) lhs in
      assert (rem_hyps = 0);
      head_constant lhs_pat, { lhs_pat = lhs_pat; rhs; }
    | _ ->
      CErrors.user_err
        Pp.(str "Cannot declare as rewrite rule: doesn't look like a proof of equality.")
