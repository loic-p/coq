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
open Constr
open Declarations

type state = (int * int Evar.Map.t) * (int * int Int.Map.t) * (int * bool list * int Int.Map.t)

let rec is_rel_inst k = function
  | SList.Nil -> true
  | SList.Default _ -> false
  | SList.Cons (t, l) -> kind t = Rel k && is_rel_inst (succ k) l

let update_invtbl ~loc env evd evk (curvar, tbl) =
  match Evar.Map.find_opt evk tbl with
  | None -> curvar, (succ curvar, Evar.Map.add evk curvar tbl)
  | Some v -> v, (curvar, tbl)

let update_invtblu1 ~loc ~(alg:bool) evd lvlold lvl (curvaru, alg_vars, tbl) =
  match Int.Map.find_opt lvl tbl with
  | None -> succ curvaru, alg :: alg_vars, Int.Map.add lvl curvaru tbl
  | Some v -> curvaru, alg_vars, tbl

let update_invtblq1 ~loc evd qold qvar (curvarq, tbl) =
  match Int.Map.find_opt qvar tbl with
  | None -> succ curvarq, Int.Map.add qvar curvarq tbl
  | Some v -> curvarq, tbl

let quality_pattern_of_quality_constant =
  let open Sorts.Quality in
  function
  | QProp -> PQProp
  | QSProp -> PQSProp
  | QType -> PQType

let safe_quality_pattern_of_quality ~loc evd qsubst stateq q =
  match Sorts.Quality.(subst (subst_fn qsubst) q) with
  | QConstant qc -> stateq, quality_pattern_of_quality_constant qc
  | QVar qv ->
    let qio = Sorts.QVar.var_index qv in
    let stateq = Option.fold_right (update_invtblq1 ~loc evd q) qio stateq in
    stateq, PQVar qio

let update_invtblu ~loc evd (qsubst, usubst) (state, stateq, stateu : state) u : state * _ =
  let (q, u) = u |> UVars.Instance.to_array in
  let stateq, maskq = Array.fold_left_map (safe_quality_pattern_of_quality ~loc evd qsubst) stateq q
  in
  let stateu, masku = Array.fold_left_map (fun stateu lvlold ->
      let lvlnew = Univ.Level.var_index @@ Univ.subst_univs_level_level usubst lvlold in
      Option.fold_right (update_invtblu1 ~loc ~alg:false evd lvlold) lvlnew stateu, lvlnew
    ) stateu u
  in
  (state, stateq, stateu), (maskq, masku)

let update_invtblqu ~loc evd (qsubst, usubst) (state, stateq, stateu : state) u : state * _ =
  let (q, u) = u |> UVars.QualUniv.to_quality_level in
  let stateq, maskq = safe_quality_pattern_of_quality ~loc evd qsubst stateq q in
  let stateu, masku =
      let lvlnew = Univ.Level.var_index @@ Univ.subst_univs_level_level usubst u in
      Option.fold_right (update_invtblu1 ~loc ~alg:false evd u) lvlnew stateu, lvlnew
  in
  (state, stateq, stateu), (maskq, masku)

let universe_level_subst_var_index usubst u =
  match Univ.Universe.level u with
    | None -> None
    | Some lvlold ->
        let lvl = Univ.subst_univs_level_level usubst lvlold in
        Option.map (fun lvl -> lvlold, lvl) @@ Univ.Level.var_index lvl

let safe_sort_pattern_of_sort ~loc evd (qsubst, usubst) (st, sq, su as state) s =
  let open Sorts in
  match s with
  | Type u ->
      begin match universe_level_subst_var_index usubst u with
      | None -> state, PSType None
      | Some (lvlold, lvl) ->
        (st, sq, update_invtblu1 ~loc ~alg:true evd lvlold lvl su), PSType (Some lvl)
      end
  | SProp -> state, PSSProp
  | Prop -> state, PSProp
  | Set -> state, PSSet
  | QSort (qold, u) ->
      let sq, bq =
        match Sorts.Quality.(var_index @@ subst_fn qsubst qold) with
        | Some q -> update_invtblq1 ~loc evd (Sorts.Quality.QVar qold) q sq, Some q
        | None -> sq, None
      in
      let su, ba =
        match universe_level_subst_var_index usubst u with
        | Some (lvlold, lvl) -> update_invtblu1 ~loc ~alg:true evd lvlold lvl su, Some lvl
        | None -> su, None
      in
      (st, sq, su), PSQSort (bq, ba)


let warn_irrelevant_pattern =
  CWarnings.create ~name:"irrelevant-pattern"
    (fun () -> Pp.(str "This subpattern is irrelevant and can never be matched against."))

let warn_eta_in_pattern =
  CWarnings.create ~name:"eta-in-pattern" Fun.id

let rec check_may_eta ~loc env evd t =
  match EConstr.kind evd (Reductionops.whd_all env evd t) with
  | Prod _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | Sort _ -> ()
  | Ind (ind, u) ->
      let specif = Inductive.lookup_mind_specif env ind in
      if not @@ Inductive.is_primitive_record specif then () else
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a primitive record type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | App (i, _) -> check_may_eta ~loc env evd i
  | _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a yet unknown type, which may be a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")

let test_may_eta ~loc env evd constr =
  let t = Retyping.get_type_of env evd constr in
  let () = check_may_eta ~loc env evd t in
  ()


let rec safe_pattern_of_constr_aux ~loc env evd usubst depth state t = Constr.kind t |> function
  | App (f, args) ->
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr ~loc env evd usubst depth) state args in
      state, (head, elims @ [PEApp pargs])
  | Case (ci, u, _, (ret, qu), _, c, brs) ->
      let state, mask = update_invtblu ~loc evd usubst state u in
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state c in
      let state, pret = safe_deep_pattern_of_constr ~loc env evd usubst depth state ret in
      let state, maskqu = update_invtblqu ~loc evd usubst state qu in
      let state, pbrs = Array.fold_left_map (safe_deep_pattern_of_constr ~loc env evd usubst depth) state brs in
      state, (head, elims @ [PECase (ci.ci_ind, mask, pret, maskqu, pbrs)])
  | Proj (p, _, c) ->
      let state, (head, elims) = safe_pattern_of_constr_aux ~loc env evd usubst depth state c in
      state, (head, elims @ [PEProj p])
  | _ ->
      let state, head = safe_head_pattern_of_constr ~loc env evd usubst depth state t in
      state, (head, [])

and safe_pattern_of_constr ~loc env evd usubst depth state t =
  begin match Retyping.relevance_of_term env evd (EConstr.of_constr t) with
  | Sorts.Irrelevant -> warn_irrelevant_pattern ?loc ()
  | Sorts.RelevanceVar _ -> () (* FIXME *)
  | Sorts.Relevant -> ()
  end;
  safe_pattern_of_constr_aux ~loc env evd usubst depth state t

and safe_head_pattern_of_constr ~loc env evd usubst depth state t = Constr.kind t |> function
  | Const (c, u) when Environ.is_symbol env c ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHSymbol (c, mask)
  | Rel i ->
    assert (i <= depth);
    state, PHRel i
  | Sort s ->
    let state, ps = safe_sort_pattern_of_sort ~loc evd usubst state s in
    state, PHSort ps
  | Ind (ind, u) ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHInd (ind, mask)
  | Construct (c, u) ->
    let state, mask = update_invtblu ~loc evd usubst state u in
    state, PHConstr (c, mask)
  | Int i -> state, PHInt i
  | Float f -> state, PHFloat f
  | Lambda _ ->
    let (ntys, b) = Term.decompose_lambda t in
    let tys = Array.rev_of_list ntys in
    let (state, env), ptys = Array.fold_left_map_i
      (fun i (state, env) (na, ty) ->
          let state, p = safe_arg_pattern_of_constr ~loc env evd usubst (depth+i) state ty in
          (state, Environ.push_rel (LocalAssum (na, ty)) env), p)
        (state, env) tys
    in
    let state, pbod = safe_arg_pattern_of_constr ~loc env evd usubst (depth + Array.length tys) state b in
    state, PHLambda (ptys, pbod)
  | Prod _ ->
    let (ntys, b) = Term.decompose_prod t in
    let tys = Array.rev_of_list ntys in
    let (state, env), ptys = Array.fold_left_map_i
      (fun i (state, env) (na, ty) ->
          let state, p = safe_arg_pattern_of_constr ~loc env evd usubst (depth+i) state ty in
          (state, Environ.push_rel (LocalAssum (na, ty)) env), p)
        (state, env) tys
    in
    let state, pbod = safe_arg_pattern_of_constr ~loc env evd usubst (depth + Array.length tys) state b in
    state, PHProd (ptys, pbod)
  | _ ->
    CErrors.user_err ?loc Pp.(str "Subterm not recognised as pattern: " ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr t))

and safe_arg_pattern_of_constr ~loc env evd usubst depth (st, stateq, stateu as state) t = Constr.kind t |> function
  | Evar (evk, inst) ->
    let EvarInfo evi = Evd.find evd evk in
    (match snd (Evd.evar_source evi) with
    | Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar id) ->
      let holei, st = update_invtbl ~loc env evd evk st in
      if not @@ is_rel_inst 1 inst then
        CErrors.user_err ?loc
          Pp.(str "In " ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr (of_kind (Evar (evk, inst))))
            ++ str ", variable "
            ++ Termops.pr_existential_key env evd evk
            ++ str" appears with a non-trivial instantiation.");
      if Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.length <> SList.length inst then
        CErrors.user_err ?loc Pp.(str "Pattern variable cannot access the whole context: "
                                  ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr t));
      (st, stateq, stateu), EHole holei
    | Evar_kinds.NamedHole _ -> CErrors.user_err ?loc Pp.(str "Named holes are not supported, you must use regular evars: "
                                                          ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr t))
    | _ ->
      if Option.is_empty @@ Evd.evar_ident evk evd then state, EHoleIgnored else
        CErrors.user_err ?loc Pp.(str "Named evar in unsupported context: "
                                  ++ Termops.Internal.print_constr_env env evd (EConstr.of_constr t))
    )
  | _ ->
    test_may_eta ~loc env evd (EConstr.of_constr t);
    let state, p = safe_pattern_of_constr ~loc env evd usubst depth state t in
    state, ERigid p

and safe_deep_pattern_of_constr ~loc env evd usubst depth state p = safe_arg_pattern_of_constr ~loc env evd usubst (depth + Array.length (fst p)) state (snd p)
