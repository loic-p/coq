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

let maybe_error_many_udecls = function
| ({CAst.loc;v=id}, Some _) ->
  CErrors.user_err ?loc
    Pp.(strbrk "When declaring multiple symbols in one command, " ++
        strbrk "only the first is allowed a universe binder " ++
        strbrk "(which will be shared by the whole block).")
| (_, None) -> ()

let preprocess_symbols l =
  let open Vernacexpr in
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a symbol is not allowed in sections.");
  let udecl = match l with
    | (coe, ((id, udecl)::rest, c))::rest' ->
      List.iter maybe_error_many_udecls rest;
      List.iter (fun (coe, (idl, c)) -> List.iter maybe_error_many_udecls idl) rest';
      udecl
    | (_, ([], _))::_ | [] -> assert false
  in
  let no_coercion_msg = Pp.(str "Cannot deal with coercions in symbols") in
  List.iter (function AddCoercion, (({CAst.loc; _}, _) :: _, _) -> CErrors.user_err ?loc no_coercion_msg | AddCoercion, _ -> assert false | _ -> ()) l;
  udecl, List.concat_map (fun (coe, (idl, c)) -> List.map (fun (id, _) -> id, c) idl) l

let do_symbol ~poly ~unfold_fix udecl (id, typ) =
  if Dumpglob.dump () then Dumpglob.dump_definition id false "symb";
  let id = id.CAst.v in
  let env = Global.env () in
  let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in
  let evd, (typ, impls) =
    Constrintern.(interp_type_evars_impls ~impls:empty_internalization_env)
      env evd typ
  in
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd typ in
  let evd = Evd.restrict_universe_context evd uvars in
  let typ = EConstr.to_constr evd typ in
  let univs = Evd.check_univ_decl ~poly evd udecl in
  let entry = Declare.symbol_entry ~univs ~unfold_fix typ in
  let kn = Declare.declare_constant ~name:id ~kind:Decls.IsSymbol (Declare.SymbolEntry entry) in
  let () = Impargs.maybe_declare_manual_implicits false (GlobRef.ConstRef kn) impls in
  let () = Declare.assumption_message id in
  ()

let do_symbols ~poly ~unfold_fix l =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Symb);
  let udecl, l = preprocess_symbols l in
  List.iter (do_symbol ~poly ~unfold_fix udecl) l



open Util
open Constr
open Declarations

let warn_irrelevant_pattern =
  CWarnings.create ~name:"irrelevant-pattern"
    (fun () -> Pp.(str "This subpattern is irrelevant and can never be matched against."))

let warn_eta_in_pattern =
  CWarnings.create ~name:"eta-in-pattern" Fun.id

let warn_redex_in_rewrite_rules =
  CWarnings.create ~name:"redex-in-rewrite-rules"
  (fun redex -> Pp.(str "This pattern contains a" ++ redex ++ str " which may prevent this rule from being triggered."))


(* relocation of evars into de Bruijn indices *)
let rec evar_subst evmap evd k t =
  match EConstr.kind evd t with
  | Evar (evk, inst) -> begin
    match Evar.Map.find_opt evk evmap with
    | None -> t
    | Some (n, vars) ->
        let head = EConstr.mkRel (n + k) in
        let Evd.EvarInfo evi = Evd.find evd evk in
        let body = EConstr.mkApp (head, vars) in
        let inst = inst |> SList.Smart.map (evar_subst evmap evd k) in
        Evd.instantiate_evar_array evd evi body inst
    end
  | _ -> EConstr.map_with_binders evd succ (evar_subst evmap evd) k t

let test_projection_apps env evd ~loc ind args =
  let specif = Inductive.lookup_mind_specif env ind in
  if not @@ Inductive.is_primitive_record specif then () else
  if Array.for_all_i (fun i arg ->
    match arg with
    | EHole _ | EHoleIgnored -> true
    | ERigid (_, []) -> false
    | ERigid (_, elims) ->
      match List.last elims with
      | PEProj p -> Ind.CanOrd.equal (Projection.inductive p) ind && Projection.arg p = i
      | _ -> false
  ) 0 args then
    warn_redex_in_rewrite_rules ?loc Pp.(str " subpattern compatible with an eta-long form for " ++ Id.print (snd specif).mind_typename ++ str"," )

let rec test_pattern_redex env evd ~loc = function
  | PHLambda _, PEApp _ :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " beta redex")
  | PHConstr _, (PECase _ | PEProj _) :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " iota redex")
  | PHConstr _, PEApp _ :: (PECase _ | PEProj _) :: _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " iota redex")
  | PHLambda _, _ -> warn_redex_in_rewrite_rules ?loc (Pp.str " lambda pattern")
  | PHConstr (c, _) as head, PEApp args :: elims -> test_projection_apps env evd ~loc (fst c) args; Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PEApp args :: elims -> Array.iter (test_pattern_redex_aux env evd ~loc) args; test_pattern_redex env evd ~loc (head, elims)
  | head, PECase (_, _, ret, _, brs) :: elims -> test_pattern_redex_aux env evd ~loc ret; Array.iter (test_pattern_redex_aux env evd ~loc) brs; test_pattern_redex env evd ~loc (head, elims)
  | head, PEProj _ :: elims -> test_pattern_redex env evd ~loc (head, elims)
  | PHProd (tys, bod), [] -> Array.iter (test_pattern_redex_aux env evd ~loc) tys; test_pattern_redex_aux env evd ~loc bod
  | (PHRel _ | PHInt _ | PHFloat _ | PHSort _ | PHInd _ | PHConstr _ | PHSymbol _), [] -> ()
and test_pattern_redex_aux env evd ~loc = function
  | EHole _ | EHoleIgnored -> ()
  | ERigid p -> test_pattern_redex env evd ~loc p


let warn_rewrite_rules_break_SR = "rewrite-rules-break-SR"

let rewrite_rules_break_SR_warning =
  CWarnings.create_warning ~name:warn_rewrite_rules_break_SR ~default:CWarnings.Enabled ()

let rewrite_rules_break_SR_msg = CWarnings.create_msg rewrite_rules_break_SR_warning ()
let warn_rewrite_rules_break_SR ~loc reason =
  CWarnings.warn rewrite_rules_break_SR_msg ?loc reason
let () = CWarnings.register_printer rewrite_rules_break_SR_msg
  (fun reason -> Pp.(str "This rewrite rule breaks subject reduction (" ++ reason ++ str ")."))

let interp_rule (udecl, eqs, lhs, rhs: Constrexpr.universe_decl_expr option * _ * _ * _) =
  let env = Global.env () in
  let evd = Evd.from_env env in

  (* 1. Read universe level binders, leaving out the constraints for now *)
  (* Inlined the relevant part of Constrintern.interp_univ_decl *)
  let evd, udecl =
    let open CAst in let open UState in
    match udecl with
    | None -> evd, default_univ_decl
    | Some udecl ->
    let evd, qualities = List.fold_left_map (fun evd lid ->
        Evd.new_quality_variable ?loc:lid.loc ~name:lid.v evd)
        evd
        udecl.univdecl_qualities
    in
    let evd, instance = List.fold_left_map (fun evd lid ->
        Evd.new_univ_level_variable ?loc:lid.loc univ_rigid ~name:lid.v evd)
        evd
        udecl.univdecl_instance
    in
    let cstrs =
      udecl.univdecl_constraints |> List.to_seq
      |> Seq.map (Constrintern.interp_univ_constraint evd)
      |> Univ.Constraints.of_seq
    in
    let decl = {
      univdecl_qualities = qualities;
      univdecl_instance = instance;
      univdecl_extensible_instance = udecl.univdecl_extensible_instance;
      univdecl_constraints = cstrs;
      univdecl_extensible_constraints = udecl.univdecl_extensible_constraints;
    } in
    evd, decl
  in
  let nvarqs = List.length udecl.univdecl_qualities in
  let nvarus = List.length udecl.univdecl_instance in


  (* 2. Read left hand side, into a pattern *)
  (* The udecl constraints must be implied by the lhs (and not the reverse) *)

  let lhs_loc = lhs.CAst.loc in
  let rhs_loc = rhs.CAst.loc in

  let lhs = Constrintern.(intern_gen WithoutTypeConstraint env evd lhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with undeclared_evars_patvars = true; patvars_abstract = true; expand_evars = false; solve_unification_constraints = false } in
  let evd, lhs, typ = Pretyping.understand_tcc_ty ~flags env evd lhs in

  let evd = Evd.minimize_universes evd in
  let _qvars, uvars = EConstr.universes_of_constr evd lhs in
  let evd = Evd.restrict_universe_context evd uvars in
  let uctx, uctx' = UState.check_univ_decl_rev (Evd.evar_universe_context evd) udecl in

  let usubst =
    let inst, auctx = UVars.abstract_universes uctx' in
    UVars.make_instance_subst inst
  in

  let ((nvars', invtbl), (nvarqs', invtblq), (nvarus', invtblu)), (head_pat, elims) =
    Rewrite_rule.safe_pattern_of_constr ~loc:lhs_loc env evd usubst 0 ((1, Evar.Map.empty), (0, Int.Map.empty), (0, Int.Map.empty)) (EConstr.Unsafe.to_constr lhs)
  in
  let () = test_pattern_redex env evd ~loc:lhs_loc (head_pat, elims) in

  let head_symbol, head_umask = match head_pat with PHSymbol (symb, mask) -> symb, mask | _ ->
    CErrors.user_err ?loc:lhs_loc
    Pp.(str "Head head-pattern is not a symbol.")
  in
  if nvarus <> nvarus' then begin
    assert (nvarus' < nvarus);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all universe level variables appear in the pattern.")
  end;
  if nvarqs <> nvarqs' then begin
    assert (nvarqs' < nvarqs);
    CErrors.user_err ?loc:lhs_loc
      Pp.(str "Not all sort variables appear in the pattern.")
  end;

  let update_invtbl evd evk n =
    let Evd.EvarInfo evi = Evd.find evd evk in
    let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
    (n, vars)
  in

  let invtbl = Evar.Map.mapi (update_invtbl evd) invtbl in

  (* 3. Read right hand side *)
  (* The udecl constraints (or, if none, the lhs constraints) must imply those of the rhs *)
  let evd = Evd.set_universe_context evd uctx in
  let rhs = Constrintern.(intern_gen WithoutTypeConstraint env evd rhs) in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with patvars_abstract = true } in
  let evd', rhs =
    try Pretyping.understand_tcc ~flags env evd ~expected_type:(OfType typ) rhs
    with Type_errors.TypeError _ | Pretype_errors.PretypeError _ ->
      warn_rewrite_rules_break_SR ~loc:rhs_loc (Pp.str "the replacement term doesn't have the type of the pattern");
      Pretyping.understand_tcc ~flags env evd rhs
  in

  let evd', eqs = List.fold_left_map (fun evd (a, b) ->
    let a_loc = a.CAst.loc in
    let b_loc = b.CAst.loc in
    let a = Constrintern.(intern_gen WithoutTypeConstraint env evd a) in
    let evd, a, ty = Pretyping.understand_tcc_ty ~flags env evd a in
    let b = Constrintern.(intern_gen WithoutTypeConstraint env evd b) in
    let evd, b =
      try Pretyping.understand_tcc ~flags env evd ~expected_type:(OfType typ) b
      with Type_errors.TypeError _ | Pretype_errors.PretypeError _ ->
        warn_rewrite_rules_break_SR ~loc:b_loc (Pp.str "the equation rhs term doesn't have the type of its lhs");
        Pretyping.understand_tcc ~flags env evd b
    in
    evd, (a, a_loc, b, b_loc)) evd' eqs
  in

  let evd' = Evd.minimize_universes evd' in
  let _qvars', uvars' = EConstr.universes_of_constr evd' rhs in
  let evd' = Evd.restrict_universe_context evd' (Univ.Level.Set.union uvars uvars') in
  let fail pp = warn_rewrite_rules_break_SR ~loc:rhs_loc Pp.(str "universe inconsistency, missing constraints: " ++ pp) in
  let () = UState.check_uctx_impl ~fail (Evd.evar_universe_context evd) (Evd.evar_universe_context evd') in
  let evd = evd' in

  let final_checks rhs_loc rhs =
    let rhs =
      let rhs' = evar_subst invtbl evd 0 rhs in
      match EConstr.to_constr_opt evd rhs' with
      | Some rhs -> rhs
      | None ->
        let pr_unresolved_evar e =
          Pp.(hov 2 (str"- " ++ Printer.pr_existential_key env evd e ++  str ": " ++
            Himsg.explain_pretype_error env evd (Pretype_errors.UnsolvableImplicit (e,None))))
        in
        CErrors.user_err ?loc:rhs_loc Pp.(hov 0 begin
          str "The replacement term contains unresolved implicit arguments:"++ fnl () ++
          str "  " ++ Printer.pr_econstr_env env evd rhs ++ fnl () ++
          str "More precisely: " ++ fnl () ++
          v 0 (prlist_with_sep cut pr_unresolved_evar (Evar.Set.elements (Evarutil.undefined_evars_of_term evd rhs')))
        end)
    in

    let rhs = Vars.subst_univs_level_constr usubst rhs in

    let test_qvar q =
      match Sorts.QVar.var_index q with
      | Some -1 ->
          CErrors.user_err ?loc:rhs_loc
            Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears in the replacement but does not appear in the pattern.")
      | Some n when n < 0 || n > nvarqs' -> CErrors.anomaly Pp.(str "Unknown sort variable in rewrite rule.")
      | Some _ -> ()
      | None ->
          if not @@ Sorts.QVar.Set.mem q (evd |> Evd.sort_context_set |> fst |> fst) then
            CErrors.user_err ?loc:rhs_loc
              Pp.(str "Sort variable " ++ Termops.pr_evd_qvar evd q ++ str " appears in the replacement but does not appear in the pattern.")
    in

    let test_level ?(alg_ok=false) lvl =
      match Univ.Level.var_index lvl with
      | Some -1 ->
          CErrors.user_err ?loc:rhs_loc
            Pp.(str "Universe level variable " ++ Termops.pr_evd_level evd lvl ++ str " appears in the replacement but does not appear in the pattern.")
      | Some n when n < 0 || n > nvarus' -> CErrors.anomaly Pp.(str "Unknown universe level variable in rewrite rule")
      | Some _ -> ()
      | None ->
          try UGraph.check_declared_universes (Environ.universes env) (Univ.Level.Set.singleton lvl)
          with UGraph.UndeclaredLevel lvl ->
            CErrors.user_err ?loc:rhs_loc
              Pp.(str "Universe level " ++ Termops.pr_evd_level evd lvl ++ str " appears in the replacement but does not appear in the pattern.")
    in

    let () =
      let qs, us = Vars.sort_and_universes_of_constr rhs in
      Sorts.QVar.Set.iter test_qvar qs;
      Univ.Level.Set.iter test_level us
    in
    rhs
  in
  let rhs = final_checks rhs_loc rhs in

  let equalities = List.map (fun (a, a_loc, b, b_loc) -> final_checks a_loc a, final_checks b_loc b) eqs in

  head_symbol, { nvars = (nvars' - 1, nvarqs', nvarus'); lhs_pat = head_umask, elims; equalities; rhs }

let do_rules id rules =
  let env = Global.env () in
  if not @@ Environ.rewrite_rules_allowed env then raise Environ.(RewriteRulesNotAllowed Rule);
  let body = { rewrules_rules = List.map interp_rule rules } in
  Global.add_rewrite_rules id body
