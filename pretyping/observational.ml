(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file generates terms for: *)
(* Observational equalities between inductive types *)
(* Index casting for indexed inductive types *)
(* Rewrite rules for cast on inductives *)
(* Rewrite rules for match on index casting *)

open Pp
open CErrors
open Util
open Names
open Term
open Constr
open Namegen
open Declarations
open Inductiveops
open Environ
open Context.Rel.Declaration

(* Useful for testing *)

(* let settype = EConstr.to_constr sigma (EConstr.mkSort EConstr.ESorts.set) in *)
(* let tm = it_mkProd_or_LetIn_name env settype ctor.cs_args in *)
(* Feedback.msg_debug (str "The args of contructor " ++ str eq_name ++ str " seem to be " ++ Constr.debug_print tm) ; *)

(* Making a term with context into a lambda/prod *)

let ident_hd env ids t na =
  let na = named_hd env (Evd.from_env env) (EConstr.of_constr t) na in
  next_name_away na ids

let set_names env_for_named_hd env_for_next_ident_away l =
  let ids = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env_for_next_ident_away)) in
  snd (List.fold_right (fun d (ids,l) ->
      let id = ident_hd env_for_named_hd ids (get_type d) (get_name d) in (Id.Set.add id ids, set_name (Name id) d :: l)) l (ids,[]))

let it_mkLambda_or_LetIn_name env b l = it_mkLambda_or_LetIn b (set_names env env l)
let it_mkProd_or_LetIn_name env b l = it_mkProd_or_LetIn b (set_names env env l)

(*let named_hd env t na = Name (ident_hd env Id.Set.empty t na)
let name_assumption env = function
| LocalAssum (na,t) -> LocalAssum (map_annot (named_hd env t) na, t)
| LocalDef (na,c,t) -> LocalDef (map_annot (named_hd env c) na, c, t)
*)
(*let mkLambda_or_LetIn_name env d b = mkLambda_or_LetIn (name_assumption env d) b
let mkProd_or_LetIn_name env d b = mkProd_or_LetIn (name_assumption env d) b
let mkLambda_name env (n,a,b) = mkLambda_or_LetIn_name env (LocalAssum (n,a)) b
let mkProd_name env (n,a,b) = mkProd_or_LetIn_name env (LocalAssum (n,a)) b*)

(*let make_prod_dep dep env = if dep then mkProd_name env else mkProd
let make_name env s r =
  make_annot (Name (next_ident_away (Id.of_string s) (Id.Set.of_list (Termops.ids_of_rel_context (rel_context env))))) r *)

let next_name = function
  | Anonymous -> Anonymous
  | Name x    -> Name (next_ident_away x Id.Set.empty)

let get_sort_of_in_context env sigma ctxt ty =
  let env = Environ.push_rel_context ctxt env in
  Retyping.get_sort_of env sigma ty

(* Duplicate all the entries in a context, and return a substitution from the duplicated context *)

let duplicate_context ctx =
  let aux = (fun decl (ren, nctx) ->
      let decl = Context.Rel.Declaration.map_constr (Vars.exliftn ren) decl in
      let d1 = Context.Rel.Declaration.map_name next_name decl in
      let d2 = Context.Rel.Declaration.map_name next_name decl in
      let ren = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in
      (ren, d1 :: d2 :: nctx))
  in
  Context.Rel.fold_outside aux ctx
    ~init:(Esubst.el_id, Context.Rel.empty)

(* instanciates a context with evars *)
let evar_ctxt ignored env sigma ctx =
  let rec reln sigma subst = function
    | Context.Rel.Declaration.LocalAssum (annot, ty) :: hyps ->
       let sigma, subst = reln sigma subst hyps in

       let ty = Vars.substl subst ty in
       let relevance = Some (annot.binder_relevance) in
       let src =
         if ignored then
           Some (None , Evar_kinds.InternalHole)
         else
           Some (None , Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar (Names.Id.of_string "_")))
       in
       let sigma, ev = Evarutil.new_evar ?src ?relevance env sigma (EConstr.of_constr ty) in
       let ev = EConstr.Unsafe.to_constr ev in
       sigma, (ev :: subst)
    | Context.Rel.Declaration.LocalDef (annot, tm, ty) :: hyps ->
       let sigma, subst = reln sigma subst hyps in
       let tm = Vars.substl subst tm in
       sigma, (tm :: subst)
    | [] -> sigma, subst
  in
  reln sigma [] ctx

(* relocation of evars into de Bruijn indices
   TODO: this is copy-pasted from vernac/comRewriteRule.ml
   maybe avoid code duplication by relocating it to pretyping/rewrite_rule.ml *)
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

(* Adding a universe level to an evar map that is greater than the sort s *)

let univ_level_sup env sigma s =
  let sigma, u1 = Evd.new_univ_level_variable Evd.univ_flexible sigma in
  let s1 =
    if EConstr.ESorts.is_sprop sigma s then
      s
    else if EConstr.ESorts.is_prop sigma s then
      user_err (Pp.str "Prop is not compatible with the observational mode. Use SProp instead.")
    else
      EConstr.ESorts.make (Sorts.mkType (Univ.Universe.make u1))
  in
  let sigma = Evd.set_leq_sort env sigma s s1 in
  sigma, s1, u1

(* Adding a universe level to an evar map that is strictly greater than the level u *)

let univ_level_next sigma u =
  let sigma, u1 = Evd.new_univ_level_variable Evd.univ_flexible sigma in
  let cstr = Univ.Constraints.singleton (u, Univ.Lt, u1) in
  let sigma = Evd.add_constraints sigma cstr in
  sigma, u1

(* Fetching the observational primitives
   For now, they are being fetched from the current file
   Eventually they should be fetched from the library *)

let obseq_constant = ref None
let cast_constant = ref None
let prop_cast_constant = ref None

let fetch_observational_data () =
  let obseq_qualid = Libnames.qualid_of_ident (Names.Id.of_string "obseq") in
  let cast_qualid = Libnames.qualid_of_ident (Names.Id.of_string "cast") in
  let prop_cast_qualid = Libnames.qualid_of_ident (Names.Id.of_string "cast_prop") in
  try
    obseq_constant := Some (Nametab.global_inductive obseq_qualid) ;
    cast_constant := Some (Nametab.locate_constant cast_qualid) ;
    prop_cast_constant := Some (Nametab.locate_constant prop_cast_qualid) ;
  with
    Not_found -> user_err Pp.(str "The observational equality or the cast operator does not exist.\
                                   Did you forget to open the observational library?")

(* Building an observational equality term *)
let make_obseq ?(is_sprop = false) sigma u ty tm1 tm2 =
  match !obseq_constant with
  | None -> user_err Pp.(str "The observational equality does not exist.")
  | Some obseq ->
     let ty = if is_sprop then EConstr.(to_constr sigma (mkSort (ESorts.make Sorts.sprop))) else ty in
     let obseq_fam = Inductiveops.make_ind_family ((obseq, UVars.Instance.of_array ([| |], [| u |])), [ty ; tm1]) in
     let obseq_tm = Inductiveops.mkAppliedInd (Inductiveops.make_ind_type (obseq_fam, [EConstr.of_constr tm2])) in
     EConstr.to_constr sigma obseq_tm

(* Building a cast term *)
let make_cast ?(is_sprop = false) u1 u2 ty1 ty2 eq tm =
  if is_sprop then
    match !prop_cast_constant with
    | None -> user_err Pp.(str "The propositional cast operator does not exist.")
    | Some cast ->
       let cast = Constr.mkConstU (cast, UVars.Instance.of_array ([| |], [| u2 |])) in
       Constr.mkApp (cast, [| ty1 ; ty2 ; eq ; tm |])
  else
    match !cast_constant with
    | None -> user_err Pp.(str "The cast operator does not exist.")
    | Some cast ->
       let cast = Constr.mkConstU (cast, UVars.Instance.of_array ([| |], [| u1 ; u2 |])) in
       Constr.mkApp (cast, [| ty1 ; ty2 ; eq ; tm |])

(* Building a rewrite rule *)
let make_rewrite_rule ?loc env sigma uinst u1 u2 ty lhs rhs =
  (* at this point there are two kinds of universes:
     - the ones that come from the instance of the inductive (if polymorphic), call them v1 v2...
     - the ones that we added, u1 and u2
     In all cases, rewrite rules for constructors will be of the form

       cast@{u1 u2} (Ind@{v1 v2...} ?A) (Ind@{v1 v2...} ?A0) ?e (ctor@{v1 v2...} ?A ?t)
         ==> ctor@{v1 v2...} ?A0 (cast@{u1 u2} B@{A := ?A} B@{A := ?A0} (ax ?e) ?t)

     Note that some levels appear several times, which should imply level equations--otherwise,
     universe polymorphic inductives will break SR
  *)
  let cast_uinst = UVars.Instance.of_array ([| |], [| u1 ; u2 |]) in
  let uinst = UVars.Instance.append uinst cast_uinst in
  let usubst = UVars.make_instance_subst uinst in
  let ((nvars', invtbl), (nvarqs', invtblq), (nvarus', alg_vars, invtblu)), (head_pat, elims) =
    Rewrite_rule.safe_pattern_of_constr ~loc:loc env sigma usubst 0
      ((1, Evar.Map.empty), (0, Int.Map.empty), (0, [], Int.Map.empty)) lhs
  in
  let update_invtbl evd evk n invtbl =
    let Evd.EvarInfo evi = Evd.find evd evk in
    let vars = Evd.evar_hyps evi |> Environ.named_context_of_val |> Context.Named.instance EConstr.mkVar in
    Evar.Map.add evk (n, vars) invtbl
  in
  let invtbl = Evar.Map.fold (update_invtbl sigma) invtbl Evar.Map.empty in
  let rhs =
    let rhs' = evar_subst invtbl sigma 0 rhs in
    match EConstr.to_constr_opt sigma rhs' with
    | Some rhs -> rhs
    | None ->
       CErrors.user_err ?loc Pp.(str "The right side of the rewrite rule contains unresolved evars: "
                                 ++ Constr.debug_print (EConstr.Unsafe.to_constr rhs))
  in
  let rhs = Vars.subst_univs_level_constr usubst rhs in
  let head_symbol, head_umask = match head_pat with PHSymbol (symb, mask) -> symb, mask | _ ->
    CErrors.user_err ?loc
    Pp.(str "Cast is not recognised as a head-pattern.")
  in
  head_symbol, { nvars = (nvars' - 1, nvarqs', nvarus'); lhs_pat = head_umask, elims; rhs }

(* Building and declaring the observational equalities *)
let declare_observational_equality = ref (fun ~univs ~name c ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))

let declare_observational_rewrite = ref (fun ~univs ~name c d ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))

let wk1_tm = Vars.exliftn (Esubst.el_shft 1 (Esubst.el_id))

let wkn n sigma = (Esubst.el_shft n (Esubst.el_liftn n sigma))

(* weaken an entire context, lifting the substitution every time *)
let wk1_context ctxt =
  let aux = fun decl (ren, ctxt) ->
    let decl = Context.Rel.Declaration.map_constr (Vars.exliftn ren) decl in
    let wk = Esubst.el_lift ren in
    (wk, decl::ctxt)
  in
  let _, ctxt = Context.Rel.fold_outside aux ctxt
                  ~init:(wkn 1 (Esubst.el_id), Context.Rel.empty) in
  ctxt

let declare_one_ctor_arg_obs_eq ~poly env uinfo name decl (sigma, ctxt, ren1, ren2, cnt) =
  match decl with
  | Context.Rel.Declaration.LocalAssum (na, ty) ->
     let (param_ctxt, arg_ctxt, arg0_ctxt) = ctxt in
     let full_ctxt = arg0_ctxt @ (arg_ctxt @ param_ctxt) in
     let n_args = List.length arg_ctxt in
     (* generating the type of the observational equality *)
     let ty = Context.Rel.Declaration.get_type decl in
     let ty1 = Vars.exliftn (wkn n_args (Esubst.el_liftn n_args ren1)) ty in
     let ty2 = Vars.exliftn (Esubst.el_liftn n_args (wkn n_args ren2)) ty in
     let sort = get_sort_of_in_context env sigma full_ctxt (EConstr.of_constr ty1) in
     let is_sprop = EConstr.ESorts.is_sprop sigma sort in
     (* we declare new universe levels u1 and u2 to instanciate the polymorphic obseq constant *)
     (* let sigma, newsort, u1 = univ_level_sup env sigma sort in *)
     (* let sigma, u2 = univ_level_next sigma u1 in *)
     (* let s = EConstr.mkSort newsort in *)
     (* let s = EConstr.to_constr sigma s in *)

     (* TODO: Instead of using the universe level of the constructor argument type, I lazily reuse
        the levels from the inductive type family. I think that cumulativity guarantees it's okay *)
     let u1, u2, s = uinfo in
     let eq_ty = make_obseq ~is_sprop sigma u2 s ty1 ty2 in
     let axiom = it_mkProd_or_LetIn_name env eq_ty full_ctxt in
     let name = Names.Id.of_string (name ^ string_of_int cnt) in

     (* optional debug *)
     Feedback.msg_debug (str "Observational inductives: Declaring parameter "
                         ++ str (Names.Id.to_string name)
                         ++ str " whose type is "
                         ++ Termops.Internal.print_constr_env env sigma (EConstr.of_constr axiom)) ;

     (* normalizing the universes in the evar map and in the body of the axiom *)
     let uctx = Evd.evar_universe_context sigma in
     let uctx = UState.minimize uctx in
     let axiom = UState.nf_universes uctx axiom in
     (* declaring the axiom with its local universe context *)
     let univs = UState.univ_entry ~poly uctx in
     let eq_name = !declare_observational_equality ~univs ~name axiom in

     (* generating the instance of the equality axiom that we will use in make_cast *)
     (* TODO: should I really be manipulating universes like that without an abstract interface? *)
     let eq_tm = match fst univs with
       | UState.Polymorphic_entry uc -> Constr.mkConstU (eq_name, UVars.UContext.instance uc)
       | UState.Monomorphic_entry pe -> Constr.mkConstU (eq_name, UVars.Instance.empty)
     in
     let eq_args = Context.Rel.instance mkRel 0 full_ctxt in
     let eq_hyp = Constr.mkApp (eq_tm, eq_args) in

     (* preparing the context for the next axiom *)
     let newty = Vars.exliftn (Esubst.el_liftn n_args ren1) ty in
     let arg_ctxt = (Context.Rel.Declaration.LocalAssum (na, newty)) :: arg_ctxt in
     (* since we added a term in arg_ctxt, we must weaken everything in arg0_ctxt *)
     let arg0_ctxt = wk1_context arg0_ctxt in
     (* then we add the new cast term to arg0_ctxt *)
     let ty1 = Vars.exliftn (wkn (n_args + 1) (Esubst.el_liftn n_args ren1)) ty in
     let ty2 = Vars.exliftn (Esubst.el_liftn n_args (wkn (n_args + 1) ren2)) ty in
     let cast_term = make_cast ~is_sprop u1 u2 ty1 ty2 (wk1_tm eq_hyp) (mkRel (n_args + 1)) in
     let arg0_ctxt = (Context.Rel.Declaration.LocalDef (na, cast_term, ty2)) :: arg0_ctxt in
     (sigma, (param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, cnt + 1)
  | Context.Rel.Declaration.LocalDef (na, tm, ty) as decl ->
     let (param_ctxt, arg_ctxt, arg0_ctxt) = ctxt in
     (* let full_ctxt = arg0_ctxt @ (arg_ctxt @ param_ctxt) in *)
     let n_args = List.length arg_ctxt in
     (* we simply make two copies of the letin, with the correct renamings *)
     let new_ren1 = (wkn n_args (Esubst.el_liftn n_args ren1)) in
     let decl1 = Context.Rel.Declaration.map_constr (Vars.exliftn new_ren1) decl in
     let arg_ctxt = decl1::arg_ctxt in
     let arg0_ctxt = wk1_context arg0_ctxt in
     let new_ren2 = (Esubst.el_liftn n_args (wkn (n_args + 1) ren2)) in
     let decl2 = Context.Rel.Declaration.map_constr (Vars.exliftn new_ren2) decl in
     let arg0_ctxt = decl2::arg0_ctxt in
     (sigma, (param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, cnt)

let declare_one_constructor_obs_eqs ?loc ~poly env sigma ctxt ind ctor ctor_name =
  (* preparing the context of hypotheses for the axioms *)
  let (ren, dup_ctxt) = duplicate_context ctxt in
  (* extending it with the equality between two instances of the inductive *)
  let (indty, s, u1, u2) = ind in
  let indty1 = Vars.exliftn ren indty in
  let indty2 = Vars.exliftn (Esubst.el_liftn 1 ren) indty in
  let eq_hyp = make_obseq sigma u2 s indty1 indty2 in
  let eq_annot = Context.make_annot (Names.Name.mk_name (Names.Id.of_string "e")) Sorts.Irrelevant in
  let hyp_ctxt = (Context.Rel.Declaration.LocalAssum (eq_annot, eq_hyp))::dup_ctxt in

  let eq_name = "obseq_" ^ Names.Id.to_string ctor_name ^ "_" in
  let args = ctor.cs_args in
  let ren1 = Esubst.el_shft 1 (Esubst.el_liftn 1 ren) in
  let ren2 = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in

  let uinfo = (u1, u2, s) in

  let new_ctxt = Context.Rel.fold_outside (declare_one_ctor_arg_obs_eq ~poly env uinfo eq_name) args
    ~init:(sigma, (hyp_ctxt, Context.Rel.empty, Context.Rel.empty), ren1, ren2, 0) in
  new_ctxt

let declare_one_constructor_rew_rules ?loc ~poly env uinst state ind ctor ctor_name =
  let sigma, (param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, _ = state in
  let n_args = List.length arg_ctxt in

  let (indty, s, u1, u2) = ind in
  let indty1 = Vars.exliftn (wkn n_args ren1) indty in
  let indty2 = Vars.exliftn (wkn n_args ren2) indty in
  let eq_hyp = mkRel (List.length arg_ctxt + 1) in

  let inst_ctor = Inductiveops.build_dependent_constructor ctor in
  let inst_ctor_1 = Vars.exliftn (Esubst.el_liftn n_args ren1) inst_ctor in
  let inst_ctor_2 = Vars.exliftn (Esubst.el_liftn n_args (wkn n_args ren2)) inst_ctor in

  (* We build evar instances of the context. esubst is made of MatchingVar's for normal holes,
     esubst_ignored is made of InternalHole's for ignored holes. *)
  let sigma, esubst = evar_ctxt false env sigma (arg_ctxt @ param_ctxt) in
  let sigma, esubst_ignored = evar_ctxt true env sigma (arg_ctxt @ param_ctxt) in

  (* the parameters in indty1 are subsumed by the parameters in inst_ctor_1, so we make them
     InternalHole's to avoid unnecessary equations. TODO: is it fine for indices? *)
  let indty1 = Vars.substl esubst_ignored indty1 in
  let rew_left = make_cast u1 u2 indty1 indty2 eq_hyp inst_ctor_1 in
  let rew_left = Vars.substl esubst rew_left in
  let rew_left = EConstr.of_constr rew_left in

  let rew_right = it_mkLambda_or_LetIn_name env inst_ctor_2 arg0_ctxt in
  let rew_right = Vars.substl esubst rew_right in
  let rew_right = EConstr.of_constr rew_right in

  let id = Names.Id.of_string ("rewrite_" ^ Names.Id.to_string ctor_name) in

  (* optional debug *)
  Feedback.msg_debug (strbrk "We are trying to declare the rewrite rule "
                      ++ Termops.Internal.print_constr_env env sigma rew_left
                      ++ fnl ()
                      ++ str " ==> "
                      ++ Termops.Internal.print_constr_env env sigma rew_right) ;

  let ty_left = Retyping.get_type_of env sigma rew_left in
  Feedback.msg_debug (str "The left side has type "
                      ++ Termops.Internal.print_constr_env env sigma ty_left) ;
  let ty_right = Retyping.get_type_of env sigma rew_right in
  Feedback.msg_debug (str "The right side has type "
                      ++ Termops.Internal.print_constr_env env sigma ty_right) ;

  let rew = make_rewrite_rule ?loc env sigma uinst u1 u2 indty2 (EConstr.Unsafe.to_constr rew_left) rew_right in
  Global.add_rewrite_rules id { rewrules_rules = [rew] }

let declare_one_inductive_obs_eqs ?loc ind =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* sigma contains the graph of global universes as well as an empty local universe context *)
  (* we update sigma with the local universes of the inductive (which is empty if ind is monomorphic) *)
  (* pind is the name of the inductive decorated with a universe instance,
     which maps universe variables in the inductive to universes in sigma *)
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let (mib,mip) = Global.lookup_inductive (fst pind) in
  let poly = Declareops.inductive_is_polymorphic mib in
  match mip.mind_relevance with
  | Sorts.Relevant ->
     (* u is the univ instance for the inductive *)
     let u = snd pind in
     (* params_ctxt is the parameter context of the inductive (including letins) *)
     let param_ctxt = Inductive.inductive_paramdecls (mib,u) in
     let param_instance = Context.Rel.instance_list mkRel 0 param_ctxt in
     (* ind_fam is the inductive family with its parameters instanciated to the ones in params_ctxt *)
     let ind_fam = Inductiveops.make_ind_family (pind, param_instance) in
     let n_indx = Inductiveops.inductive_nrealargs env (fst pind) in
     (* indx_ctxt is the telescope of indices, instanciated in param_ctxt *)
     let indx_ctxt = Inductiveops.get_arity env ind_fam in

     (* the full context contains parameters AND indices (also called "real arguments") *)
     let full_ctxt = indx_ctxt @ param_ctxt in
     let full_param_instance = Context.Rel.instance_list mkRel n_indx param_ctxt in
     (* full_ind_fam is the same as ind_fam, but weakened to the context full_ctxt *)
     let full_ind_fam = Inductiveops.make_ind_family (pind, full_param_instance) in

     (* instanciating the inductive type in the full context *)
     let indx_instance = Context.Rel.instance_list EConstr.mkRel 0 indx_ctxt in
     let ind_ty = Inductiveops.mkAppliedInd (Inductiveops.make_ind_type (full_ind_fam, indx_instance)) in
     (* we use retyping to find the sort of the inductive type in its context of parameters
        The sort might be algebraic, so we add two new levels to the evar_map:
        one for the inductive type (>= its sort), and one strictly above *)
     let sort = get_sort_of_in_context env sigma full_ctxt ind_ty in
     let sigma, newsort, u1 = univ_level_sup env sigma sort in
     let sigma, u2 = univ_level_next sigma u1 in
     let s = EConstr.mkSort newsort in
     let s = EConstr.to_constr sigma s in
     let instanciated_ind = (EConstr.to_constr sigma ind_ty, s, u1, u2) in

     (* declaring the observational equality axioms for every constructor *)
     let ctors = Inductiveops.get_constructors env full_ind_fam in
     let ctors_names = mip.mind_consnames in
     for i = 0 to (Array.length ctors) - 1 do
       let state = declare_one_constructor_obs_eqs ?loc ~poly env sigma full_ctxt instanciated_ind ctors.(i) ctors_names.(i) in
       declare_one_constructor_rew_rules ?loc ~poly env u state instanciated_ind ctors.(i) ctors_names.(i)
     done
  | _ -> ()


let warn_about_sections () =
  CWarnings.create ~name:"observational-in-section"
    (fun msg -> hov 0 msg) (hov 0 (str "Observational inductives do not properly support the sections mechanism yet. \
                                        You might get rules that are weaker than you expect outside of the section."))

let declare_inductive_observational_data ?loc (kn,i) =
  let mib = Global.lookup_mind kn in
  (* check that all options are set correctly *)
  if mib.mind_finite = Declarations.CoFinite then
    user_err Pp.(str "Observational coinductive types are not supported yet.");
  if Context.Named.length mib.mind_hyps > 0 then
    warn_about_sections ();
  (* generate stuff *)
  fetch_observational_data ();
  declare_one_inductive_obs_eqs ?loc (kn,i);
