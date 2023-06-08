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
open Libnames
open Nameops
open Term
open Constr
open Context
open Vars
open Namegen
open Declarations
open Declareops
open Inductive
open Inductiveops
open Environ
open Reductionops
open Context.Rel.Declaration

(* useful for testing *)

(* let settype = EConstr.to_constr sigma (EConstr.mkSort EConstr.ESorts.set) in *)
(* let tm = it_mkProd_or_LetIn_name env settype ctor.cs_args in *)
(* Feedback.msg_debug (str "The args of contructor " ++ str eq_name ++ str " seem to be " ++ Constr.debug_print tm) ; *)

(* Some helpers, I imagine *)

let ident_hd env ids t na =
  let na = named_hd env (Evd.from_env env) (EConstr.of_constr t) na in
  next_name_away na ids
let named_hd env t na = Name (ident_hd env Id.Set.empty t na)
let name_assumption env = function
| LocalAssum (na,t) -> LocalAssum (map_annot (named_hd env t) na, t)
| LocalDef (na,c,t) -> LocalDef (map_annot (named_hd env c) na, c, t)

let mkLambda_or_LetIn_name env d b = mkLambda_or_LetIn (name_assumption env d) b
let mkProd_or_LetIn_name env d b = mkProd_or_LetIn (name_assumption env d) b
let mkLambda_name env (n,a,b) = mkLambda_or_LetIn_name env (LocalAssum (n,a)) b
let mkProd_name env (n,a,b) = mkProd_or_LetIn_name env (LocalAssum (n,a)) b

let set_names env_for_named_hd env_for_next_ident_away l =
  let ids = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env_for_next_ident_away)) in
  snd (List.fold_right (fun d (ids,l) ->
      let id = ident_hd env_for_named_hd ids (get_type d) (get_name d) in (Id.Set.add id ids, set_name (Name id) d :: l)) l (ids,[]))
let it_mkLambda_or_LetIn_name env b l = it_mkLambda_or_LetIn b (set_names env env l)
let it_mkProd_or_LetIn_name env b l = it_mkProd_or_LetIn b (set_names env env l)

let make_prod_dep dep env = if dep then mkProd_name env else mkProd
let make_name env s r =
  make_annot (Name (next_ident_away (Id.of_string s) (Id.Set.of_list (Termops.ids_of_rel_context (rel_context env))))) r

let next_name = function
  | Anonymous -> Anonymous
  | Name x    -> Name (next_ident_away x Id.Set.empty)

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

(* Fetching the observational primitives *)

let obseq_constant = ref None
let cast_constant = ref None

let fetch_observational_data () =
  let obseq_qualid = Libnames.qualid_of_ident (Names.Id.of_string "obseq") in
  let cast_qualid = Libnames.qualid_of_ident (Names.Id.of_string "cast") in
  try
    obseq_constant := Some (Nametab.locate_constant obseq_qualid) ;
    cast_constant := Some (Nametab.locate_constant cast_qualid) ;
  with
    Not_found -> user_err Pp.(str "The observational equality or the cast operator does not exist.\
                                   Did you forget to open the observational library?")

let make_obseq ty tm1 tm2 =
  match !obseq_constant with
  | None ->
     user_err Pp.(str "The observational equality does not exist.\
                       Did you forget to open the observational library?")
  | Some obseq ->
     let obseq = Constr.mkConst obseq in
     Constr.mkApp (obseq, [| ty ; tm1 ; tm2 |])

let make_cast ty1 ty2 eq tm =
  match !cast_constant with
  | None ->
     user_err Pp.(str "The cast operator does not exist.\
                       Did you forget to open the observational library?")
  | Some cast ->
     let cast = Constr.mkConst cast in
     Constr.mkApp (cast, [| ty1 ; ty2 ; eq ; tm |])

(* Building and declaring the observational equalities *)

let declare_observational_equality = ref (fun ~univs ~name c ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))

let declare_one_ctor_arg_obs_eq ~poly env sigma name decl (ctxt, ren, cnt) =
  match decl with
  | Context.Rel.Declaration.LocalAssum (na, ty) ->
     (* generating the term *)
     let ty = Context.Rel.Declaration.get_type decl in
     let sort = Retyping.get_sort_of env sigma (EConstr.of_constr ty) in
     let s = EConstr.mkSort sort in
     let s = EConstr.to_constr sigma s in
     (** TODO : error messages *)
     let ty1 = Vars.exliftn ren ty in
     let ty2 = Vars.exliftn (Esubst.el_liftn 1 ren) ty in
     let eq = make_obseq s ty1 ty2 in
     let tm = it_mkProd_or_LetIn_name env eq ctxt in

     (* declaring the term *)
     let name = Names.Id.of_string (name ^ string_of_int cnt) in
     Feedback.msg_debug (str "We are trying to declare " ++ Constr.debug_print tm) ;
     let uctx = Evd.evar_universe_context sigma in
     let uctx = UState.minimize uctx in
     let tm = UState.nf_universes uctx tm in
     (** TODO : is it really necessary to normalize universes every time? *)
     let univs = UState.univ_entry ~poly uctx in
     let _ = !declare_observational_equality ~univs ~name tm in

     (* preparing the next context *)
     let ctxt = (Context.Rel.Declaration.LocalAssum (na, ty1)) :: ctxt in
     let ctxt = (Context.Rel.Declaration.LocalAssum (na, ty1)) :: ctxt in
     (* let cast_term = make_cast (wk1 ty1) (wk1 ty2) (wk1 eq) (mkRel 1) in *)
     (* let ctxt = (mkletin cast_term) :: ctxt in *)
     let ren = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in
     (ctxt, ren, cnt + 1)
  | Context.Rel.Declaration.LocalDef (na, tm, ty) ->
     (ctxt, ren, cnt)

let declare_one_constructor_obs_eqs ~poly env sigma ctxt ctor ctor_name =
  let eq_name = "eq_" ^ Names.Id.to_string ctor_name ^ "_" in
  let (ren, dup_ctxt) = duplicate_context ctxt in
  let args = ctor.cs_args in

  let _ = Context.Rel.fold_outside (declare_one_ctor_arg_obs_eq ~poly env sigma eq_name) args
    ~init:(dup_ctxt, ren, 0) in
  ()

let declare_one_inductive_obs_eqs ind =
  let env = Global.env () in
  (* sigma contains the graph of global universes as well as an empty local universe context
     we update sigma with the local universe context of the inductive *)
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let (mib,mip) = Global.lookup_inductive (fst pind) in
  let poly = Declareops.inductive_is_polymorphic mib in
  (* u is the universe instance that maps universe variables in the inductive to universes in the evd *)
  let u = snd pind in

  (* params_ctxt is the parameter context of the mutual inductive (including letins) *)
  let param_ctxt = Inductive.inductive_paramdecls (mib,u) in
  let params = Context.Rel.instance_list mkRel 0 param_ctxt in
  (* indf is the inductive family with its parameters instanciated to the ones in params_ctxt *)
  let indf = Inductiveops.make_ind_family (pind, params) in
  let n_indx = Inductiveops.inductive_nrealargs env (fst pind) in
  let indx_ctxt, s = Inductiveops.get_arity env indf in

  (* the full context contains parameters AND indices (also called "real arguments") *)
  let full_ctxt = indx_ctxt @ param_ctxt in
  let full_params = Context.Rel.instance_list mkRel n_indx param_ctxt in
  (* full_indf is the same as indf, but weakened to the context full_ctxt *)
  let full_indf = Inductiveops.make_ind_family (pind, full_params) in

  let ctors = Inductiveops.get_constructors env full_indf in
  let ctors_names = mip.mind_consnames in
  for i = 0 to (Array.length ctors) - 1 do
    declare_one_constructor_obs_eqs ~poly env sigma full_ctxt ctors.(i) ctors_names.(i)
  done

let declare_inductive_obs_eqs kn =
  let mib = Global.lookup_mind kn in
  for i = 0 to Array.length mib.mind_packets - 1 do
    declare_one_inductive_obs_eqs (kn,i);
  done

let declare_inductive_casts kn =
  ()

let declare_inductive_rewrite_rules kn =
  ()

let warn_about_sections () =
  CWarnings.create ~name:"observational-in-section" ~category:"inductives"
         (fun msg -> hov 0 msg) (hov 0 (str "Observational inductives are not properly supported in sections yet"))

let declare_inductive_observational_data kn =
  let mib = Global.lookup_mind kn in
  fetch_observational_data ();
  if mib.mind_finite = Declarations.CoFinite then
    user_err Pp.(str "Observational coinductive types are not supported yet");
  if Context.Named.length mib.mind_hyps > 0 then
    warn_about_sections ();
  declare_inductive_obs_eqs kn;
  declare_inductive_casts kn;
  declare_inductive_rewrite_rules kn
