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

let duplicate_context ctx =
  let aux = (fun decl (ren, nctx) ->
      let decl = Context.Rel.Declaration.map_constr (Vars.exliftn ren) decl in
      let d1 = Context.Rel.Declaration.map_name next_name decl in
      let d2 = Context.Rel.Declaration.map_name next_name decl in
      let ren = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in
      (ren, d1 :: d2 :: nctx))
  in
  let (_, nctx) = Context.Rel.fold_outside aux ctx
    ~init:(Esubst.el_id, Context.Rel.empty)
  in nctx

let declare_one_inductive_obs_eqs ind =
  let env = Global.env () in
  (* sigma contains the graph of global universes as well as an empty local universe context
     we update sigma with the local universe context of the inductive *)
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in

  let (mib,mip) = Global.lookup_inductive (fst pind) in
  (* sans doute qu'il faut substituer (snd pind) qqpart *)

  let dctx = duplicate_context mib.mind_params_ctxt in

  let settype = EConstr.mkSort EConstr.ESorts.set in
  let temp = it_mkProd_or_LetIn_name env (EConstr.Unsafe.to_constr settype) dctx in
  Feedback.msg_debug (str "We will be declaring " ++ Constr.debug_print temp);

  (* recover the local universes from the evar map, minimize them, and update the term *)
  let uctx = Evd.evar_universe_context sigma in
  let uctx = UState.minimize uctx in
  let tm = UState.nf_universes uctx tm in
  (* declare the definition *)
  let kind = Decls.(IsDefinition Definition) in
  let poly = Declareops.inductive_is_polymorphic mib in
  let univ_entry = UState.univ_entry ~poly uctx in
  let entry = Declare.definition_entry ~univs:univ_entry tm in
  let kn = Declare.declare_constant ~name ~kind entry in

  (* minimize universes *)

  (* declare the definition but the intended way *)
  let info = Declare.Info.make ~poly in
  let cinfo = Declare.CInfo.make name (Some typ) () in
  let opaque = false in
  let kn = Declare.declare_definition ~info ~cinfo ~opaque ~body evd

(* let declare_definition_scheme ~internal ~univs ~role ~name c = *)
(*   let kind = Decls.(IsDefinition Scheme) in *)
(*   let entry = pure_definition_entry ~univs c in *)
(*   let kn, eff = declare_private_constant ~role ~kind ~name entry in *)
(*   let () = if internal then () else definition_message name in *)
(*   kn, eff *)

let declare_inductive_obs_eqs kn =
  let mib = Global.lookup_mind kn in
  (* On récup l'environnement
   on instancie les univers
   Nécessairement, *)
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
  (* user_err Pp.(str "Observational inductives are not supported in sections yet") *)

let declare_inductive_observational_data kn =
  let mib = Global.lookup_mind kn in
  if mib.mind_finite = Declarations.CoFinite then
    user_err Pp.(str "Observational coinductive types are not supported yet");
  if Context.Named.length mib.mind_hyps > 0 then
    warn_about_sections ();
  declare_inductive_obs_eqs kn;
  declare_inductive_casts kn;
  declare_inductive_rewrite_rules kn
