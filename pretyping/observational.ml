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
open Constr
open Namegen
open Declarations
open Inductiveops


(** Useful for testing *)

(* let settype = EConstr.to_constr sigma (EConstr.mkSort EConstr.ESorts.set) in *)
(* let tm = it_mkProd_or_LetIn_name env settype ctor.cs_args in *)
(* Feedback.msg_debug (str "The args of contructor " ++ str eq_name ++ str " seem to be " ++ Constr.debug_print tm) ; *)


(** Global stuff and open recursion *)

let max_indices = 4
let obseq_constant = ref None
let cast_constant = ref None
let prop_cast_constant = ref None
let ap_ty_constant = Array.make max_indices None

let declare_observational_equality = ref (fun ~univs ~name c ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))

let declare_forded_constructor = ref (fun ~univs ~name c ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))

let declare_observational_rewrite = ref (fun ~univs ~name c d ->
    CErrors.anomaly (Pp.str "observational axioms declarator not registered"))


(** records for intermediate data *)

type constructor_info = {
    csi_params : EConstr.rel_context;
    csi_args : EConstr.rel_context;    (* defined in context `csi_params` *)
    csi_ind : EConstr.t;               (* defined in context `csi_params ; csi_args` *)
    csi_name : Names.Id.t;             (* name of the constructor *)
    csi_base_name : Names.Id.t;        (* abbreviation to be used as a base for other names *)
  }

type ind_ty_info = {
    idi_params : EConstr.rel_context;
    idi_indx : EConstr.rel_context;                              (* defined in context `idi_params` *)
    idi_indx_univs : (Univ.Universe.t * EConstr.ESorts.t) list;  (* universes and sorts for indices *)
    idi_ind_type : Inductiveops.inductive_type;                  (* defined in context `idi_params ; idi_indx` *)
    idi_ind_constr : EConstr.t;                                  (* defined in context `idi_params ; idi_indx` *)
    idi_sort : EConstr.ESorts.t ;                                (* sort for the inductive type *)
  }


(* let ident_hd env ids t na = *)
(*   let na = named_hd env (Evd.from_env env) (EConstr.of_constr t) na in *)
(*   next_name_away na ids *)

(* let set_names env_for_named_hd env_for_next_ident_away l = *)
(*   let ids = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env_for_next_ident_away)) in *)
(*   snd (List.fold_right (fun d (ids,l) -> *)
(*       let id = ident_hd env_for_named_hd ids (get_type d) (get_name d) in (Id.Set.add id ids, set_name (Name id) d :: l)) l (ids,[])) *)

(* let it_mkLambda_or_LetIn_name env b l = it_mkLambda_or_LetIn b (set_names env env l) *)
(* let it_mkProd_or_LetIn_name env b l = it_mkProd_or_LetIn b (set_names env env l) *)

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
  let env = EConstr.push_rel_context ctxt env in
  Retyping.get_sort_of env sigma ty

(* let get_type_of_in_context env sigma ctxt ty = *)
(*   let env = Environ.push_rel_context ctxt env in *)
(*   Retyping.get_type_of env sigma ty *)


(** Weaken a renaming
   if `sigma : Delta -> Gamma` and Delta_0 has size n
   then `wkn n sigma : Delta ; Delta_0 -> Gamma` *)

let wkn n sigma = (Esubst.el_shft n (Esubst.el_liftn n sigma))


(** Vars.exliftn but for eConstr instead of Constr *)

let e_exliftn ren c =
  let c = EConstr.Unsafe.to_constr c in
  let res = Vars.exliftn ren c in
  EConstr.of_constr res


(** Weaken an entire context, lifting the substitution every time
    TODO : is that not just EConstr.Vars.lift_rel_context 1 ? *)

let wk1_context ctxt =
  let aux = fun decl (ren, ctxt) ->
    let decl = Context.Rel.Declaration.map_constr (e_exliftn ren) decl in
    let wk = Esubst.el_lift ren in
    (wk, decl::ctxt)
  in
  let _, ctxt = Context.Rel.fold_outside aux ctxt
                  ~init:(wkn 1 (Esubst.el_id), Context.Rel.empty) in
  ctxt


(** TODO : probably just EConstr.Vars.lift 1 *)

let wk1_tm = e_exliftn (Esubst.el_shft 1 (Esubst.el_id))


(** Some functions for manipulating lists *)

let rec alternate_zip l1 l2 =
  match l1 with
  | [] -> l2
  | hd::tl -> hd::(alternate_zip l2 tl)

let rec alternate_zip3 l1 l2 l3 =
  match l1 with
  | [] -> alternate_zip l2 l3
  | hd::tl -> hd::(alternate_zip3 l2 l3 tl)

let rec fold_right4 f l1 l2 l3 l4 accu =
  match (l1, l2, l3, l4) with
    ([], [], [], []) -> accu
  | (a1::l1, a2::l2, a3::l3, a4::l4) -> f a1 a2 a3 a4 (fold_right4 f l1 l2 l3 l4 accu)
  | (_, _, _, _) -> invalid_arg "fold_right4"

let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
    ([], [], []) -> []
  | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
  | (_, _, _) -> invalid_arg "map3"

let rec separate n l =
  if n > 0 then
    match l with
    | [] -> [], []
    | hd::tl -> let l1, l2 = separate (n-1) tl in hd::l1, l2
  else
    [], l


(** Duplicate all the entries in a context, and return a substitution from the duplicated context *)

let duplicate_context ctx =
  let aux = (fun decl (ren, nctx) ->
      let decl = Context.Rel.Declaration.map_constr (e_exliftn ren) decl in
      let d1 = Context.Rel.Declaration.map_name next_name decl in
      let d2 = Context.Rel.Declaration.map_name next_name decl in
      let ren = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in
      (ren, d1 :: d2 :: nctx))
  in
  Context.Rel.fold_outside aux ctx
    ~init:(Esubst.el_id, Context.Rel.empty)


(** This function instantiates a context with new evars, and returns the updated evar_map along with the instance.
    If ignored is true, then the evars are InternalHoles. Otherwise they are MatchingVar's *)

let evar_ctxt ignored env sigma ctx =
  let rec reln sigma subst = function
    | Context.Rel.Declaration.LocalAssum (annot, ty) :: hyps ->
       let sigma, subst = reln sigma subst hyps in

       let ty = EConstr.Vars.substl subst ty in
       let relevance = Some (annot.binder_relevance) in
       let src =
         if ignored then
           Some (None , Evar_kinds.InternalHole)
         else
           Some (None , Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar (Names.Id.of_string "_")))
       in
       let sigma, ev = Evarutil.new_evar ?src ?relevance env sigma ty in
       (* let ev = EConstr.Unsafe.to_constr ev in *)
       sigma, (ev :: subst)
    | Context.Rel.Declaration.LocalDef (annot, tm, ty) :: hyps ->
       let sigma, subst = reln sigma subst hyps in
       let tm = EConstr.Vars.substl subst tm in
       sigma, (tm :: subst)
    | [] -> sigma, subst
  in
  reln sigma [] ctx


(* let complex_instantiate mk ctx = *)
(*   let rec aux = function *)
(*     | Context.Rel.Declaration.LocalAssum (annot, ty) :: hyps -> *)
(*        let n, subst = aux hyps in *)
(*        let ty = EConstr.Vars.substl subst ty in *)
(*        let tm = mk n ty in *)
(*        n+1, (tm :: subst) *)
(*     | Context.Rel.Declaration.LocalDef (annot, tm, ty) :: hyps -> *)
(*        let n, subst = aux hyps in *)
(*        let tm = EConstr.Vars.substl subst tm in *)
(*        n, (tm :: subst) *)
(*     | [] -> 1, [] *)
(*   in *)
(*   snd (aux ctx) *)


(** If gamma is an instance of the context Gamma,
    then this function produces the list of types of gamma *)

let types_of_instance ctx inst =
  let rec aux ctx inst =
    match ctx, inst with
    | Context.Rel.Declaration.LocalDef (annot, tm, ty) :: hyps , _ ->
       let subst, tys = aux hyps inst in
       let tm = EConstr.Vars.substl subst tm in
       (tm :: subst), tys
    | Context.Rel.Declaration.LocalAssum (annot, ty) :: hyps , tm :: tl ->
       let subst, tys = aux hyps tl in
       let ty = EConstr.Vars.substl subst ty in
       (tm :: subst), (ty :: tys)
    | [] , [] ->
       [], []
    | _ , _ -> invalid_arg "types_of_instance"
  in
  List.rev (snd (aux ctx (List.rev inst)))


(** Relocation of evars into de Bruijn indices
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


(* Adding a universe level >= s to an evar map.
    s is a sort, which might be a sup of several levels. *)

(* let univ_level_sup env sigma s = *)
(*   let sigma, u1 = Evd.new_univ_level_variable Evd.univ_flexible sigma in *)
(*   let s1 = *)
(*     if EConstr.ESorts.is_sprop sigma s then *)
(*       s *)
(*     else if EConstr.ESorts.is_prop sigma s then *)
(*       user_err (Pp.str "Prop is not compatible with the observational mode. Use SProp instead. *)
(*                         (Hint: if your inductive definition is a sub-singleton, Coq might put it in Prop without telling you)") *)
(*     else *)
(*       EConstr.ESorts.make (Sorts.mkType (Univ.Universe.make u1)) *)
(*   in *)
(*   let sigma = Evd.set_leq_sort env sigma s s1 in *)
(*   sigma, s1, u1 *)


(** This function is a bit silly:
   in order to get the universe corresponding to s, we create a new flexible universe variable,
   we put it inside a universe, and we add an equality constraint to the evar_map.
   Even though s is basically a disguised universe... *)

let universe_of_sort env sigma s =
  if EConstr.ESorts.is_prop sigma s then
    user_err (Pp.str "Prop is not compatible with the observational mode. Use SProp instead.
                      (Hint: if your inductive definition is a sub-singleton, Coq might put it in Prop without telling you)")
  else if EConstr.ESorts.is_sprop sigma s then
    sigma, (Univ.Universe.type0, EConstr.ESorts.sprop)
  else
    let sigma, u = Evd.new_univ_level_variable Evd.univ_flexible sigma in
    let univ = Univ.Universe.make u in
    let new_s = EConstr.ESorts.make (Sorts.mkType univ) in
    let sigma = Evd.set_leq_sort env sigma s new_s in
    sigma, (univ, new_s)


(* Adding a universe level strictly greater than u to the evar_map.
    u is a level. *)

(* let univ_level_next sigma u = *)
(*   let sigma, u1 = Evd.new_univ_level_variable Evd.univ_flexible sigma in *)
(*   let cstr = Univ.Constraints.singleton (u, Univ.Le, Univ.Universe.(super (make u1))) in *)
(*   let sigma = Evd.add_constraints sigma cstr in *)
(*   sigma, u1 *)


(** Fetching the observational primitives
    For now, they are being fetched from the current file
    Eventually they should be fetched from the library *)

let fetch_observational_data () =
  let obseq_qualid = Libnames.qualid_of_ident (Names.Id.of_string "obseq") in
  let cast_qualid = Libnames.qualid_of_ident (Names.Id.of_string "cast") in
  let prop_cast_qualid = Libnames.qualid_of_ident (Names.Id.of_string "cast_prop") in
  try
    obseq_constant := Some (Nametab.global_inductive obseq_qualid) ;
    cast_constant := Some (Nametab.locate_constant cast_qualid) ;
    prop_cast_constant := Some (Nametab.locate_constant prop_cast_qualid) ;
    for i = 1 to max_indices do
      ap_ty_constant.(i - 1) <- Some (Nametab.locate_constant
                                    (Libnames.qualid_of_ident
                                       (Names.Id.of_string ("ap_ty" ^ (string_of_int i))))) ;
    done ;
  with
    Not_found -> user_err Pp.(str "The observational equality or the cast operator does not exist.\
                                   Did you forget to open the observational library?")


(** Building @obseq@{u} ty tm1 tm2 *)

let make_obseq u ty tm1 tm2 =
  match !obseq_constant with
  | None -> user_err Pp.(str "The observational equality does not exist.")
  | Some obseq ->
     let univs = EConstr.EInstance.make (UVars.Instance.of_array ([| |], [| u |])) in
     let obseq_fam = Inductiveops.make_ind_family ((obseq, univs), [ty ; tm1]) in
     Inductiveops.mkAppliedInd (Inductiveops.make_ind_type (obseq_fam, [tm2]))


(** Building @obseq@{u+1} Type@{u} tm1 tm2 *)

let make_obseqU ?(is_sprop = false) u tm1 tm2 =
  let u = if is_sprop then Univ.Universe.type0 else u in
  let unext = if is_sprop then Univ.Universe.type1 else Univ.Universe.super u in
  let ty = EConstr.(mkSort (if is_sprop then ESorts.sprop else (ESorts.make (Sorts.mkType u)))) in
  match !obseq_constant with
  | None -> user_err Pp.(str "The observational equality does not exist.")
  | Some obseq ->
     let univs = EConstr.EInstance.make (UVars.Instance.of_array ([| |], [| unext |])) in
     let obseq_fam = Inductiveops.make_ind_family ((obseq, univs), [ty; tm1]) in
     Inductiveops.mkAppliedInd (Inductiveops.make_ind_type (obseq_fam, [tm2]))

(** Building @obseq_refl@{u} ty tm *)

let make_obseq_refl u ty tm =
  match !obseq_constant with
  | None -> user_err Pp.(str "The observational equality does not exist.")
  | Some obseq ->
     let univs = EConstr.EInstance.make (UVars.Instance.of_array ([| |], [| u |])) in
     let ctor = EConstr.mkConstructUi ((obseq, univs), 1) in
     EConstr.mkApp (ctor, [| ty ; tm |])


(** Building a cast term *)

let make_cast ?(is_sprop = false) u ty1 ty2 eq tm =
  if is_sprop then
    match !prop_cast_constant with
    | None -> user_err Pp.(str "The propositional cast operator does not exist.")
    | Some cast ->
       let univs = EConstr.EInstance.empty in
       let cast = EConstr.mkConstU (cast, univs) in
       EConstr.mkApp (cast, [| ty1 ; ty2 ; eq ; tm |])
  else
    match !cast_constant with
    | None -> user_err Pp.(str "The cast operator does not exist.")
    | Some cast ->
       let univs = EConstr.EInstance.make (UVars.Instance.of_array ([| |], [| u |])) in
       let cast = EConstr.mkConstU (cast, univs) in
       EConstr.mkApp (cast, [| ty1 ; ty2 ; eq ; tm |])


(** This function uses the constant ap_ty to obtain an equality between two instances of the last type of a (smashed) context
   - telescope should be a smashed context of n+1 types
   - univs should be a list of n+1 universe levels for the types in telescope
   - inst0 and inst1 are two instances of size n of the first n types of context
   - eqs is a list of n equalities between inst0 and inst1 *)

let make_ap_ty n telescope univs inst0 inst1 eqs =
  if n < 1 then
    user_err Pp.(str "Trying to build ap_ty for a telescope with < 2 elements.") ;
  let ap_ty_cst = match ap_ty_constant.(n - 1) with
    | None -> user_err Pp.(str "The constant ap_ty" ++ int n ++ str " does not exist.")
    | Some cst -> cst
  in
  let (_, ty_predicates) =
    Context.Rel.fold_outside
      (fun decl (ctxt, preds) -> (decl::ctxt, (EConstr.it_mkLambda_or_LetIn (Context.Rel.Declaration.get_type decl) ctxt)::preds))
      telescope ~init:(Context.Rel.empty, [])
  in
  let univs = Array.of_list (List.rev univs) in
  let remaining_args = alternate_zip3 eqs inst1 inst0 in
  let full_args = remaining_args @ ty_predicates in
  let full_args = Array.of_list (List.rev full_args) in
  let univs = EConstr.EInstance.make (UVars.Instance.of_array ([| |], univs)) in
  let ap_ty = EConstr.mkConstU (ap_ty_cst, univs) in
  EConstr.mkApp (ap_ty, full_args)


(** This function produces a context of equalities that encodes the equality of two instances
    - telescope should be a context of types (not necessarily smashed)
    - univs should be a list of n+1 universe levels for the types in telescope
    - inst0 and inst1 are two instances of the telescope *)

let telescope_equality env sigma telescope univs inst0 inst1 =
  let telescope = List.rev (EConstr.Vars.smash_rel_context telescope) in
  let univs = List.rev univs in
  let fold_aux ty (u, sort) x y (ctxt, lift, tys, us, xs, ys, eqs) =
    (* update the new x, y with the renaming *)
    let n = Context.Rel.length tys in
    let ty = Context.Rel.Declaration.map_constr (EConstr.Vars.liftn lift (n+1)) ty in
    let x = EConstr.Vars.lift lift x in
    let y = EConstr.Vars.lift lift y in
    (* first we define a new equality built from ap_ty *)
    let ap_ty = make_ap_ty n (ty::tys) (u::us) xs ys eqs in
    let subst_x = EConstr.Vars.subst_of_rel_context_instance_list tys (List.rev xs) in
    let subst_y = EConstr.Vars.subst_of_rel_context_instance_list tys (List.rev ys) in
    let ty_x = EConstr.Vars.substl subst_x (Context.Rel.Declaration.get_type ty) in
    let ty_y = EConstr.Vars.substl subst_y (Context.Rel.Declaration.get_type ty) in
    let is_sprop = EConstr.ESorts.is_sprop sigma sort in
    let ty_ap_ty = make_obseqU ~is_sprop u ty_x ty_y in
    (* we add it to the context *)
    let annot = Context.make_annot (Names.Name.mk_name (Names.Id.of_string "h")) Sorts.Irrelevant in
    let ctxt = Context.Rel.Declaration.LocalDef (annot, ap_ty, ty_ap_ty) :: ctxt in
    (* next we build the cast of x *)
    let cast_x = make_cast u (EConstr.Vars.lift 1 ty_x) (EConstr.Vars.lift 1 ty_y)
                   (EConstr.mkRel 1) (EConstr.Vars.lift 1 x) in
    (* finally we build the equality type between cast_x and y and we add it to the context *)
    let eq_x_y = make_obseq u (EConstr.Vars.lift 1 ty_y) cast_x (EConstr.Vars.lift 1 y) in
    let eqannot = Context.make_annot (Names.Name.mk_name (Names.Id.of_string "e")) Sorts.Irrelevant in
    let ctxt = Context.Rel.Declaration.LocalAssum (eqannot, eq_x_y) :: ctxt in
    (* we update all the data to be in the new context for the recursive call *)
    (* let new_ren = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in *)
    (* let wk2 = Esubst.el_shft 1 (Esubst.el_liftn 2 Esubst.el_id) in *)
    let new_tys = EConstr.Vars.lift_rel_context 2 (ty::tys) in
    let new_xs = List.map (EConstr.Vars.lift 2) (x::xs) in
    let new_ys = List.map (EConstr.Vars.lift 2) (y::ys) in
    let new_eqs = (EConstr.mkRel 1)::(List.map (EConstr.Vars.lift 2) eqs) in
    (ctxt, lift+2, new_tys, u::us, new_xs, new_ys, new_eqs)
  in
  match telescope, univs, inst0, inst1 with
  | [], [], [], [] -> Context.Rel.empty
  | ty0::telescope, (u0, sort0)::univs, x0::inst0, y0::inst1 ->
     begin
       let telescope, univs, inst0, inst1 = List.rev telescope, List.rev univs, List.rev inst0, List.rev inst1 in
       let eq0 = make_obseq u0 (Context.Rel.Declaration.get_type ty0) x0 y0 in
       (* let ids = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env)) in *)
       let eq0_annot = Context.make_annot (Names.Name.mk_name (Names.Id.of_string "e")) Sorts.Irrelevant in
       let init_ctxt = [ Context.Rel.Declaration.LocalAssum (eq0_annot, eq0) ] in
       let init_eq = EConstr.mkRel 1 in
       let result, _, _, _, _, _, _ =
         fold_right4 fold_aux telescope univs inst0 inst1
           (init_ctxt, 1, [Context.Rel.Declaration.map_constr (EConstr.Vars.lift 1) ty0], [u0]
            , [EConstr.Vars.lift 1 x0], [EConstr.Vars.lift 1 y0], [init_eq])
       in result
     end
  | _, _, _, _ -> user_err Pp.(str "function telescope_equality called with unbalanced arguments")


(** This function converts a constructor with indices to a forded constructor.
    ctor is the base constructor_summary and ctor_name is its name *)

let get_forded_ctor env sigma instantiated_ind ctor ctor_name =
  let param_ctxt = instantiated_ind.idi_params in
  let indx_ctxt, indx_univs = instantiated_ind.idi_indx, instantiated_ind.idi_indx_univs in
  let args_ctxt = ctor.cs_args in
  let size_args = List.length args_ctxt in
  let size_indx = List.length indx_ctxt in

  let wk_indx = EConstr.Vars.lift_rel_context (size_args + size_indx) indx_ctxt in (* indx_ctxt is defined in param_ctxt *)
  let expected_inst = Array.to_list (ctor.cs_concl_realargs) in (* cs_concl_realargs is defined in cs_args @ indx_ctxt @ param_ctxt *)
  let actual_inst = Context.Rel.instance_list EConstr.mkRel size_args indx_ctxt in
  let eq_ctxt = telescope_equality env sigma wk_indx indx_univs actual_inst expected_inst in

  let forded_params = indx_ctxt @ param_ctxt in
  let forded_args = eq_ctxt @ args_ctxt in
  let forded_name = Names.Id.of_string (Names.Id.to_string ctor_name ^ "_cast") in
  { csi_ind = EConstr.Vars.lift (List.length forded_args) instantiated_ind.idi_ind_constr
  ; csi_params = forded_params
  ; csi_args = forded_args
  ; csi_name = forded_name
  ; csi_base_name = ctor_name }


(** Reflexivity for all the forded arguments *)

let forded_reflexive_instance instantiated_ind ctor =
  let wk = (List.length ctor.cs_args + List.length instantiated_ind.idi_indx) in
  (* from context `params` to `params ; indx ; args` *)
  let indx_ctxt = EConstr.Vars.lift_rel_context wk instantiated_ind.idi_indx in
  let indx_univs = instantiated_ind.idi_indx_univs in
  let expected_inst = Array.to_list ctor.cs_concl_realargs in (* in context params ; indx ; args *)
  let index_tys = types_of_instance indx_ctxt expected_inst in
  (* in context params ; indx ; args *)
  map3 (fun univ ty tm -> make_obseq_refl (fst univ) ty tm) indx_univs index_tys expected_inst


(** This function declares a forded constructor and returns the declared name with the universe entry *)

let declare_forded_ctor ?loc ~poly env sigma ctor =
  let ctxt = ctor.csi_args @ ctor.csi_params in
  (* let param_inst = Context.Rel.instance_list mkRel 0 ctor.csi_params in *)
  let ty = ctor.csi_ind in
  let forded_ctor = EConstr.it_mkProd_or_LetIn ty ctxt in

  (* optional debug *)
  Feedback.msg_debug (str "Observational inductives: Declaring parameter "
                      ++ str (Names.Id.to_string ctor.csi_name)
                      ++ str " whose type is "
                      ++ Termops.Internal.print_constr_env env sigma forded_ctor) ;

  (* normalizing the universes in the evar map and in the body of the axiom *)
  let uctx = Evd.evar_universe_context sigma in
  let uctx = UState.minimize uctx in
  let forded_ctor = EConstr.to_constr sigma forded_ctor in
  let forded_ctor = UState.nf_universes uctx forded_ctor in
  (* declaring the axiom with its local universe context *)
  let univs = UState.univ_entry ~poly uctx in
  let declared_name = !declare_forded_constructor ~univs ~name:ctor.csi_name forded_ctor in
  (declared_name, univs)


(** Building a rewrite rule *)

let make_rewrite_rule ?loc env sigma uinst lhs rhs =
  (* at this point there are two kinds of universes:
     - the ones that come from the instance of the inductive (if polymorphic), call them v1 v2...
     - the ones that we added, u1 and u2
     In all cases, rewrite rules for constructors will be of the form

       cast@{u1 u2} (Ind@{v1 v2...} ?A) (Ind@{v1 v2...} ?A0) ?e (ctor@{v1 v2...} ?A ?t)
         ==> ctor@{v1 v2...} ?A0 (cast@{u1 u2} B@{A := ?A} B@{A := ?A0} (ax ?e) ?t)

     Note that some levels appear several times, which should imply level equations--otherwise,
     universe polymorphic inductives will break SR
  *)
  (* let cast_uinst = UVars.Instance.of_array ([| |], [| u1 |]) in *)
  (* let uinst = UVars.Instance.append uinst cast_uinst in *)
  let usubst = UVars.make_instance_subst uinst in
  let ((nvars', invtbl), (nvarqs', invtblq), (nvarus', invtblu)), (head_pat, elims) =
    Rewrite_rule.safe_pattern_of_constr ~loc:loc env sigma usubst 0
      ((1, Evar.Map.empty), (0, Int.Map.empty), (0, Int.Map.empty)) lhs
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
  head_symbol, { nvars = (nvars' - 1, nvarqs', nvarus'); lhs_pat = head_umask, elims; rhs; equalities = [] }


(** This function declares a new observational equality axiom, and updates the state
    TODO: better documentation *)

let declare_ctorarg_obs_eq ~poly env u1 name decl (sigma, ctxt, ren1, ren2, cnt) =
  match decl with
  | Context.Rel.Declaration.LocalAssum (na, ty) ->
     let (param_ctxt, arg_ctxt, arg0_ctxt) = ctxt in
     let full_ctxt = arg0_ctxt @ (arg_ctxt @ param_ctxt) in
     let n_args = List.length arg_ctxt in
     (* generating the type of the observational equality *)
     let ty = Context.Rel.Declaration.get_type decl in
     let ty1 = e_exliftn (wkn n_args (Esubst.el_liftn n_args ren1)) ty in
     let ty2 = e_exliftn (Esubst.el_liftn n_args (wkn n_args ren2)) ty in
     let sort = get_sort_of_in_context env sigma full_ctxt ty1 in
     let is_sprop = EConstr.ESorts.is_sprop sigma sort in
     (* we declare new universe levels u1 and u2 to instantiate the polymorphic obseq constant *)
     (* let sigma, newsort, u1 = univ_level_sup env sigma sort in *)
     (* let sigma, u2 = univ_level_next sigma u1 in *)
     (* let s = EConstr.mkSort newsort in *)
     (* let s = EConstr.to_constr sigma s in *)

     (* TODO: Instead of using the universe level of the constructor argument type, I lazily reuse
        the levels from the inductive type family. I think that cumulativity guarantees it's okay *)
     let eq_ty = make_obseqU ~is_sprop u1 ty1 ty2 in
     let axiom = EConstr.it_mkProd_or_LetIn eq_ty full_ctxt in
     let name = Names.Id.of_string (name ^ string_of_int cnt) in

     (* optional debug *)
     Feedback.msg_debug (str "Observational inductives: Declaring parameter "
                         ++ str (Names.Id.to_string name)
                         ++ str " whose type is "
                         ++ Termops.Internal.print_constr_env env sigma axiom) ;

     (* normalizing the universes in the evar map and in the body of the axiom *)
     let uctx = Evd.evar_universe_context sigma in
     let uctx = UState.minimize uctx in
     let axiom = EConstr.to_constr sigma axiom in
     let axiom = UState.nf_universes uctx axiom in
     (* declaring the axiom with its local universe context *)
     let univs = UState.univ_entry ~poly uctx in
     let eq_name = !declare_observational_equality ~univs ~name axiom in

     (* generating the instance of the equality axiom that we will use in make_cast *)
     (* TODO: should I really be manipulating universes like that without an abstract interface? *)
     let eq_tm = match fst univs with
       | UState.Polymorphic_entry uc ->
          EConstr.mkConstU (eq_name, EConstr.EInstance.make (UVars.Instance.of_level_instance (UVars.UContext.instance uc)))
       | UState.Monomorphic_entry pe -> EConstr.mkConstU (eq_name, EConstr.EInstance.empty)
     in
     let eq_args = Context.Rel.instance EConstr.mkRel 0 full_ctxt in
     let eq_hyp = EConstr.mkApp (eq_tm, eq_args) in

     (* preparing the context for the next axiom *)
     let newty = e_exliftn (Esubst.el_liftn n_args ren1) ty in
     let arg_ctxt = (Context.Rel.Declaration.LocalAssum (na, newty)) :: arg_ctxt in
     (* since we added a term in arg_ctxt, we must weaken everything in arg0_ctxt *)
     let arg0_ctxt = wk1_context arg0_ctxt in
     (* then we add the new cast term to arg0_ctxt *)
     let ty1 = e_exliftn (wkn (n_args + 1) (Esubst.el_liftn n_args ren1)) ty in
     let ty2 = e_exliftn (Esubst.el_liftn n_args (wkn (n_args + 1) ren2)) ty in
     let cast_term = make_cast ~is_sprop u1 ty1 ty2 (wk1_tm eq_hyp) (EConstr.mkRel (n_args + 1)) in
     let arg0_ctxt = (Context.Rel.Declaration.LocalDef (na, cast_term, ty2)) :: arg0_ctxt in
     (sigma, (param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, cnt + 1)
  | Context.Rel.Declaration.LocalDef (na, tm, ty) as decl ->
     let (param_ctxt, arg_ctxt, arg0_ctxt) = ctxt in
     (* let full_ctxt = arg0_ctxt @ (arg_ctxt @ param_ctxt) in *)
     let n_args = List.length arg_ctxt in
     (* we simply make two copies of the letin, with the correct renamings *)
     let new_ren1 = (Esubst.el_liftn n_args ren1) in
     let decl1 = Context.Rel.Declaration.map_constr (e_exliftn new_ren1) decl in
     let arg_ctxt = decl1::arg_ctxt in
     let arg0_ctxt = wk1_context arg0_ctxt in
     let new_ren2 = (Esubst.el_liftn n_args (wkn (n_args + 1) ren2)) in
     let decl2 = Context.Rel.Declaration.map_constr (e_exliftn new_ren2) decl in
     let arg0_ctxt = decl2::arg0_ctxt in
     (sigma, (param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, cnt)


(** This function declares all the observational equality axioms that correspond to the
    arguments of the constructor `ctor`
    TODO: document return type *)

let declare_ctor_obs_eqs ?loc ~poly env sigma ind univ ctor =
  (* preparing the context of hypotheses for the axioms *)
  let ctxt = ind.idi_indx @ ind.idi_params in
  let (ren, dup_ctxt) = duplicate_context ctxt in
  (* extending it with the equality between two instances of the inductive *)
  let indty = ind.idi_ind_constr in
  let indty1 = e_exliftn ren indty in
  let indty2 = e_exliftn (Esubst.el_liftn 1 ren) indty in
  let eq_hyp = make_obseqU univ indty1 indty2 in
  let eq_annot = Context.make_annot (Names.Name.mk_name (Names.Id.of_string "e")) Sorts.Irrelevant in
  let hyp_ctxt = (Context.Rel.Declaration.LocalAssum (eq_annot, eq_hyp))::dup_ctxt in

  let eq_name = "obseq_" ^ Names.Id.to_string ctor.csi_base_name ^ "_" in
  let args = ctor.csi_args in
  let ren1 = Esubst.el_shft 1 (Esubst.el_liftn 1 ren) in
  let ren2 = Esubst.el_shft 1 (Esubst.el_liftn 2 ren) in

  let new_ctxt = Context.Rel.fold_outside (declare_ctorarg_obs_eq ~poly env univ eq_name) args
    ~init:(sigma, (hyp_ctxt, Context.Rel.empty, Context.Rel.empty), ren1, ren2, 0) in
  new_ctxt


let declare_ctor_cast_rule ?loc ~poly env uinst state ind univ (ctor, ctor_constr) =
  let sigma, (double_param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, _ = state in
  (* double_param_ctxt: two instances of parameters and indices + the equality between the two instantiated families *)
  (* arg_ctxt: an instance for the arguments of the current constructor *)
  (* arg0_ctxt: local definitions for the casted arguments *)
  (* ren1, ren2: term defined in the context of parameters and indices -> term defined in hyp_ctxt *)
  let n_args = List.length arg_ctxt in

  let indty = ind.idi_ind_constr in
  (* from params to double_params ; args *)
  let indty1 = e_exliftn (wkn n_args ren1) indty in
  let indty2 = e_exliftn (wkn n_args ren2) indty in
  let eq_hyp = EConstr.mkRel (n_args + 1) in

  (* from a term defined in `params ; args` to `double_params ; args` *)
  let inst_ctor_1 = e_exliftn (Esubst.el_liftn n_args ren1) ctor_constr in
  (* from a term defined in `params ; args` to `double_params ; args ; args0` *)
  let inst_ctor_2 = e_exliftn (Esubst.el_liftn n_args (wkn n_args ren2)) ctor_constr in

  (* We build evar instances of the context. esubst is made of MatchingVar's for normal holes,
     esubst_ignored is made of InternalHole's for ignored holes. *)
  let sigma, esubst = evar_ctxt false env sigma (arg_ctxt @ double_param_ctxt) in
  let sigma, esubst_ignored = evar_ctxt true env sigma (arg_ctxt @ double_param_ctxt) in

  (* the parameters in indty1 are subsumed by the parameters in inst_ctor_1, so we make them
     InternalHole's to avoid unnecessary equations. TODO: is it fine for indices? *)
  let indty1 = EConstr.Vars.substl esubst_ignored indty1 in
  let rew_left = make_cast univ indty1 indty2 eq_hyp inst_ctor_1 in
  let rew_left = EConstr.Vars.substl esubst rew_left in

  let rew_right = EConstr.it_mkLambda_or_LetIn inst_ctor_2 arg0_ctxt in
  let rew_right = EConstr.Vars.substl esubst rew_right in

  let id = Names.Id.of_string ("rewrite_" ^ Names.Id.to_string ctor.csi_name) in

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

  let rew = make_rewrite_rule ?loc env sigma uinst (EConstr.Unsafe.to_constr rew_left) rew_right in
  Global.add_rewrite_rules id { rewrules_rules = [rew] }


let declare_normal_to_forded ?loc ~poly env uinst state ind univ (normal_ctor, normal_constr) (forded_ctor, forded_constr) =
  let sigma, (double_param_ctxt, arg_ctxt, arg0_ctxt), ren1, ren2, _ = state in
  (* double_param_ctxt: two instances of parameters and indices + the equality between the two instantiated families *)
  (* arg_ctxt: an instance for the arguments of the current constructor *)
  (* arg0_ctxt: local definitions for the casted arguments *)
  (* ren1, ren2: term defined in the context of parameters and indices -> term defined in hyp_ctxt *)
  let size_normal = List.length normal_ctor.cs_args in
  let size_total = List.length arg_ctxt in
  let size_forded = size_total - size_normal in
  let forded_arg_ctxt, normal_arg_ctxt = separate size_forded arg_ctxt in
  let reflexive_inst = forded_reflexive_instance ind normal_ctor in
  let reflexive_inst = List.map (e_exliftn (Esubst.el_liftn size_normal ren1)) reflexive_inst in
  let reflexive_subst = EConstr.Vars.subst_of_rel_context_instance_list forded_arg_ctxt reflexive_inst in

  let indty = ind.idi_ind_constr in
  (* from `params ; indx` to `double_params ; double_index ; eq ; normal_args` *)
  let indty1 = e_exliftn (wkn size_normal ren1) indty in
  let indty2 = e_exliftn (wkn size_normal ren2) indty in
  let eq_hyp = EConstr.mkRel (size_normal + 1) in

  (* from `params ; indx ; normal_args` to `double_params ; double_indx ; eq ; normal_args` *)
  let inst_ctor_1 = e_exliftn (Esubst.el_liftn size_normal ren1) normal_constr in
  (* from `params ; indx ; normal_args ; forded_args` to
     `double_params ; double_indx ; eq ; normal_args ; forded_args ; normal_args0 ; forded_args0` *)
  let inst_ctor_2 = e_exliftn (Esubst.el_liftn size_total (wkn size_total ren2)) forded_constr in

  (* We build evar instances of the context. esubst is made of MatchingVar's for normal holes,
     esubst_ignored is made of InternalHole's for ignored holes. *)
  let sigma, esubst = evar_ctxt false env sigma (normal_arg_ctxt @ double_param_ctxt) in
  let sigma, esubst_ignored = evar_ctxt true env sigma (normal_arg_ctxt @ double_param_ctxt) in

  (* the parameters in indty1 are subsumed by the parameters in inst_ctor_1, so we make them
     InternalHole's to avoid unnecessary equations. TODO: is it fine for indices? *)
  (* TODO: i deactivated this but now there is some superfluous equations on parameters.. *)
  (* let indty1 = EConstr.Vars.substl esubst_ignored indty1 in *)
  let rew_left = make_cast univ indty1 indty2 eq_hyp inst_ctor_1 in
  let rew_left = EConstr.Vars.substl esubst rew_left in

  let rew_right = EConstr.it_mkLambda_or_LetIn inst_ctor_2 arg0_ctxt in
  let rew_right = EConstr.Vars.substl reflexive_subst rew_right in
  let rew_right = EConstr.Vars.substl esubst rew_right in

  let id = Names.Id.of_string ("rewrite_" ^ Names.Id.to_string forded_ctor.csi_base_name) in

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

  let rew = make_rewrite_rule ?loc env sigma uinst (EConstr.Unsafe.to_constr rew_left) rew_right in
  Global.add_rewrite_rules id { rewrules_rules = [rew] }


(**
   - normal_constr is defined in context `params ; indx ; args`
   - forded_constr is defined in context `params ; indx ; args ; forded_args` *)

let declare_forded_to_normal ?loc ~poly env uinst ind univ (normal_ctor, normal_constr) (forded_ctor, forded_constr) =
  let size_normal = List.length normal_ctor.cs_args in
  let size_total = List.length arg_ctxt in
  let size_forded = size_total - size_normal in
  let param_ctxt = ind.idi_params in
  let indx_ctxt = ind.idi_indx in  (* defined in `params` *)
  let full_arg_ctxt = forded_ctor.csi_args in  (* defined in `params ; indx` *)
  let forded_arg_ctxt, normal_arg_ctxt = separate size_forded full_arg_ctxt in

  let normal_constr = EConstr.Vars.lift size_forded normal_constr in
  ()


(** Grabs the universes from ctxt after pushing local_ctxt in the environment *)

let get_context_univs env sigma local_ctxt ctxt =
  let ctxt = EConstr.Vars.smash_rel_context ctxt in
  let fold_aux decl (sigma, local_ctxt, univs) =
    let sort = get_sort_of_in_context env sigma local_ctxt
                 (Context.Rel.Declaration.get_type decl) in
    let sigma, u = universe_of_sort env sigma sort in
    (sigma, decl::local_ctxt, u::univs)
  in
  let sigma, _, result = Context.Rel.fold_outside fold_aux ctxt ~init:(sigma, local_ctxt, []) in
  sigma, result


(** Instantiates the inductive, updates sigma, outputs ind_ty_info *)

let instantiate_ind env sigma ind u mib =
  let u = UVars.Instance.of_level_instance u in
  let uinst = EConstr.EInstance.make u in
  let param_ctxt = EConstr.of_rel_context (Inductive.inductive_paramdecls (mib, u)) in
  let param_instance = Context.Rel.instance_list EConstr.mkRel 0 param_ctxt in
  (* ind_fam is the inductive family with parameters instantiated to the ones from param_ctxt *)
  let ind_fam = Inductiveops.make_ind_family ((ind, uinst), param_instance) in
  let indx_ctxt = Inductiveops.get_arity env ind_fam in (* defined in param_ctxt *)
  let size_indx = List.length indx_ctxt in
  let n_indx = Inductiveops.inductive_nrealargs env ind in
  if n_indx > max_indices then
    user_err Pp.(str "Observational inductives with more than " ++ int max_indices
                 ++ str " indices are not supported yet.");

  let full_ctxt = indx_ctxt @ param_ctxt in
  let full_param_instance = Context.Rel.instance_list EConstr.mkRel size_indx param_ctxt in
  (* full_ind_fam is the same as ind_fam, but weakened to the context full_ctxt *)
  let full_ind_fam = Inductiveops.make_ind_family ((ind, uinst), full_param_instance) in

  (* instanciating the inductive type in the full context *)
  let indx_instance = Context.Rel.instance_list EConstr.mkRel 0 indx_ctxt in
  let ind_ty = Inductiveops.make_ind_type (full_ind_fam, indx_instance) in
  let ind_econstr = Inductiveops.mkAppliedInd ind_ty in
  (* grabbing the universes of the indices for the fording translation *)
  let sigma, indx_univs = get_context_univs env sigma param_ctxt indx_ctxt in
  let sort = get_sort_of_in_context env sigma full_ctxt ind_econstr in

  sigma, { idi_params = param_ctxt;
    idi_indx = indx_ctxt;
    idi_indx_univs = indx_univs;
    idi_ind_type = ind_ty;
    idi_ind_constr = ind_econstr;
    idi_sort = sort;
  }


let univ_for_inductive env sigma sort =
  let sigma, u = universe_of_sort env sigma sort in
  (* let s = EConstr.mkSort newsort in *)
  sigma, u


(** Generate constructor_info for a non-forded constructor *)

let get_ctor_info instantiated_ind ctor ctor_name =
  { csi_ind = EConstr.Vars.lift (List.length ctor.cs_args) instantiated_ind.idi_ind_constr
  ; csi_params = instantiated_ind.idi_params
  ; csi_args = ctor.cs_args
  ; csi_name = ctor_name
  ; csi_base_name = ctor_name }


(** Turns the constructor info for a forded constructor into an eConstr
    The result is defined in context `params ; indices ; args ; forded args` *)

let build_forded_constructor ctor (name, univs) =
  let ctor_constr = match fst univs with
    | UState.Polymorphic_entry uc ->
       EConstr.mkConstU (name, EConstr.EInstance.make (UVars.Instance.of_level_instance (UVars.UContext.instance uc)))
    | UState.Monomorphic_entry pe -> EConstr.mkConstU (name, EConstr.EInstance.empty)
  in
  let args = (Context.Rel.instance_list EConstr.mkRel 0 ctor.csi_args) in
  let nargs = List.length ctor.csi_args in
  let params = List.map (EConstr.Vars.lift nargs) (Context.Rel.instance_list EConstr.mkRel 0 ctor.csi_params) in
  let res = EConstr.applist (ctor_constr, params @ args) in
  res


(** TODO : this should be in univGen probably
    fresh_level_isntance is basically a copy of UnivGen.fresh_instance but it returns a LevelInstance *)

let fresh_level_instance auctx : _ UnivGen.in_sort_context_set =
  let qlen, ulen = UVars.AbstractContext.size auctx in
  let qinst = Array.init qlen (fun _ -> Sorts.Quality.QVar (UnivGen.new_sort_global())) in
  let uinst = Array.init ulen (fun _ -> UnivGen.fresh_level()) in
  let qctx = Array.fold_left (fun qctx q -> match q with
      | Sorts.Quality.QVar q -> Sorts.QVar.Set.add q qctx
      | _ -> assert false)
      Sorts.QVar.Set.empty
      qinst
  in
  let uctx = Array.fold_right Univ.Level.Set.add uinst Univ.Level.Set.empty in
  let linst = UVars.LevelInstance.of_array (qinst,uinst) in
  let inst = UVars.Instance.of_level_instance linst in
  linst, ((qctx,uctx), UVars.AbstractContext.instantiate inst auctx)


(** TODO : this should be in univGen probably
    fresh_inductive_levelinstance is basically a copy of Evd.fresh_inductive_instance
    but it returns a LevelInstance*)

let fresh_inductive_levelinstance ?loc ?(rigid=UState.univ_flexible) env sigma ind =
  let auctx = Environ.universes_of_global env (GlobRef.IndRef ind) in
  let u, ctx = fresh_level_instance auctx in
  Evd.with_sort_context_set ?loc rigid sigma ((ind, u), ctx)


(** Main function *)

let declare_one_inductive_obs_eqs ?loc ind =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  (* sigma contains the graph of global universes as well as an empty local universe context
     we update sigma with the local universes levels of the inductive (which is empty if ind is monomorphic) *)
  let sigma, pind = fresh_inductive_levelinstance ~rigid:UState.univ_rigid env sigma ind in
  (* u is the level instance for the inductive
     It maps universe variables in the inductive to universes in sigma *)
  let u = snd pind in
  let (mib,mip) = Global.lookup_inductive (fst pind) in
  let poly = Declareops.inductive_is_polymorphic mib in

  match mip.mind_relevance with
  | Sorts.Relevant ->
     let sigma, instantiated_ind = instantiate_ind env sigma (fst pind) u mib in
     let n_indx = List.length instantiated_ind.idi_indx_univs in
     let ctors = Inductiveops.get_constructors env
                   (fst (Inductiveops.dest_ind_type instantiated_ind.idi_ind_type)) in
     let ctors_names = mip.mind_consnames in
     for i = 0 to (Array.length ctors) - 1 do
       if n_indx > 0 then
         (* do the fording translation *)
         let forded_ctor = get_forded_ctor env sigma instantiated_ind ctors.(i) ctors_names.(i) in
         let forded_ctor_cst = declare_forded_ctor ?loc ~poly env sigma forded_ctor in
         let env = Global.env () in (* TODO: why do I need to fetch a new env after the declaration?? *)
         let forded_ctor_constr = build_forded_constructor forded_ctor forded_ctor_cst in
         (* declaring the observational axioms + rewrite rule *)
         let sigma_plus, (univ, _) = univ_for_inductive env sigma instantiated_ind.idi_sort in
         let state = declare_ctor_obs_eqs ?loc ~poly env sigma_plus instantiated_ind univ forded_ctor in
         declare_ctor_cast_rule ?loc ~poly env u state instantiated_ind univ (forded_ctor, forded_ctor_constr) ;
         (* relating the normal constructor to the forded constructor with rewrite rules *)
         let normal_ctor_constr = Inductiveops.build_dependent_constructor ctors.(i) in
         declare_normal_to_forded ?loc ~poly env u state instantiated_ind univ
           (ctors.(i), normal_ctor_constr) (forded_ctor, forded_ctor_constr) ;
         declare_forded_to_normal ?loc ~poly env u state instantiated_ind univ
           (ctors.(i), normal_ctor_constr) (forded_ctor, forded_ctor_constr) ;
         (* match and fix for forded contstructor *)
         (* declare_forded_ctor_match_rule *)
         ()
       else
         let ctor_constr = Inductiveops.build_dependent_constructor ctors.(i) in (* defined in context `params ; args` *)
         let ctor = get_ctor_info instantiated_ind ctors.(i) ctors_names.(i) in
         let sigma_plus, (univ, _) = univ_for_inductive env sigma instantiated_ind.idi_sort in
         let state = declare_ctor_obs_eqs ?loc ~poly env sigma_plus instantiated_ind univ ctor in
         declare_ctor_cast_rule ?loc ~poly env u state instantiated_ind univ (ctor, ctor_constr)
     done
  | _ -> ()

let warn_about_sections () =
  CWarnings.create ~name:"observational-in-section"
    (fun msg -> hov 0 msg) (hov 0 (str "Observational inductives do not properly support the sections mechanism yet. \
                                        You might get rules that are weaker than you expect outside of the section."))

let declare_inductive_observational_data ?loc (kn,i) =
  let mib = Global.lookup_mind kn in
  (* check that all options are set correctly *)
  if not (Environ.rewrite_rules_allowed (Global.env ())) then
    raise Environ.(RewriteRulesNotAllowed ObsInd);
  if mib.mind_finite = Declarations.CoFinite then
    user_err Pp.(str "Observational coinductive types are not supported yet.");
  if Context.Named.length mib.mind_hyps > 0 then
    warn_about_sections ();
  (* generate stuff *)
  fetch_observational_data ();
  declare_one_inductive_obs_eqs ?loc (kn,i);
