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

let mask_of_instance =
  Univ.Instance.to_array %>
  Array.map (Univ.Level.var_index %> Option.has_some)

let sort_pattern_of_sort =
  let open Sorts in
  function
  | Type u ->
    let b = match Univ.Universe.level u with Some lvl -> Option.has_some (Univ.Level.var_index lvl) | None ->
      if not @@ Univ.Level.(Set.for_all (var_index %> Option.has_some)) @@ Univ.Universe.levels u then
        CErrors.user_err Pp.(str "Unsupported algebraic level in pattern.")
      else false
    in
    InType, [| b |]
  | SProp -> InSProp, [||]
  | Prop -> InProp, [||]
  | Set -> InSet, [||]
  | QSort _ -> CErrors.user_err Pp.(str "Unsupported qsort level in pattern.")

let rec arg_pattern_of_constr t = kind t |> function
  | Rel _ -> APHole
  | _ -> APRigid (rigid_arg_pattern_of_constr t)
and rigid_arg_pattern_of_constr t = kind t |> function
  | App (f, args) -> APApp (rigid_arg_pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Const (c, u) -> APSymbol (c, mask_of_instance u)
  | Sort s -> APSort (sort_pattern_of_sort s)
  | Ind (ind, u) -> APInd (ind, mask_of_instance u)
  | Construct (c, u) -> APConstr (c, mask_of_instance u)
  | Int i -> APInt i
  | Float f -> APFloat f
  | _ -> assert false

let app_pattern_of_constr n t =
  let f, args = decompose_appvect t in
  let nargs = Array.length args in
  assert (nargs >= n);
  let remargs, _ = Array.chop (nargs - n) args in
  arg_pattern_of_constr (mkApp (f, remargs))

let app_pattern_of_constr' p = app_pattern_of_constr (Array.length (fst p)) (snd p)

let rec pattern_of_constr t = kind t |> function
  | Const (c, u) -> PConst (c, mask_of_instance u)
  | App (f, args) -> PApp (pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Case (ci, u, _, p, _, c, brs) ->
      PCase (ci.ci_ind, mask_of_instance u, app_pattern_of_constr' p, pattern_of_constr c, Array.map app_pattern_of_constr' brs)
  | Proj (p, c) -> PProj (p, pattern_of_constr c)
  | _ -> assert false

type state = (int * int Int.Map.t) * (int * int Int.Map.t)

let update_invtbl i curvar tbl =
  succ curvar, tbl |> Int.Map.update i @@ function
  | None -> Some curvar
  | Some k as c when k = curvar -> c
  | Some _ ->
      CErrors.user_err
        Pp.(str "Variable "
          ++ Constr.debug_print (of_kind (Rel i))
          ++ str" not used at the right place, expected "
          ++ Constr.debug_print (of_kind (Rel curvar))
          ++ str".")

let update_shft_invtbl shft (state, stateu) i =
  let (curvar, invtbl) = state in
  if i <= shft then
    CErrors.user_err
      Pp.(str "Variable "
        ++ Constr.debug_print (of_kind (Rel i))
        ++ str" not available from toplevel.");
  update_invtbl (i-shft) curvar invtbl, stateu

let update_invtblu1 lvl curvaru tbl =
  succ curvaru, tbl |> Int.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some _ ->
        CErrors.user_err
          Pp.(str "Universe variable "
            ++ Univ.Level.(pr (var lvl))
            ++ str" not used at the right place, expected "
            ++ Univ.Level.(pr (var curvaru))
            ++ str".")

let update_invtblu (state, stateu) u =
  let u = Univ.Instance.to_array u in
  let stateu, mask = Array.fold_left_map (fun (curvaru, invtblu) lvl ->
      match Univ.Level.var_index lvl with
      | Some lvl -> update_invtblu1 lvl curvaru invtblu, true
      | None -> (curvaru, invtblu), false
    ) stateu u
  in
  (state, stateu), mask

let safe_sort_pattern_of_sort (statev, stateu as state) =
  let open Sorts in
  function
  | Type u ->
    let stateu, mask1 = match Univ.Universe.level u with
    | None ->
      if not @@ Univ.Level.(Set.for_all (var_index %> Option.has_some)) @@ Univ.Universe.levels u then
        CErrors.user_err Pp.(str "Unsupported algebraic level in pattern.");
      stateu, false
    | Some lvl ->
      match Univ.Level.var_index lvl with
      | None -> stateu, false
      | Some lvl ->
          let curvaru, invtblu = stateu in
          update_invtblu1 lvl curvaru invtblu, true
    in
    (statev, stateu), (InType, [|mask1|])
  | SProp -> state, (InSProp, [||])
  | Prop -> state, (InProp, [||])
  | Set -> state, (InSet, [||])
  | QSort _ -> CErrors.user_err Pp.(str "Unsupported qsort level in pattern.")

let rec safe_arg_pattern_of_constr env shft state t = kind t |> function
  | Rel i ->
      let state = update_shft_invtbl shft state i in
      state, APHole
  | _ ->
      let state, p = safe_rigid_arg_pattern_of_constr env shft state t in
      state, APRigid p
and safe_rigid_arg_pattern_of_constr env shft state t = kind t |> function
  | App (f, args) ->
      let state, pf = safe_rigid_arg_pattern_of_constr env shft state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr env shft) state args in
      state, APApp (pf, pargs)
  | Const (c, u) when Environ.is_symbol env c ->
      let state, mask = update_invtblu state u in
      state, APSymbol (c, mask)
  | Sort s ->
      let state, ps = safe_sort_pattern_of_sort state s in
      state, APSort ps
  | Ind (ind, u) ->
      let state, mask = update_invtblu state u in
      state, APInd (ind, mask)
  | Construct (c, u) ->
      let state, mask = update_invtblu state u in
      state, APConstr (c, mask)
  | Int i -> state, APInt i
  | Float f -> state, APFloat f
  | _ -> CErrors.user_err Pp.(str "Subterm not recognised as arg_pattern: " ++ Constr.debug_print t)

let safe_app_pattern_of_constr env shft ((curvar, invtbl), stateu) n t =
  let f, args = decompose_appvect t in
  let nargs = Array.length args in
  if not (nargs >= n) then CErrors.user_err Pp.(str "Subterm not recognised as pattern under binders: " ++ Constr.debug_print t);
  let remargs, usedargs = Array.chop (nargs - n) args in
  let () = Array.iter
    (kind %> function
      | Rel i when i <= n -> ()
      | t -> CErrors.user_err Pp.(str "Subterm not recognised as pattern under binders: " ++ Constr.debug_print (of_kind t)))
    usedargs
  in
  safe_arg_pattern_of_constr env (n + shft) ((curvar, invtbl), stateu) (mkApp (f, remargs))

let safe_app_pattern_of_constr' env shft state p = safe_app_pattern_of_constr env shft state (Array.length (fst p)) (snd p)


let rec safe_pattern_of_constr env shft state t = kind t |> function
  | Const (c, u) ->
      (match (Environ.lookup_constant c env).const_body with
      | Def _ | OpaqueDef _ | Primitive _ | Undef _ ->
          CErrors.user_err Pp.(str "Constant " ++ Constant.print c ++ str" used in pattern is not a symbol.")
      | Symbol _ -> ());
      let state, mask = update_invtblu state u in
      state, PConst (c, mask)
  | App (f, args) ->
      let state, pf = safe_pattern_of_constr env shft state f in
      let state, pargs = Array.fold_left_map (safe_arg_pattern_of_constr env shft) state args in
      state, PApp (pf, pargs)
  | Case (ci, u, _, ret, _, c, brs) ->
      let state, mask = update_invtblu state u in
      let state, pc = safe_pattern_of_constr env shft state c in
      let state, pret = safe_app_pattern_of_constr' env shft state ret in
      let state, pbrs = Array.fold_left_map (safe_app_pattern_of_constr' env shft) state brs in
      state, PCase (ci.ci_ind, mask, pret, pc, pbrs)
  | Proj (p, c) ->
      let state, pc = safe_pattern_of_constr env shft state c in
      state, PProj (p, pc)
  | _ -> CErrors.user_err Pp.(str "Subterm not recognised as pattern: " ++ Constr.debug_print t)

let rec head_constant = function
  | PConst (c, _) -> c
  | PApp (h, _) -> head_constant h
  | PCase (_, _, _, c, _) -> head_constant c
  | PProj (_, c) -> head_constant c

(* relocation of de Bruijn n in an explicit lift and a renaming table *)
let reloc_ren_rel (shft, tbl) n =
  if n <= shft then n else Int.Map.find (n-shft) tbl + shft

let rec rename eltbl c =
  match kind c with
  | Rel i ->
    let j = reloc_ren_rel eltbl i in
    if Int.equal i j then c else mkRel j
  | _ -> map_with_binders (on_fst succ) rename eltbl c

let rule_of_constant env c =
  let cb = Environ.lookup_constant c env in
  let ctx, eq_rule = Term.decompose_prod_decls cb.const_type in
  let lhs, rhs = match kind eq_rule with
  (* XXX should be checking that the head is eq not some arbitrary inductive
      Maybe by registering eq in retroknowledge *)
  | App (hd, [|_;lhs;rhs|]) when isInd hd -> lhs, rhs
  | _ ->
    CErrors.user_err
      Pp.(str "Cannot declare as rewrite rule: doesn't look like a proof of equality.")
  in
  let nvars = Context.Rel.length ctx in
  let nvarus = Univ.AbstractContext.size @@ Declareops.constant_polymorphic_context cb in
  let ((seen_vars, invtbl), (_, invtblu)), lhs_pat =
    safe_pattern_of_constr env 0 ((1, Int.Map.empty), (0, Int.Map.empty)) lhs
  in
  let seen_vars = pred seen_vars in
  (* Rels begin at 1 *)
  if not (seen_vars = nvars) then
    CErrors.user_err
      Pp.(str "Not all pattern variables appear in the pattern.");
    Vars.universes_of_constr rhs |> Univ.Level.Set.iter (fun lvl -> lvl |> Univ.Level.var_index |> Option.iter (fun lvli ->
    if not (Int.Map.mem lvli invtblu) then
      CErrors.user_err
        Pp.(str "Universe level variable" ++ Univ.Level.pr lvl ++ str " appears in rhs but does not appear in the pattern.")
  ));
  let usubst = Univ.Instance.of_array (Array.init nvarus (fun i -> Univ.Level.var (Option.default i (Int.Map.find_opt i invtblu)))) in
  Format.print_flush ();
  head_constant lhs_pat, { lhs_pat = lhs_pat; rhs = rename (0, invtbl) (Vars.subst_instance_constr usubst rhs); }

