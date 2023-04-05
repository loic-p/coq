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

let rec head_pattern_of_constr t = kind t |> function
  | Const (c, u) -> PHSymbol (c, mask_of_instance u)
  | Sort s -> PHSort (sort_pattern_of_sort s)
  | Ind (ind, u) -> PHInd (ind, mask_of_instance u)
  | Construct (c, u) -> PHConstr (c, mask_of_instance u)
  | Int i -> PHInt i
  | Float f -> PHFloat f
  | Lambda _ ->
      let (ntys, b) = Term.decompose_lambda t in
      let ptys = Array.of_list (List.rev_map (snd %> arg_pattern_of_constr) ntys) in
      let pbod = app_pattern_of_constr (Array.length ptys) b in
      PHLambda (ptys, pbod)
  | Prod _ ->
      let (ntys, b) = Term.decompose_prod t in
      let ptys = Array.of_list (List.rev_map (snd %> arg_pattern_of_constr) ntys) in
      let pbod = app_pattern_of_constr (Array.length ptys) b in
      PHProd (ptys, pbod)
  | _ -> assert false

and arg_pattern_of_constr t = kind t |> function
  | Rel _ -> APHole
  | _ -> APRigid (rigid_arg_pattern_of_constr t)
and rigid_arg_pattern_of_constr t = kind t |> function
  | App (f, args) -> APApp (rigid_arg_pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | _ -> APHead (head_pattern_of_constr t)

and app_pattern_of_constr n t =
  let f, args = decompose_appvect t in
  let nargs = Array.length args in
  assert (nargs >= n);
  let remargs, _ = Array.chop (nargs - n) args in
  arg_pattern_of_constr (mkApp (f, remargs))

let app_pattern_of_constr' p = app_pattern_of_constr (Array.length (fst p)) (snd p)

let rec pattern_of_constr t = kind t |> function
  | Const (c, u) -> PHead (c, mask_of_instance u)
  | App (f, args) -> PApp (pattern_of_constr f, Array.map arg_pattern_of_constr args)
  | Case (ci, u, _, p, _, c, brs) ->
      PCase (ci.ci_ind, mask_of_instance u, app_pattern_of_constr' p, pattern_of_constr c, Array.map app_pattern_of_constr' brs)
  | Proj (p, c) -> PProj (p, pattern_of_constr c)
  | _ -> assert false

type state = (int * int Int.Map.t * int Int.Map.t) * (int * int Int.Map.t)

let update_invtbl i curvar tbl eqs =
  Int.Map.find_opt i tbl |> function
  | None -> succ curvar, Int.Map.add i curvar tbl, eqs
  | Some k when k = curvar -> succ curvar, tbl, eqs
  | Some k -> assert (k < curvar) ; succ curvar, tbl, Int.Map.add curvar k eqs

let update_shft_invtbl shft (state, stateu) i =
  let (curvar, invtbl, eqs) = state in
  if i <= shft then
    CErrors.user_err
      Pp.(str "Variable "
        ++ Constr.debug_print (of_kind (Rel i))
        ++ str" not available from toplevel.");
  update_invtbl (i-shft) curvar invtbl eqs, stateu

let update_invtblu1 lvl curvaru tbl =
  succ curvaru, tbl |> Int.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some k ->
        CErrors.user_err
          Pp.(str "Universe variable "
            ++ Univ.Level.(pr (var lvl))
            ++ str" already taken for hole " ++ int k
            ++ str" but used here for hole " ++ int curvaru
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

let rec safe_head_pattern_of_constr env shft state t = kind t |> function
  | Const (c, u) when Environ.is_symbol env c ->
      let state, mask = update_invtblu state u in
      state, PHSymbol (c, mask)
  | Sort s ->
      let state, ps = safe_sort_pattern_of_sort state s in
      state, PHSort ps
  | Ind (ind, u) ->
      let state, mask = update_invtblu state u in
      state, PHInd (ind, mask)
  | Construct (c, u) ->
      let state, mask = update_invtblu state u in
      state, PHConstr (c, mask)
  | Int i -> state, PHInt i
  | Float f -> state, PHFloat f
  | Lambda _ ->
      let (ntys, b) = Term.decompose_lambda t in
      let tys = Array.of_list (List.rev_map snd ntys) in
      let state, ptys = Array.fold_left_map_i (fun i state ty -> safe_arg_pattern_of_constr env (shft+i) state ty) state tys in
      let state, pbod = safe_app_pattern_of_constr env shft state (Array.length tys) b in
      state, PHLambda (ptys, pbod)
  | Prod _ ->
      let (ntys, b) = Term.decompose_prod t in
      let tys = Array.of_list (List.rev_map snd ntys) in
      let state, ptys = Array.fold_left_map_i (fun i state ty -> safe_arg_pattern_of_constr env (shft+i) state ty) state tys in
      let state, pbod = safe_app_pattern_of_constr env shft state (Array.length tys) b in
      state, PHProd (ptys, pbod)
  | _ -> CErrors.user_err Pp.(str "Subterm not recognised as head_pattern: " ++ Constr.debug_print t)


and safe_arg_pattern_of_constr env shft state t = kind t |> function
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
  | _ ->
    let state, p = safe_head_pattern_of_constr env shft state t in
    state, APHead p

and safe_app_pattern_of_constr env shft state n t =
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
  safe_arg_pattern_of_constr env (n + shft) state (mkApp (f, remargs))

let safe_app_pattern_of_constr' env shft state p = safe_app_pattern_of_constr env shft state (Array.length (fst p)) (snd p)


let rec safe_pattern_of_constr env shft state t = kind t |> function
  | Const (c, u) ->
      (match (Environ.lookup_constant c env).const_body with
      | Def _ | OpaqueDef _ | Primitive _ | Undef _ ->
          CErrors.user_err Pp.(str "Constant " ++ Constant.print c ++ str" used in pattern is not a symbol.")
      | Symbol _ -> ());
      let state, mask = update_invtblu state u in
      state, PHead (c, mask)
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
  | PHead (c, _) -> c
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

let rec debug_string_of_equations eqs =
  if Int.Map.is_empty eqs then
    Pp.str "None."
  else
    Int.Map.fold (fun lhs rhs s -> Pp.(str"(" ++ int lhs ++ str" = " ++ int rhs ++ str") " ++ s)) eqs (Pp.str "")

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
  let ((seen_vars, invtbl, lhs_eqs), (_, invtblu)), lhs_pat =
    safe_pattern_of_constr env 0 ((1, Int.Map.empty, Int.Map.empty), (0, Int.Map.empty)) lhs
  in
  let neqs = Int.Map.cardinal lhs_eqs in
  let seen_vars = pred seen_vars in
  (* Rels begin at 1 *)
  if not (seen_vars = nvars + neqs) then
    CErrors.user_err
      Pp.(str "Not all pattern variables appear in the pattern.");
  Vars.universes_of_constr rhs |> Univ.Level.Set.iter (fun lvl -> lvl |> Univ.Level.var_index |> Option.iter (fun lvli ->
    if not (Int.Map.mem lvli invtblu) then
      CErrors.user_err
        Pp.(str "Universe level variable" ++ Univ.Level.pr lvl ++ str " appears in rhs but does not appear in the pattern.")
  ));
  let usubst = Univ.Instance.of_array (Array.init nvarus (fun i -> Univ.Level.var (Option.default i (Int.Map.find_opt i invtblu)))) in
  Format.print_flush ();
  (* debugging *)
  Pp.(Feedback.msg_info (str "Equation successfully added.\nThere are " ++ int seen_vars ++ str" holes and "
                         ++ int nvars ++ str" variables."
                         ++ str "\nRight side after renaming of the holes: "
                         ++ Constr.debug_print (rename (0, invtbl) (Vars.subst_instance_constr usubst rhs))
                         ++ str "\nThe equations on holes are as follows: "
                         ++ debug_string_of_equations lhs_eqs)) ;
  head_constant lhs_pat, { lhs_pat = lhs_pat; lhs_eqs = lhs_eqs; rhs = rename (0, invtbl) (Vars.subst_instance_constr usubst rhs); }
