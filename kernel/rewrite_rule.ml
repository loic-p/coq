open Util
open Names
open Constr

type case_info = { ci_ind: inductive }

type rewrite_arg_pattern =
  | APHole
  (* | APHoleIgnored *)
  | APApp     of rewrite_arg_pattern * rewrite_arg_pattern array
  | APInd     of inductive
  | APConstr  of constructor
  | APInt     of Uint63.t
  | APFloat   of Float64.t

type rewrite_pattern =
  | PApp      of rewrite_pattern * rewrite_arg_pattern array
  | PConst    of Constant.t  (* Symbol *)
  | PCase     of case_info * rewrite_arg_pattern * rewrite_pattern * rewrite_arg_pattern array
  | PProj     of Projection.t * rewrite_pattern


type rewrite_rule = {
  lhs_pat : rewrite_pattern;
  rhs : constr;
}

type t = rewrite_rule

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
  | Case (ci, _, _, p, _, c, brs) -> PCase ({ci_ind = ci.Constr.ci_ind}, arg_pattern_of_constr (snd p), pattern_of_constr c, Array.map (fun (_, br) -> arg_pattern_of_constr br) brs)
  | Proj (p, c) -> PProj (p, pattern_of_constr c)
  | _ -> assert false

let lookup_constant _env _c = assert false

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
      (match lookup_constant env c with
      | Declarations.Def _ | Declarations.OpaqueDef _ | Declarations.Primitive _ ->
          CErrors.anomaly Pp.(str "Constant " ++ Constant.print c ++ str" used in pattern has a body.")
      | Declarations.Undef _ -> ());
      nvar, PConst c
  | App (f, args) ->
      let nvar, pf = safe_pattern_of_constr env nvar f in
      let nvar, pargs = Array.fold_left_map safe_arg_pattern_of_constr nvar args in
      nvar, PApp (pf, pargs)
  | Case (ci, _, _, (_, ret), _, c, brs) ->
      let nvar, pc = safe_pattern_of_constr env nvar c in
      let nvar, pret = safe_arg_pattern_of_constr nvar ret in
      let nvar, pbrs = Array.fold_left_map (fun nvar (_, br) -> safe_arg_pattern_of_constr nvar br) nvar brs in
      nvar, PCase ({ci_ind = ci.Constr.ci_ind}, pret, pc, pbrs)
  | Proj (p, c) ->
      let nvar, pc = safe_pattern_of_constr env nvar c in
      nvar, PProj (p, pc)
  | _ -> CErrors.anomaly Pp.(str "Subterm not recognised as pattern" ++ Constr.debug_print t)
