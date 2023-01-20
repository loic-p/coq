(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let declare id entry =
  let _ : Constant.t =
    Declare.declare_constant ~name:id ~kind:Decls.IsSymbol (Declare.SymbolEntry entry)
  in
  Flags.if_verbose Feedback.msg_info Pp.(Id.print id ++ str " is declared")

let preprocess_symbols l =
  let open Vernacexpr in
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a symbol is not allowed in sections.");
  let no_udecl_msg = Pp.str "Symbols do not suport universe polymorphism." in
  List.iter (fun (coe, (idl, c)) -> List.iter (function ({CAst.loc; _}, Some _) -> CErrors.user_err ?loc no_udecl_msg | (_, None) -> ()) idl) l;
  let no_coercion_msg = Pp.(str "Cannot deal with coercions in symbols") in
  List.iter (function AddCoercion, (({CAst.loc; _}, _) :: _, _) -> CErrors.user_err ?loc no_coercion_msg | AddCoercion, _ -> assert false | _ -> ()) l;
  List.concat_map (fun (coe, (idl, c)) -> List.map (fun (id, _) -> id, c) idl) l

let do_symbol (id, typ) =
  if Dumpglob.dump () then Dumpglob.dump_definition id false "symb";
  let id = id.CAst.v in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, (typ, impls) =
    Constrintern.(interp_type_evars_impls ~impls:empty_internalization_env)
      env evd typ
  in
  Pretyping.check_evars_are_solved ~program_mode:false env evd;
  let evd = Evd.minimize_universes evd in
  let uvars = EConstr.universes_of_constr evd typ in
  let evd = Evd.restrict_universe_context evd uvars in
  let typ = EConstr.to_constr evd typ in
  let univs = Evd.check_univ_decl ~poly:false evd UState.default_univ_decl in
  let entry = Declare.symbol_entry ~univs typ in
  declare id entry

let do_symbols : (Constrexpr.ident_decl list * Constrexpr.constr_expr) Vernacexpr.with_coercion list -> unit =
  fun l -> l
  |> preprocess_symbols
  |> List.iter do_symbol
