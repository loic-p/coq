(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Interpreting a rewrite rule from a constr *)

type state = (int * int Evar.Map.t) * (int * int Int.Map.t) * (int * bool list * int Int.Map.t)

val safe_pattern_of_constr :
  loc:Loc.t option -> Environ.env -> Evd.evar_map -> Sorts.Quality.t Sorts.QVar.Map.t * Univ.universe_level_subst
  -> int -> state -> Constr.constr -> state * Declarations.head_elimination
