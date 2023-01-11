(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Declarations

val pattern_of_constr : constr -> rewrite_pattern

type state

val safe_pattern_of_constr : Environ.env -> int -> state -> constr -> state * rewrite_pattern

val rule_of_constant : Environ.env -> Names.Constant.t -> Names.Constant.t * rewrite_rule
