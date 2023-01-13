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
open Constr

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
  | PCase     of inductive * rewrite_arg_pattern * rewrite_pattern * rewrite_arg_pattern array
  | PProj     of Projection.t * rewrite_pattern

type t = {
  lhs_pat : rewrite_pattern;
  rhs : constr;
}

val pattern_of_constr : constr -> rewrite_pattern

val safe_pattern_of_constr : 'a -> int -> constr -> int * rewrite_pattern
