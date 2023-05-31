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
open Environ
open Evd

(** From an inductive type, generates a list of observational equalities
    that *)

val duplicate_context : (constr, constr) Context.Rel.pt -> (constr, constr) Context.Rel.pt

val declare_inductive_obs_eqs : Names.MutInd.t -> unit

val declare_inductive_casts : Names.MutInd.t -> unit

val declare_inductive_rewrite_rules : Names.MutInd.t -> unit

val declare_inductive_observational_data : Names.MutInd.t -> unit

val declare_observational_equality :
  (univs:UState.named_universes_entry
   -> name:Id.t
   -> Constr.t
   -> Constant.t) ref
