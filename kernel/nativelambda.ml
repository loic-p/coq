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
open Esubst
open Constr
open Genlambda

(** This file defines the lambda code generation phase of the native compiler *)

type lambda = Nativevalues.t Genlambda.lambda

(*s Constructors *)

(** Simplification of lambda expression *)

(* TODO: make the VM and native agree *)
let can_subst lam =
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Lval _ | Lsort _ | Lind _ | Llam _
  | Levar _ -> true
  | _ -> false

let simplify subst lam = simplify can_subst subst lam

let is_value lc =
  match lc with
  | Lval _ | Lint _ | Luint _ | Lfloat _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lval v -> v
  | Lint tag -> Nativevalues.mk_int tag
  | Luint i -> Nativevalues.mk_uint i
  | Lfloat f -> Nativevalues.mk_float f
  | _ -> raise Not_found

let as_value tag args =
  if Array.for_all is_value args then
    let dummy_val = Obj.magic 0 in
    let args =
      (* Don't simplify this to Array.map, cf. the related comment in
         function eval_to_patch, file kernel/csymtable.ml *)
      let a = Array.make (Array.length args) dummy_val in
      Array.iteri (fun i v -> a.(i) <- get_value v) args; a in
    Some (Nativevalues.mk_block tag args)
  else None

let is_lazy t =
  match Constr.kind t with
  | App _ | LetIn _ | Case _ | Proj _ -> true
  | _ -> false

module Val =
struct
  open Declarations
  type value = Nativevalues.t
  let as_value = as_value
  let check_inductive _ _ = ()
  let get_constant knu cb = match cb.const_body with
  | Def body -> if is_lazy body then mkLapp Lforce [|Lconst knu|] else Lconst knu
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> assert false
end

module Lambda = Genlambda.Make(Val)

let lambda_of_constr env sigma c =
  let lam = Lambda.lambda_of_constr env sigma c in
  simplify (subs_id 0) lam
