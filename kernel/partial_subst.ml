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

module NoDupArray : sig
  (** Like a Parray, but the old pointers are invalidated instead of updated *)
  type 'a t
  val make : int -> 'a t

  val get : 'a t -> int -> 'a option

  val add : int -> 'a -> 'a t -> 'a t

  val add_or_conv : ('a -> 'a -> bool) -> int -> 'a -> 'a t -> 'a t option

  val to_array : 'a t -> 'a array

  val pr : ('a -> Pp.t) -> 'a t -> Pp.t
end = struct
  type 'a t = 'a option array * bool ref

  let make n = Array.make n None, ref true

  let get a n =
    (fst a).(n)

  let invalidate b =
    if not !b then
      CErrors.anomaly Pp.(str "Tried to reuse invalidated NoDupArray.");
    b := false

  let add i e (a, b) =
    invalidate b;
    begin match a.(i) with
    | None -> a.(i) <- Some e
    | Some _ -> CErrors.anomaly Pp.(str "Tried to add duplicate in NoDupArray.")
    end;
    a, ref true

  let add_or_conv conv i e (a, b) =
    invalidate b;
    begin match a.(i) with
    | None -> a.(i) <- Some e; Some (a, ref true)
    | Some e0 -> if conv e e0 then Some (a, ref true) else None
    end

  let to_array (a, b) =
    invalidate b;
    Array.map (function Some e -> e | None -> CErrors.anomaly Pp.(str "Tried to cast non-full NoDupArray.")) a

  let pr pre (a, _) =
    Pp.(str"[|"++prvect_with_sep pr_semicolon (function None -> str "\u{2205}" (* Empty set *) | Some e -> pre e) a++str"|]")
end

type ('term, 'quality, 'univ) t =
  'term NoDupArray.t * 'quality NoDupArray.t * 'univ NoDupArray.t

let make (m, n, p) =
  (NoDupArray.make m, NoDupArray.make n, NoDupArray.make p)

let get_term (ts, _, _) n =
  NoDupArray.get ts (n-1)

let get_quality (_, qs, _) n =
  NoDupArray.get qs n

let get_univ (_, _, us) n =
  NoDupArray.get us n

let add_term_or_conv conv i t (ts, qs, us) =
  match NoDupArray.add_or_conv conv i t ts with
  | Some ts -> Some (ts, qs, us)
  | None -> None

let maybe_add_term_or_conv conv io t tqus =
  match io with
  | Some i -> add_term_or_conv conv i t tqus
  | None -> Some tqus

let add_quality_or_conv conv i t (ts, qs, us) =
  match NoDupArray.add_or_conv conv i t qs with
  | Some qs -> Some (ts, qs, us)
  | None -> None

let maybe_add_quality_or_conv conv io t tqus =
  match io with
  | Some i -> add_quality_or_conv conv i t tqus
  | None -> Some tqus

let add_univ_or_conv conv i t (ts, qs, us) =
  match NoDupArray.add_or_conv conv i t us with
  | Some us -> Some (ts, qs, us)
  | None -> None

let maybe_add_univ_or_conv conv io t tqus =
  match io with
  | Some i -> add_univ_or_conv conv i t tqus
  | None -> Some tqus

let add_term i t tqus : ('t, 'q, 'u) t =
  on_pi1 (NoDupArray.add (i-1) t) tqus

let maybe_add_term io t tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_term i t) io tqus

let add_quality i q tqus : ('t, 'q, 'u) t =
  on_pi2 (NoDupArray.add i q) tqus

let maybe_add_quality io q tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_quality i q) io tqus

let add_univ i u tqus : ('t, 'q, 'u) t =
  on_pi3 (NoDupArray.add i u) tqus

let maybe_add_univ io u tqus : ('t, 'q, 'u) t =
  Option.fold_right (fun i -> add_univ i u) io tqus

let to_arrays (ts, qs, us : _ t) =
  (NoDupArray.to_array ts, NoDupArray.to_array qs, NoDupArray.to_array us)

let pr prt prq pru (ts, qas, us) =
  Pp.(NoDupArray.pr prt ts ++ pr_comma () ++ NoDupArray.pr prq qas ++ pr_comma () ++ NoDupArray.pr pru us)
