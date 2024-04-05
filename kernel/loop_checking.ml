open Univ

let _, debug_updates = CDebug.create_full ~name:"loop-checking-updates" ()

(* let debug_check_fwd, _ = CDebug.create_full ~name:"loop-checking-fix-check" () *)

let _debug_loop_checking_partition, debug_loop_partition = CDebug.create_full ~name:"loop-checking-partition" ()
let debug_loop_checking_invariants, debug_invariants = CDebug.create_full ~name:"loop-checking-invariants" ()
let _debug_loop_checking_invariants_all, debug_invariants_all = CDebug.create_full ~name:"loop-checking-invariants-all" ()
let _debug_loop_checking_model, debug_model = CDebug.create_full ~name:"loop-checking-model" ()
let _debug_loop_checking_clauses, _debug_clauses = CDebug.create_full ~name:"loop-checking-clauses" ()
(* let _debug_loop_checking_bwdclauses, debug_bwdclauses = CDebug.create_full ~name:"loop-checking-bwdclauses" () *)
let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()
let _debug_loop_checking_loop, debug_loop = CDebug.create_full ~name:"loop-checking-loop" ()
let _debug_loop_checking_check_model, debug_check_model = CDebug.create_full ~name:"loop-checking-check-model" ()
let _debug_loop_checking_check, _debug_check = CDebug.create_full ~name:"loop-checking-check" ()

let _debug_loop_checking_global_flag, debug_global = CDebug.create_full ~name:"loop-checking-global" ()


(* let _ = CDebug.set_flag debug_loop_checking_check true *)

let _time prefix =
  let accum = ref 0. in
  fun f x ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
    res
  else f x

let time2 prefix f =
  let accum = ref 0. in
  let calls = ref 0 in
  fun x y ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    incr calls;
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s" ++
      str " in " ++ int !calls ++ str " calls") in
    res
  else f x y

let time3 prefix f =
  let accum = ref 0. in
  fun x y z ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y z in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s") in
    res
  else f x y z

let time4 prefix f =
  let accum = ref 0. in
  let calls = ref 0 in
  fun x y z w ->
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x y z w in
    let stop = Unix.gettimeofday () in
    let time = stop -. start in
    let () = accum := time +. !accum in
    incr calls;
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real time ++ str "s") in
    let () = debug_timing Pp.(fun () -> prefix ++ str " total execution time is: " ++ Pp.real !accum ++ str "s" ++
      str " in " ++ int !calls ++ str " calls") in
    res
  else f x y z w


module Index :
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
  type table
  val empty : table
  val fresh : Level.t -> table -> t * table
  val mem : Level.t -> table -> bool
  val find : Level.t -> table -> t
  val repr : t -> table -> Level.t
  val dom : table -> Level.Set.t
  val hash : t -> int
end =
struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  module Set = Int.Set
  module Map = Int.Map

  type table = {
    tab_len : int;
    tab_fwd : Level.t Int.Map.t;
    tab_bwd : int Level.Map.t
  }

  let empty = {
    tab_len = 0;
    tab_fwd = Int.Map.empty;
    tab_bwd = Level.Map.empty;
  }
  let mem x t = Level.Map.mem x t.tab_bwd
  let find x t = Level.Map.find x t.tab_bwd
  let repr n t = Int.Map.find n t.tab_fwd

  let fresh x t =
    let () = assert (not @@ mem x t) in
    let n = t.tab_len in
    n, {
      tab_len = n + 1;
      tab_fwd = Int.Map.add n x t.tab_fwd;
      tab_bwd = Level.Map.add x n t.tab_bwd;
    }

  let dom t = Level.Map.domain t.tab_bwd

  let hash x = x
end

module PMap = Index.Map
module PSet = Index.Set

module NeList =
struct

  type 'a t =
    | Tip of 'a
    | Cons of 'a * 'a t

  let tip x = Tip x
  (* let cons x xs = Cons (x, xs) *)

  let map f (x : 'a t) : 'b t =
    let rec aux l =
      match l with
      | Tip x -> Tip (f x)
      | Cons (x, xs) ->
        let x' = f x in
        let xs' = aux xs in
        Cons (x', xs')
    in aux x

  let smart_map f (x : 'a t) : 'a t =
    let rec aux l =
      match l with
      | Tip x -> let x' = f x in if x' == x then l else Tip x'
      | Cons (x, xs) -> let x' = f x in
        let xs' = aux xs in
        if x' == x && xs' == xs then l
        else Cons (x', xs')
    in aux x

  let fold (f : 'a -> 'b -> 'b) (x : 'a t) (acc : 'b) : 'b =
    let rec aux acc l =
      match l with
      | Tip x -> f x acc
      | Cons (hd, tl) -> aux (f hd acc) tl
    in aux acc x

  let fold_ne (f : 'a -> 'b -> 'b) (g : 'a -> 'b) (x : 'a t) : 'b =
    let rec aux l =
      match l with
      | Tip x -> g x
      | Cons (hd, tl) -> f hd (aux tl)
    in aux x

  let fold_map (f : 'a -> 'b -> 'a * 'b) (x : 'a t) (acc : 'b) : 'a t * 'b =
    let rec aux acc l =
      match l with
      | Tip x -> let x', res = f x acc in Tip x', res
      | Cons (hd, tl) -> let hd', res = f hd acc in
        let tl', res = aux res tl in
        Cons (hd', tl'), res
    in aux acc x

  let iter f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd; aux tl
    in aux x

  let for_all f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd && aux tl
    in aux x

  let exists f x =
    let rec aux l =
      match l with
      | Tip x -> f x
      | Cons (hd, tl) -> f hd || aux tl
    in aux x

  let equal f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> false
      | Tip _, Cons _ -> false
      | Cons (hd, tl), Cons (hd', tl') ->
        f hd hd' && aux tl tl'
    in aux x y

  let compare f x y =
    let rec aux l l' =
      match l, l' with
      | Tip x, Tip y -> f x y
      | Cons _, Tip _ -> 1
      | Tip _, Cons _ -> -1
      | Cons (hd, tl), Cons (hd', tl') ->
        match f hd hd' with
        | 0 -> aux tl tl'
        | c -> c
    in aux x y

  let rec of_list = function
    | [] -> assert false
    | [hd] -> Tip hd
    | hd :: tl -> Cons (hd, of_list tl)

  let rec to_list = function
    | Tip hd -> [hd]
    | Cons (hd, tl) -> hd :: to_list tl

  let _filter_map_same f l =
    let rec aux l =
      match l with
      | Tip hd ->
        begin match f hd with
        | None -> None
        | Some hd' -> if hd == hd' then Some l else Some (Tip hd')
        end
      | Cons (hd, tl) ->
        match f hd with
        | Some hd' ->
          let tl' = aux tl in
          begin match tl' with
            | None -> Some (Tip hd')
            | Some tl' ->
              if hd == hd' && tl == tl' then Some l
              else Some (Cons (hd', tl'))
            end
        | None -> aux tl
    in aux l

  let rec append xs ys =
    match xs with
    | Tip x -> Cons (x, ys)
    | Cons (x, xs) -> Cons (x, append xs ys)

  let map_splice (f : 'a -> 'a t option) (l : 'a t) : 'a t =
    let rec aux l =
      match l with
      | Tip x -> (match f x with Some l -> l | None -> l)
      | Cons (x, xs) ->
        match f x with
        | Some l -> append l (aux xs)
        | None -> Cons (x, aux xs)
    in aux l

  let _mem_assq x = exists (fun y -> fst y == x)

  let _assq x l =
    let rec aux l =
      match l with
      | Tip (hd, v) -> if hd == x then v else raise_notrace Not_found
      | Cons ((hd, v), tl) ->
        if hd == x then v else aux tl
    in aux l

  let _find f l =
    let rec aux l =
      match l with
      | Tip (hd, v) -> if f hd then v else raise_notrace Not_found
      | Cons ((hd, v), tl) ->
        if f hd then v else aux tl
    in aux l

  let _head x =
    match x with
    | Tip hd -> hd
    | Cons (hd, _) -> hd

  let pr_with_sep sep prelt =
    let open Pp in
    let rec aux l =
      match l with
      | Tip x -> prelt x
      | Cons (hd, tl) -> prelt hd ++ sep () ++ aux tl
    in aux

  let filter p l =
    let rec aux l =
      match l with
      | Tip x -> if p x then Some l else None
      | Cons (hd, tl) ->
        let phd = p hd in
        match aux tl with
        | None -> if phd then Some (Tip hd) else None
        | Some tl' ->
          if phd then
            if tl == tl' then Some l
            else Some (Cons (hd, tl'))
          else Some tl'
    in aux l

  let uniq eq l =
    let rec aux l =
      match l with
      | Tip _ -> l
      | Cons (hd, tl) ->
        if exists (fun y -> eq hd y) tl then aux tl
        else Cons (hd, aux tl)
    in aux l

end

module Premises =
struct

  module Premise =
  struct
    type t = Index.t * int

    let equal x y : bool =
      let (idx, k) = x in
      let (idx', k') = y in
      if Index.equal idx idx' then
        Int.equal k k'
      else false

    let compare x y : int =
      let (idx, k) = x in
      let (idx', k') = y in
      match Index.compare idx idx' with
      | 0 -> Int.compare k k'
      | x -> x

  end

  (* Invariant: sorted, non-empty *)
  type t = Premise.t NeList.t

  let _fold = NeList.fold

  let fold_ne = NeList.fold_ne

  let iter = NeList.iter
  let for_all = NeList.for_all
  let _exists = NeList.exists
  (* let _add prem (x : t) : t = CList.merge_set Premise.compare [prem] x *)
  (* let _union (x : t) (y : t) : t = CList.merge_set Premise.compare x y *)
  let compare : t -> t -> int = NeList.compare Premise.compare
  let equal : t -> t -> bool = NeList.equal Premise.equal

  (* let of_list = NeList.of_list *)

  let to_list = NeList.to_list

  let smart_map = NeList.smart_map
end

let pr_with f (l, n) =
  if Int.equal n 0 then f l
  else Pp.(f l ++ Pp.str"+" ++ int n)

module ClausesOf = struct
  module ClauseInfo = struct
    type t = int * Premises.t

    let _equal x y : bool =
      let (k, prems) = x in
      let (k', prems') = y in
      if Int.equal k k' then
        Premises.equal prems prems'
      else false

    let compare x y : int =
      let (k, prems) = x in
      let (k', prems') = y in
      match Int.compare k k' with
      | 0 -> Premises.compare prems prems'
      | x -> x

    (* let of_list (k, prems) = (k, Premises.of_list prems) *)

    let pr pr_pointint concl (k, prem) =
      let open Pp in
      hov 0 (prlist_with_sep (fun () -> str ",") pr_pointint (Premises.to_list prem) ++ str " → " ++ pr_pointint (concl, k))
  end

  module S = Set.Make(ClauseInfo)
  include S

  let pr pr_pointint concl cls =
    let open Pp in
    v 0 (prlist_with_sep spc (ClauseInfo.pr pr_pointint concl) (elements cls))

  (* Ocaml >= 4.11 has a more efficient version. *)
  let filter_map p l =
    fold (fun x acc ->
      match p x with
      | None ->  remove x acc
      | Some x' -> if x' == x then acc else add x' (remove x acc)) l l

  let shift n cls = if Int.equal n 0 then cls else map (fun (k, prems) -> (k + n, prems)) cls

end

type clause = Index.t * ClausesOf.t

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    clauses_bwd : ClausesOf.t; (* premises -> canon + k *)
    clauses_fwd : ClausesOf.t PMap.t (* canon + k, ... ->  concl + k' *) }

(* A Level.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of Index.t * int

type model = {
  entries : entry PMap.t;
  values : int PMap.t;
  canonical : int; (* Number of canonical nodes *)
  table : Index.table }

let empty_model = {
  entries = PMap.empty;
  values = PMap.empty;
  canonical = 0;
  table = Index.empty
}

module CN = struct
  type t = canonical_node
  let equal x y = x == y
  let hash x = Index.hash x.canon
  (* let compare x y = Index.compare x.canon y.canon *)
end
(* module CSet = CSet.Make(CN) *)

let enter_equiv m u v i =
  { entries = PMap.modify u (fun _ a ->
          match a with
          | Canonical _ -> Equiv (v, i)
          | _ -> assert false) m.entries;
    canonical = m.canonical - 1;
    values = PMap.remove u m.values;
    table = m.table }

let change_equiv entries u (v, i) =
  PMap.modify u (fun _ a ->
      match a with
      | Canonical _ -> assert false
      | Equiv _ -> Equiv (v, i)) entries

let change_node m n =
  { m with entries =
    PMap.modify n.canon
      (fun _ a ->
        match a with
        | Canonical _ -> Canonical n
        | _ -> assert false)
      m.entries }

(* canonical representative : we follow the Equiv links *)
let rec repr m u =
  match PMap.find u m.entries with
  | Equiv (v, k) -> let (can, k') = repr m v in (can, k' + k)
  | Canonical arc -> (arc, 0)

let repr_expr m (u, k) =
  let can, k' = repr m u in
  (can.canon, k + k')

let repr_expr_can m (u, k) =
  let can, k' = repr m u in
  (can, k + k')

let repr_can_expr m (u, k) =
  let can, k' = repr m u.canon in
  (can, k + k')

(* canonical representative with path compression : we follow the Equiv links
  and updated them as needed *)
let repr_compress_entries entries u =
  let rec aux u =
    match PMap.find u entries with
    | Equiv (v, k) ->
      let entries, (can, k') = aux v in
      if Index.equal v can.canon then entries, (can, k + k')
      else change_equiv entries u (can.canon, k + k'), (can, k + k')
    | Canonical can -> entries, (can, 0)
  in aux u

let repr_compress m u =
  let entries, can = repr_compress_entries m.entries u in
  { m with entries }, can

let repr_node m u =
  try repr m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined" ++
      (if Index.mem u m.table then str" (index found)" else str " (index not found in " ++ Level.Set.pr Level.raw_pr (Index.dom m.table) ++ str")") ++ str".")

let repr_node_expr m (u, k) =
  let (can, k') = repr_node m u in (can, k + k')

let repr_compress_node m u =
  try repr_compress m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Level.raw_pr u ++ str" undefined.")

let pr_expr = LevelExpr.pr Level.raw_pr

let pr_raw_index_point m idx =
  try pr_expr (Index.repr idx m.table, 0)
  with Not_found -> Pp.str"<point not in table>"

let pr_index_point m idx =
  let (idx, k) = try let can, k = repr m idx in (can.canon, k) with Not_found -> (idx, 0) in
  try pr_expr (Index.repr idx m.table, k)
  with Not_found -> Pp.str"<point not in table>"

let pr_pointint m = pr_with (pr_index_point m)

let _pr_clause_info m concl cl = ClausesOf.ClauseInfo.pr (pr_pointint m) concl cl

let pr_clauses_of m = ClausesOf.pr (pr_pointint m)

let repr_premise m (idx, k as x) =
  let idx', k' = repr m idx in
  if Index.equal idx idx'.canon then x
  else (idx'.canon, k + k')

let repr_premises m (x : Premises.t) : Premises.t =
  Premises.smart_map (repr_premise m) x

let repr_clauses_of m ((k, prems as x) : ClausesOf.ClauseInfo.t) : ClausesOf.ClauseInfo.t =
  let prems' = repr_premises m prems in
  if prems' == prems then x
  else (k, prems')

let repr_clauses_of m x =
  ClausesOf.map (repr_clauses_of m) x

module ClausesOfRepr =
struct
  open ClausesOf
  let premise_equal_upto m (idx, k) (idx', k') =
    Int.equal k k' && repr m idx == repr m idx'

  let premises_equal_upto m prems prems' =
    NeList.equal (premise_equal_upto m) prems prems'

  let premises_equal_upto m (k, prems) (k', prems') =
    k <= k' &&
    premises_equal_upto m prems prems'

  let mem_upto m (cl : ClauseInfo.t) cls =
    let eq cl' = premises_equal_upto m cl cl' in
    exists eq cls

  let subset_upto m cls cls' =
    for_all (fun cl -> mem_upto m cl cls') cls

  let expr_eq (idx, k) (idx', k') =
    Index.equal idx idx' && Int.equal k k'

  let filter_trivial_clause m l (k, prems) =
    (* Canonicalize the premises *)
    let prems' = NeList.map (repr_expr m) prems in
     (* Filter out ..., u + k, ... -> u trivial clause *)
    if NeList.exists (fun (can, k') -> Index.equal can l && k' >= k) prems' then None
    else
      (* Simplify (u + k, ... u + k -> v + k') clauses to have a single premise by universe *)
      let prems' = NeList.uniq expr_eq prems' in
      Some (k, prems')

  let filter_trivial (m : model) l kprem =
    filter_map (filter_trivial_clause m l) kprem

  let union_upto m idx x y =
    union (filter_trivial m idx x) (filter_trivial m idx y)
end

module ClausesBackward =
struct
  type t = ClausesOf.t PMap.t

  let add ((idx, kprem) : clause) clauses : t =
    PMap.update idx
      (fun cls ->
        match cls with
        | None -> Some kprem
        | Some cls -> Some (ClausesOf.union kprem cls))
      clauses

  (* let union (clauses : t) (clauses' : t) : t = *)
    (* PMap.fold (fun idx cls acc -> add (idx, cls) acc) clauses clauses' *)

  let _union (clauses : t) (clauses' : t) : t =
    let merge _idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' -> Some (ClausesOf.union cls cls')
    in
    PMap.merge merge clauses clauses'

  let cardinal (cls : t) : int =
    PMap.fold (fun _ cls card ->
      ClausesOf.cardinal cls + card)
      cls 0

  let empty = PMap.empty
  let _is_empty = PMap.is_empty

  let singleton cl = add cl empty

  let fold = PMap.fold


  let find idx clauses : ClausesOf.t =
    try PMap.find idx clauses
    with Not_found -> ClausesOf.empty

  let _add_upto (m : model) (l, kprem as cl : clause) (cls : t) : t =
    if ClausesOfRepr.subset_upto m kprem (find l cls) then cls
    else add cl cls

  let reindex m (clauses : t) : t =
    PMap.fold (fun idx clsof acc ->
      let idx', k = repr m idx in
      if Index.equal idx'.canon idx then acc
      else
        let clsof = ClausesOf.shift k clsof in
        let acc = PMap.update idx'.canon (function None -> Some clsof | Some clsof' -> Some (ClausesOf.union clsof clsof')) acc in
        PMap.remove idx acc)
      clauses clauses

  let pr m (cls : t) =
    let open Pp in
    PMap.fold (fun concl cls acc -> pr_clauses_of m concl cls ++ spc () ++ acc) cls (Pp.mt())

  let union_upto (m : model) (clauses : t) (clauses' : t) : t =
    let merge idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | None, Some _ -> cls'
      | Some _, None -> cls
      | Some cls, Some cls' ->
        Some (ClausesOfRepr.union_upto m idx cls cls')
    in
    let iclauses = reindex m clauses
    and iclauses' = reindex m clauses' in
    PMap.merge merge iclauses iclauses'

  let repr m (clauses : t) : t =
    PMap.fold (fun idx clsof acc ->
      let idx', k = repr m idx in
      let clsof' = repr_clauses_of m clsof in
      if Index.equal idx'.canon idx && clsof' == clsof then acc
      else
        let clsof' = ClausesOf.shift k clsof' in
        let acc = PMap.update idx'.canon (function None -> Some clsof' | Some clsofo -> Some (ClausesOf.union clsofo clsof')) acc in
        PMap.remove idx acc)
      clauses clauses

  let _repr_clausesof m x =
    PMap.map (repr_clauses_of m) x

  let _partition (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t * t = PMap.partition p cls
  let _filter (p : Index.t -> ClausesOf.t -> bool) (cls : t) : t = PMap.filter p cls

end

let pr_clauses_bwd m (cls : ClausesBackward.t) = ClausesBackward.pr m cls
let _pr_clause_info m ((concl, kprem) : clause) =
  pr_clauses_of m concl kprem

type t = model

let eq_pointint m x x' =
  let (can, idx) = repr_expr m x
  and (can', idx') = repr_expr m x' in
  can == can' && Int.equal idx idx'


let simplify_can_premises p =
  let uniq = NeList.uniq (fun (can, k) (can', k') -> can == can' && Int.equal k k') p in
  NeList.map (fun (can, k) -> (can.canon, k)) uniq

let canonical_premises m = NeList.map (repr_expr_can m)

let check_invariants ~(required_canonical:Level.t -> bool) model =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      (* assert (PMap.mem idx model.values); *)
      let cls = can.clauses_bwd in
      ClausesOf.iter
        (fun (k, prems) ->
          (* prems -> can + k *)
          if not (k >= 0) then CErrors.user_err Pp.(str "A conclusion has negative weight") else ();
          let prems = simplify_can_premises (canonical_premises model prems) in
          let check_prem (l, lk) =
            if not (lk >= 0) then CErrors.user_err Pp.(str "A premise has negative weight") else ();
            assert (PMap.mem l model.entries);
            let lcan, _lk = repr_expr_can model (l, lk) in
            (* Ensure this backward clause of shape [max(... l + lk ... ) -> can + k] is registered as a forward clause for the premise l *)
            PMap.exists (fun idx kprem ->
              (* kprem = { (kconcl, max ( ... l' + lk' ... )) } -> idx *)
              let (can', shift) = repr model idx in
              can' == can &&
              ClausesOf.exists (fun (k', prems') -> Int.equal k k' && NeList.equal (eq_pointint model)
                prems (simplify_can_premises (canonical_premises model prems')))
                (ClausesOf.shift shift kprem))
              lcan.clauses_fwd
          in
          Premises.iter (fun kprem -> if (check_prem kprem) then () else
            CErrors.user_err Pp.(str"Clause " ++ pr_clauses_bwd model
              (ClausesBackward.singleton (can.canon, ClausesOf.singleton (k, prems))) ++ str" is not registered as a forward clauses for "
              ++ pr_pointint model kprem)) prems) cls;
      assert (PMap.for_all (fun _ kprems ->
          ClausesOf.for_all (fun (_, prems) ->
            NeList.exists (fun (idx', _) -> can == fst (repr model idx')) prems) kprems) can.clauses_fwd);
      incr n_canon
    | Equiv (idx', k) ->
      assert (k >= 0);
      assert (PMap.mem idx' model.entries);
      assert (Index.mem (Index.repr idx' model.table) model.table);
      (* The clauses should not mention aliases *)
      assert (not (required_canonical idx)))
    model.entries

let lift_opt f x y =
  match x, y with
  | Some x', Some y' -> Some (f x' y')
  | Some _, None -> x
  | None, Some _ -> y
  | None, None -> None

let max_opt = lift_opt max
let min_opt = lift_opt min

let model_max (m : model) : int option =
  PMap.fold (fun _ v acc -> max_opt (Some v) acc) m.values None

let model_min (m : model) : int option =
  PMap.fold (fun _ v acc -> min_opt (Some v) acc) m.values None

let clauses_cardinal (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can -> acc + ClausesOf.cardinal can.clauses_bwd)
    m.entries 0

let canonical_universes (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical _ -> succ acc)
    m.entries 0

let without_bound (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can ->
      let cls = can.clauses_bwd in
      if ClausesOf.is_empty cls then succ acc else acc)
    m.entries 0

let _pr_updates m s =
  let open Pp in
  prlist_with_sep spc (fun idx -> Level.raw_pr (Index.repr idx m.table)) (PSet.elements s)

let length_path_from m idx =
  let rec aux = function
    | Canonical _ -> 0
    | Equiv (idx, _) -> succ (aux (PMap.find idx m))
  in aux (PMap.find idx m)

let maximal_path m =
  PMap.fold (fun _ entry acc ->
    match entry with
    | Equiv (idx, _) -> max (succ (length_path_from m idx)) acc
    | Canonical _ -> acc) m 0

let statistics model =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" universes" ++
  str", " ++ int (canonical_universes model) ++ str" canonical universes" ++
  str ", maximal value in the model is " ++ pr_opt int (model_max model) ++
  str ", minimal value is " ++ pr_opt int (model_min model) ++
  str", " ++ int (clauses_cardinal model) ++ str" clauses." ++ spc () ++
  int (without_bound model) ++ str" canonical universes are not bounded above " ++
  str", " ++ int (maximal_path model.entries) ++ str" maximal path length in equiv nodes"

let pr_can m can =
  Level.raw_pr (Index.repr can.canon m.table)

let pr_clauses_all m =
  PMap.fold (fun p e acc ->
    match e with
    | Equiv (p', k) ->
      Pp.(pr_raw_index_point m p ++ str " = " ++ pr_with_incr (pr_raw_index_point m) (p',k) ++ spc () ++ acc)
    | Canonical can ->
      let bwd = can.clauses_bwd in
      Pp.(str"For " ++ pr_can m can ++ fnl () ++ pr_clauses_of m can.canon bwd ++ fnl () ++
        str"Forward" ++ spc () ++ pr_clauses_bwd m can.clauses_fwd ++ fnl () ++ acc))
    m.entries (Pp.mt ())

let debug_check_invariants m =
  if CDebug.get_flag debug_loop_checking_invariants then
    (debug_invariants_all Pp.(fun () -> str"Checking invariants, " ++ statistics m);
     debug_invariants_all (fun () -> pr_clauses_all m);
     try check_invariants ~required_canonical:(fun _ -> false) m
     with e ->
      debug_invariants Pp.(fun () -> str "Broken invariants on: " ++ pr_clauses_all m ++ CErrors.print e);
      raise e)

(* PMaps are purely functional hashmaps *)

exception Undeclared of Level.t

let canonical_value m c = PMap.find_opt c.canon m.values
let index_value m idx = PMap.find_opt idx m.values

let set_canonical_value m can v =
  { m with values = PMap.add can.canon v m.values }

let set_index_value m idx v =
  { m with values = PMap.add idx v m.values }

let _repr_canon m can =
  let bwd = repr_clauses_of m can.clauses_bwd in
  let fwd = ClausesBackward.repr m can.clauses_fwd in
  let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
  change_node m can, can

let add_opt o k =
  Option.map ((+) k) o

let model_value m l =
  let canon, k =
    try repr m l
    with Not_found -> raise (Undeclared (Index.repr l m.table))
  in add_opt (canonical_value m canon) k

exception VacuouslyTrue

let min_premise (m : model) prem =
  let g (l, k) = (match (model_value m l) with None -> raise VacuouslyTrue | Some v -> v) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

module CanSet =
struct
  type t = ClausesBackward.t PMap.t * int (* cardinal of the PMap.t *)

  let fold f (m, _cm)  acc = PMap.fold f m acc

  let add k v (w, cw) =
    let card = ref cw in
    let upd = function
      | None -> incr card; Some v
      | Some _ -> Some v
    in
    let pm = PMap.update k upd w in
    (pm, !card)

  let _singleton k v = (PMap.singleton k v, 1)

  let _mem x (w, _cw) = PMap.mem x w

  let empty = (PMap.empty, 0)

  let _is_empty (w, _cw) = PMap.is_empty w

  let cardinal (_w, cw : t) = cw

  let update idx f (w, cw as x) =
    let cwr = ref cw in
    let w' =
      PMap.update idx (fun old ->
        let n = f old in
        match old, n with
        | None, None -> n
        | None, Some _ -> incr cwr; n
        | Some _, None -> cwr := !cwr - 1; n
        | Some _, Some _ -> n)
        w
    in
    if w == w' then x else (w', !cwr)

  let _pr m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, _) -> Level.raw_pr (Index.repr idx m.table)) (PMap.bindings w)

  let pr_clauses m (w, _) =
    let open Pp in
    prlist_with_sep spc (fun (idx, fwd) ->
      Level.raw_pr (Index.repr idx m.table) ++ str": " ++ spc () ++
      str" Forward clauses " ++ pr_clauses_bwd m fwd)
      (PMap.bindings w)


  let domain (w, _) = PMap.domain w

  (* let _of_pset model w = PSet.fold (fun idx -> *)
    (* let can = repr model idx in *)
    (* add can.canon (can.clauses_bwd, can.clauses_fwd)) w empty *)

  (* Right-biased union *)
  let _union (w, c) (w', _) =
    let card = ref c in
    let merge _idx cls cls' =
      match cls, cls' with
      | None, None -> cls
      | _, Some _ -> incr card; cls'
      | Some _, None -> cls
    in
    let union = PMap.merge merge w w' in
    (union, !card)

end

exception FoundImplication

let update_value idx m clause : int option =
  let (k, premises) = clause in
  match min_premise m premises with
  | exception VacuouslyTrue -> None
  | k0 when k0 < 0 -> None
  | k0 ->
    let newk = k + k0 in
    match index_value m idx with
    | Some v when newk <= v -> None
    | _ ->
      debug_updates Pp.(fun () -> str"Updated value of " ++ pr_index_point m idx ++ str " to " ++ int newk);
      debug_updates Pp.(fun () -> str" due to clause " ++ pr_clauses_bwd m (ClausesBackward.singleton (idx, ClausesOf.singleton clause)));
      Some newk

let check_model_clauses_of_aux m idx cls =
  ClausesOf.fold (fun cls m ->
    match update_value idx m cls with
    | None -> m
    | Some newk -> set_index_value m idx newk)
    cls m

let find_bwd m idx cls =
  match PMap.find_opt idx cls with
  | Some cls -> cls
  | None ->
    PMap.fold (fun concl cls acc ->
      let can', _k = repr m concl in
      if can'.canon == idx then ClausesOf.union cls acc else acc) cls ClausesOf.empty

(** Check a set of forward clauses *)
let check_model_fwd_clauses_aux ?early_stop (cls : ClausesBackward.t) (acc : PSet.t * model) : PSet.t * model =
  let check () =
    PMap.fold (fun concl cls (* premises -> concl + k *) (wcls, m as acc) ->
      let can, k = repr m concl in
      let cls = ClausesOf.shift k cls in
      let m' = check_model_clauses_of_aux m can.canon cls in
      if m == m' then (* not modifed *) acc
      else (PSet.add can.canon wcls, m'))
      cls acc
  in
  match early_stop with
  | None -> check ()
  | Some (can, k) ->
      let (_, m) = acc in
      let cls = find_bwd m can.canon cls in
        ClausesOf.iter (fun cls ->
          match update_value can.canon m cls with
          | None -> ()
          | Some newk -> if k <= newk then raise FoundImplication)
          cls;
        check ()

let check_model_fwd_aux ?early_stop (cls, m) : PSet.t * model =
  CanSet.fold (fun _ fwd m -> check_model_fwd_clauses_aux ?early_stop fwd m) cls (PSet.empty, m)

(* let check_model_fwd_aux ?early_stop (cls, m) =
  (* if CDebug.get_flag debug_check_fwd then
    CanSet.fold (fun _ fwd acc -> check_model_fwd_clauses_aux ?early_stop fwd acc) cls
    (PSet.empty, m)
  else  *)
    check_model_fwd_aux ?early_stop (cls, m) *)

let check_clauses_with_premises ?early_stop (cls : CanSet.t) model : (PSet.t * model) option =
  let (updates, model') = check_model_fwd_aux ?early_stop (cls, model) in
  if model == model' then (debug Pp.(fun () -> str"Found a model"); None)
  else Some (updates, model')

(* let _check_model_bwd = check_model *)
let cardinal_fwd w =
  CanSet.fold (fun _idx fwd acc -> ClausesBackward.cardinal fwd + acc) w 0

let check_clauses_with_premises ?early_stop (updates : CanSet.t) model : (PSet.t * model) option =
  let open Pp in
  debug_check_model (fun () -> str"check_model on " ++ int (CanSet.cardinal updates) ++ str" universes, " ++
  int (cardinal_fwd updates) ++ str " clauses");
  check_clauses_with_premises ?early_stop updates model

(*let check_clauses_with_premises = time3 (Pp.str"check_clauses_with_premises") check_clauses_with_premises*)

(* let check_model = time3 (Pp.str "check_model") check_model *)

type 'a result = Loop | Model of 'a * model

let canonical_cardinal m = m.canonical

let can_all_premises_in m w prem =
  Premises.for_all (fun (l, _) -> PSet.mem (fst (repr m l)).canon w) prem

let partition_clauses_of model w cls =
  ClausesOf.partition (fun (_k, prems) -> can_all_premises_in model w prems) cls

let add_bwd concl cls clsof =
  if ClausesOf.is_empty cls then clsof
  else ClausesBackward.add (concl, cls) clsof

let add_canset idx clauses canset =
  if PMap.is_empty clauses then canset
  else CanSet.add idx clauses canset

(* Partition the clauses according to the presence of w in the premises, and only w in the conclusions *)
let partition_clauses_fwd model (w : PSet.t) (cls : CanSet.t) : CanSet.t * CanSet.t * CanSet.t =
  CanSet.fold (fun idx fwd (allw, conclw, conclnw) ->
    let fwdw, fwdpremw, fwdnw =
      ClausesBackward.fold (fun concl cls (fwdallw, fwdnallw, fwdnw) ->
        let concl, conclk = repr model concl in
        let concl = concl.canon in
        let ccls = ClausesOf.shift conclk cls in
        if PSet.mem concl w then
          let allw, nallw = partition_clauses_of model w ccls in
          (add_bwd concl allw fwdallw,
           add_bwd concl nallw fwdnallw,
           fwdnw)
        else (fwdallw, fwdnallw, add_bwd concl cls fwdnw))
        fwd (ClausesBackward.empty, ClausesBackward.empty, ClausesBackward.empty)
    in
    (* We do not keep bindings for all indexes *)
    let allw = add_canset idx fwdw allw (* Premises and conclusions in w *) in
    let conclw = add_canset idx fwdpremw conclw (* Conclusions in w, premises not all in w *) in
    let conclnw = add_canset idx fwdnw conclnw in (* Conclusions not in w, Premises not all in w *)
    (allw, conclw, conclnw))
    cls (CanSet.empty, CanSet.empty, CanSet.empty)

let add_fwd_clauses m w cls =
  PSet.fold (fun idx cls ->
    let upd = function
      | None ->
        let can, _ = repr m idx in
        debug_loop_partition Pp.(fun () -> str"Adding forward clauses of " ++ pr_can m can ++ pr_clauses_bwd m can.clauses_fwd);
        Some can.clauses_fwd
      | (Some _) as x -> x
    in CanSet.update idx upd cls)
 w cls

let partition_clauses_fwd = time2 (Pp.str"partition clauses fwd") partition_clauses_fwd

(* If early_stop is given, check raises FoundImplication as soon as
   it finds that the given atom is true *)

let model_points model =
  PMap.fold (fun idx equiv s ->
    match equiv with
    | Canonical _ -> PSet.add idx s
    | Equiv _ -> s)
    model.entries PSet.empty

let _pr_w m w =
  let open Pp in
  PSet.fold (fun idx pp ->
    pr_index_point m idx ++ spc () ++ pp) w (mt())

let w_of_canset (c : CanSet.t) = CanSet.domain c

let target_of_canset (c : CanSet.t) =
  CanSet.fold (fun _idx fwd acc ->
    PSet.union (PMap.domain fwd) acc) c PSet.empty

let pr_w m w = let open Pp in prlist_with_sep spc (pr_index_point m) (PSet.elements w)

let _pr_canset m (cls : CanSet.t) : Pp.t =
  let open Pp in
  CanSet.fold (fun idx fwd acc ->
    hov 1 (str "For " ++ pr_index_point m idx ++ str": " ++  pr_clauses_bwd m fwd) ++ fnl () ++ acc) cls (Pp.mt())

let pr_clauses m =
  PMap.fold (fun p e acc ->
    match e with
    | Equiv (p', k) ->
      Pp.(pr_index_point m p ++ str " = " ++ pr_with_incr (pr_index_point m) (p', k) ++ acc)
    | Canonical can ->
      let bwd = can.clauses_bwd in
      Pp.(pr_clauses_of m can.canon bwd ++ fnl () ++ acc)) m.entries (Pp.mt ())

(* model is a model for the clauses outside cls *)
let check_canset ?early_stop model ?(w=PSet.empty) (cls : CanSet.t) =
  let v = model_points model in
  let cV = canonical_cardinal model in
  debug_loop Pp.(fun () -> str"All model clauses: " ++ pr_clauses model);
  assert (cV = PSet.cardinal v);
  debug_check_invariants model;
  let rec inner_loop w cardW premconclw conclw m =
    (* Should consider only clauses with conclusions in w *)
    (* Partition the clauses acscording to the presence of w in the premises *)
    debug_loop Pp.(fun () -> str "Inner loop on " ++ int cardW ++ str" universes: " ++ spc () ++
      hov 2 (str " Premises and conclusions in w: " ++ int (PSet.cardinal (w_of_canset premconclw))) ++ fnl () ++
      hov 2 (str " Conclusions in w: " ++ int (PSet.cardinal (w_of_canset conclw))));
    (* Warning: m is not necessarily a model for w *)
    let rec inner_loop_partition w cardW premconclw conclw m =
      debug_loop Pp.(fun () -> str "inner_loop_partition on #|premconclw| = " ++ int (CanSet.cardinal premconclw) ++ str" cardW = " ++ int cardW);
      (* debug_loop Pp.(fun () -> str "cls = " ++ pr_w m cls); *)
      match loop w cardW PSet.empty premconclw m with
      | Loop -> Loop
      | Model (wr, mr) ->
        debug_loop Pp.(fun () -> str "inner_loop_partition call to loop results in a model with wr of size " ++ int (CanSet.cardinal wr) );
        (* debug_loop Pp.(fun () -> str "wr = " ++ pr_w mr wr); *)
        (* This is only necessary when clauses do have multiple premises,
           otherwise each clause is either in premconclw and already considered
           or in conclw but then the premise cannot be updated and this is useless work *)
        (match check_clauses_with_premises ?early_stop conclw mr with
        | Some (_wconcl, mconcl) ->
          (* debug_loop Pp.(fun () -> str "clsconcl = " ++ pr_w mconcl clsconcl); *)
          debug_loop Pp.(fun () -> str"Found an update in conclw after finding a model of premconclw in inner loop");
          inner_loop_partition w cardW premconclw conclw mconcl
        | None ->
          debug_loop Pp.(fun () -> str"Inner loop found a model");
          Model (wr, mr))
      in
      assert (PSet.cardinal (w_of_canset premconclw) <= cardW);
      assert (PSet.cardinal (target_of_canset conclw) <= cardW);
      inner_loop_partition w cardW premconclw conclw m
  and loop v cV winit (cls : CanSet.t) m =
    debug_loop Pp.(fun () -> str "loop on winit = " ++ pr_w m winit ++ str", #|cls| = " ++ int (cardinal_fwd cls) ++ str" bound is " ++ int cV);
    (* debug_loop Pp.(fun () -> str" cls = : " ++ pr_w m u); *)
    debug_loop_partition Pp.(fun () -> str"initial clauses: " ++ CanSet.pr_clauses m cls);
    (* debug_loop Pp.(fun () -> str"loop iteration on " ++ CanSet.pr_clauses m cls ++ str" with bound " ++ int cV); *)
    match check_clauses_with_premises ?early_stop cls m with
    | None -> debug_loop Pp.(fun () -> str "loop on #|w| = " ++ int (CanSet.cardinal cls) ++ str" found a model, bound is " ++ int cV);
      Model (cls, m)
    | Some (wupd, m) ->
      let w = PSet.union winit wupd in
      debug_loop Pp.(fun () -> str"check_clauses_with_premises updated " ++ int (PSet.cardinal w) ++ str" universes, bound is " ++ int cV);
      (* debug_loop Pp.(fun () -> str"diff between w and cls: " ++ pr_w m (PSet.diff w u)); *)
      (* debug_loop Pp.(fun () -> str"diff between w and cls domain: " ++ pr_w m (PSet.diff w (CanSet.domain cls))); *)
      (* debug_loop Pp.(fun () -> str"diff between cls domain and w: " ++ pr_w m (PSet.diff (CanSet.domain cls) w)); *)
      (* debug_loop Pp.(fun () -> str"cls domain is: " ++ pr_w m (CanSet.domain cls))); *)
      (* debug_loop Pp.(fun () -> str"Updated universes: " ++ pr_w m w ++ str", bound is " ++ int cV); *)
      let cardW = (PSet.cardinal w) in
      if Int.equal cardW cV
      then (debug_loop Pp.(fun () -> str"Found a loop on " ++ int cV ++ str" universes" ); Loop)
      else begin
        (if cardW > cV then
          let diff = (PSet.diff w v) in
          if PSet.is_empty diff then assert false;
          Feedback.msg_warning Pp.(str"Cardinal of w > V: " ++ pr_w m diff));

        let cls = add_fwd_clauses m wupd cls in
        let (premconclw, conclw, premw) = partition_clauses_fwd m w cls in
        debug_loop_partition Pp.(fun () -> str"partitioning clauses: " ++ CanSet.pr_clauses m cls);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: from and to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premconclw);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: to w, not from w: " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } conclw);
        debug_loop_partition Pp.(fun () -> str"partitioned clauses: from w, not to w " ++ spc () ++
          CanSet.pr_clauses { m with entries = PMap.empty } premw);

        (match inner_loop w cardW premconclw conclw m with
        | Loop -> Loop
        | Model (wc, mc) ->
          (* debug_loop Pp.(fun () -> str "wc = " ++ pr_w mc wc); *)
          debug_loop Pp.(fun () -> str"Checking clauses with premises in w, concl not in w, bound is " ++ int cV);
          (* wc is a subset of w *)
          (* TODO check weird Loop behavior in cumulativity.v without early stop *)
          (match check_clauses_with_premises ?early_stop premw mc with
          | None -> Model (wc, mc)
          | Some (w', mcls) ->
            (* if Int.equal (PSet.cardinal w') cV then Loop else *)
            (debug_loop Pp.(fun () -> str"Resulted in an update of #|w| = " ++ int (PSet.cardinal w') ++
              str" universes, launching back loop. w = " ++ pr_w mcls w ++ spc () ++ str" w' = " ++ pr_w mcls w');
            let cls = add_fwd_clauses mcls w' cls in
            loop v cV (PSet.union w w') cls mcls)))
      end
  in
  loop v cV w cls model

let check ?early_stop model w =
  let cls = add_fwd_clauses model w CanSet.empty in
  check_canset ?early_stop model ~w cls

let expr_value m (can, k) = add_opt (canonical_value m can) (- k)

let entry_value m e =
  match e with
  | Equiv (idx, k) -> expr_value m (repr_expr_can m (idx, k))
  | Canonical can -> canonical_value m can

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    let value = entry_value m v in
    let point = Index.repr u m.table in
    Level.raw_pr point ++ str" -> " ++ pr_opt int value) (PMap.bindings m.entries))
  (* Level.Map.pr Pp.int m  *)

let pr_model model =
  Pp.(str "model: " ++ pr_levelmap model)

let debug_model m =
  debug_model Pp.(fun () -> str"Model is " ++ pr_levelmap m)

let _repr_clause m (concl, prem as cl : clause) =
  let concl' = (fst (repr m concl)).canon in
  let prem' = repr_clauses_of m prem in
  if concl' == concl && prem' == prem then cl
  else (concl', prem')

let _modify_can canidx (f : Index.t -> canonical_node -> canonical_node) =
  PMap.modify canidx
    (fun idx entry ->
    match entry with
    | Equiv _ -> assert false
    | Canonical can -> let can' = f idx can in
      if can' == can then entry else Canonical can')

type can_clause = ((canonical_node * int) NeList.t * (canonical_node * int))

let pr_can_clause m (prems, conclk) =
  let open Pp in
  pr_with (pr_can m) conclk ++ str" ≤ " ++ NeList.pr_with_sep (fun () -> str", ") (pr_with (pr_can m)) prems

let add_can_clause_model m ((prems, (canl, k)) : can_clause) : can_clause * model =
  let clof = (k, NeList.map (fun (can, k) -> (can.canon, k)) prems) in
  (* Add clause to the backwards clauses of l *)
  let canl' =
    let bwd =
      (* if ClausesOfRepr.mem_upto m clof clauses_bwd then clauses_bwd else  *)
        ClausesOf.add clof canl.clauses_bwd in
    if bwd == canl.clauses_bwd then canl
    else { canl with clauses_bwd = bwd }
  in
  let m' = if canl == canl' then m else change_node m canl' in
  let prems', m' = (* Add clause to the forward clauses from the premises *)
    NeList.fold_map (fun ((idx0, k) as prem) entries ->
      let idx = if idx0 == canl then canl' else idx0 in
      let idx' =
        let fwd = ClausesBackward.add (canl'.canon, ClausesOf.singleton clof) idx.clauses_fwd in
        if fwd == idx.clauses_fwd then idx
        else { idx with clauses_fwd = fwd }
      in
      if idx0 != idx' then ((idx', k), change_node entries idx')
      else (prem, entries))
      prems m'
  in (prems', repr_expr_can m' (canl'.canon, k)), m'

let repr_model m =
  let entries' =
    PMap.Smart.map (function
    | Equiv _ as entry -> entry
    | Canonical can as entry ->
      let bwd = repr_clauses_of m can.clauses_bwd in
      let fwd = ClausesBackward.repr m can.clauses_fwd in
      if bwd == can.clauses_bwd && fwd == can.clauses_fwd then entry
      else Canonical { can with clauses_bwd = bwd; clauses_fwd = fwd })
    m.entries
  in
  if entries' == m.entries then m
  else { m with entries = entries' }

let _canonical_model m = repr_model m

let _clauses_levels cls =
  PMap.fold (fun concl _ acc -> PSet.add concl acc)
    (* (ClausesOf.fold (fun cli acc ->
      let (_, prems) = cli in
      List.fold_left (fun acc (l, _k') -> PSet.add (repr m l).canon acc) acc prems)
      cls acc)) *)
    cls PSet.empty

let infer_clauses_extension cans m =
  debug_check_invariants m;
  (* debug_check_invariants model clauses; *)
  debug Pp.(fun () -> str"Calling loop-checking" ++ statistics m);
  (* debug Pp.(fun () -> str"Filtered clauses " ++ int (Clauses.cardinal filtered_clauses)); *)
  (* Clauses.mark m.clauses ClausesOf.ClauseInfo.Skip;  *)
  (* match check_model clauses (clauses_levels model clauses) model with
  | None -> Some m
  | Some (w, m') ->
    let inw = clauses_forward m' m.clauses w in
    debug Pp.(fun () -> str"After one check model: " ++ int (Clauses.cardinal inw) ++ str" having premises in w");*)
  (* let levels = PSet.union w (clauses_levels clauses.Clauses.clauses_fwd) in *)
  match check m cans with
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    None
  | Model (_updates, model) ->
    debug_check_invariants model;
    debug_model model;
    debug Pp.(fun () -> str"loop-checking found a model");
    Some model

(* let infer_clauses_extension ?w = time2 Pp.(str"infer_clauses_extension") (infer_clauses_extension ?w) *)
let empty = empty_model

let pr_incr pr (x, k) =
  Pp.(pr x ++ if k == 0 then mt() else str"+" ++ int k)

(* Precondition: canu.value = canv.value, so no new model needs to be computed *)
let enforce_eq_can model (canu, ku as u) (canv, kv as v) : (canonical_node * int) * t =
  assert (expr_value model u = expr_value model v);
  assert (canu != canv);
  (* v := u or u := v, depending on Level.is_source (for Set) *)
  debug_check_invariants model;
  let model0 = model in
  let can, k, other, diff, model =
    if Level.is_set (Index.repr canu.canon model.table) then
      (* Set + k = l + k' -> k' < k
        -> l = Set + (k - k') *)
      (assert (kv <= ku);
       (canu, ku, canv, ku - kv, enter_equiv model canv.canon canu.canon (ku - kv)))
    else if ku <= kv then
      (canv, kv, canu, kv - ku, enter_equiv model canu.canon canv.canon (kv - ku))
    else
      (* canu + ku = canv + kv /\ kv < ku ->
        canv = canu + (ku - kv)
        *)
      (canu, ku, canv, ku - kv, enter_equiv model canv.canon canu.canon (ku - kv))
  in
  (* other = can + diff *)
  let can, model =
    let bwd = ClausesOfRepr.union_upto model can.canon can.clauses_bwd (ClausesOf.shift diff other.clauses_bwd) in
    let fwd = ClausesBackward.union_upto model can.clauses_fwd other.clauses_fwd in
    let modeln = { model with entries = PMap.empty } in
      debug Pp.(fun () -> str"Backward clauses for " ++
      pr_can model can ++ str": " ++ spc () ++
      pr_clauses_of modeln can.canon can.clauses_bwd);
      debug Pp.(fun () -> str"Backward clauses for " ++
      pr_can model0 other ++ str": " ++ spc () ++
      pr_clauses_of modeln other.canon other.clauses_bwd);
      debug Pp.(fun () -> str"New backward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_of modeln can.canon bwd);
      debug Pp.(fun () -> str"Add forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln fwd);
      debug Pp.(fun () -> str"Previous forward clauses for " ++
        pr_can model can ++ str": " ++ spc () ++
        pr_clauses_bwd modeln can.clauses_fwd);
      debug Pp.(fun () -> str"Other forward clauses for " ++
        pr_can model0 other ++ str": " ++ spc () ++
        pr_clauses_bwd modeln other.clauses_fwd);
    let can = { can with clauses_bwd = bwd; clauses_fwd = fwd } in
    can, change_node model can
  in
  debug_check_invariants model;
  (can, k), model

let enforce_eq_can = time3 (Pp.str"enforce_eq_can") enforce_eq_can

 let pr_can_constraints m can =
  let open Pp in
  pr_clauses_of m can.canon can.clauses_bwd ++ spc () ++
  str"Forward clauses: " ++ pr_clauses_bwd m can.clauses_fwd

let make_equiv m equiv =
  debug_global Pp.(fun () -> str"Unifying universes: " ++
    prlist_with_sep spc (fun can -> pr_incr (pr_can m) can) equiv);
  match equiv with
  | can :: can' :: tl ->
    (* We are about to merge all these universes as they should be equal in the model,
      they should hence have the same values *)
    if CDebug.(get_flag debug_loop_checking_invariants) then
      assert (List.for_all (fun x -> expr_value m x = expr_value m can) (can' :: tl));
    let can, m =
      List.fold_left (fun (can, m) can' -> enforce_eq_can m can can')
        (enforce_eq_can m can can') tl
    in
    debug_global Pp.(fun () -> str"Chosen canonical universe: " ++ pr_incr (pr_can m) can ++
          str"Constraints:" ++ pr_can_constraints m (fst can));
    m
  | [_] -> m
  | _ -> assert false

let make_equiv = time2 (Pp.str"make_equiv") make_equiv

let clauses_bwd_univs m cls =
  PMap.fold (fun concl _ acc -> PSet.add (fst (repr m concl)).canon acc) cls PSet.empty

module Status = struct
  module Internal = Hashtbl.Make(CN)

  (** we could experiment with creation size based on the size of [g] *)
  let create (_m:model) = Internal.create 17

  let _mem = Internal.mem
  let find = Internal.find
  let replace = Internal.replace
  let fold = Internal.fold
end

let find_to_merge model status (canv, kv) (canu, ku) =
  let rec forward (can, k) : bool =
    debug Pp.(fun () -> str"visiting " ++ pr_can model can);
    match Status.find status can with
    | merge, _ -> merge
    | exception Not_found ->
      let merge = (can == canv && Int.equal k kv) || (can == canu && Int.equal k ku) in
      let () = Status.replace status can (merge, k) in
      let cls = can.clauses_fwd in
      debug Pp.(fun () -> str"Forward universes: " ++ int (ClausesBackward.cardinal cls) ++
        str " Canonical: " ++ int (PSet.cardinal (clauses_bwd_univs model cls)));
      let merge =
        ClausesBackward.fold (fun concl cls (* cls = { prems -> concl + k | can + k' ∈ prems } *) merge ->
          let conclcan, conclk = repr model concl in
          if (* Avoid self-loops *) conclcan != can
          then
            (* Ensure there is indeed a forward clause of shape can -> conclcan, not going through max() premises *)
            ClausesOf.fold (fun (clk, prems) merge ->
              match prems with
              | NeList.Tip (_, kprem) ->
                (* Stay in the same equivalence class *)
                if expr_value model (conclcan, conclk + clk) = expr_value model (can, k) then
                  if kprem > k then merge (* The clause is too high: i.e. l + 1 -> concl while we are looking at merging l *)
                  else
                    let merge' = forward (conclcan, conclk + clk + (k - kprem)) in
                    merge' || merge
                else merge
              | _ -> merge) cls merge
          else merge) cls merge
      in
      Status.replace status can (merge, k);
      merge
  in
  let merge = forward (canu, ku) in
  if merge then
    let merge_fn can (mark, k) acc = if mark then (can, k) :: acc else acc in
    let equiv = Status.fold merge_fn status [] in
    merge, equiv
  else merge, []

let find_to_merge =
  time4 (Pp.str "find_to_merge") find_to_merge

let pr_can_expr m = pr_incr (fun c -> pr_index_point m c.canon)

let simplify_clauses_between model (canv, kv as v) (canu, _ as u) =
  if canv == canu then
    (debug_global Pp.(fun () -> str"simplify clauses between: same universes"); model)
  else if not (Option.equal Int.equal (expr_value model u) (expr_value model v)) then
      (* We know v -> u and check for u -> v, this can only be true if both levels
        already have the same value *)
    (debug_global Pp.(fun () -> pr_can model canu ++ str"'s value =  " ++
        pr_opt int (canonical_value model canu) ++ str" and " ++ pr_can model canv ++ str "'s value = "
      ++ pr_opt int (canonical_value model canv) ++ str", no simplification possible");
      model)
  else
    let status = Status.create model in
    let merge, equiv = find_to_merge model status v u in
    (if merge then debug_global Pp.(fun () -> str"Trying to merge: " ++ pr_can_expr model u ++ str" (value =  " ++
        pr_opt int (canonical_value model canu) ++ str") and " ++ pr_can_expr model (canv, kv) ++ str " (value = " ++
        pr_opt int (canonical_value model canv));
    if merge then make_equiv model equiv else model)

(* let simplify_clauses_between = *)
  (* time3 (Pp.str "simplify_clauses_between") simplify_clauses_between *)
(*

let enforce_eq_points ({ model; clauses } as m : t) u v =
  debug Pp.(fun () -> str"Enforce equal points");
  let canu = repr_node model u in
  let canv = repr_node model v in
  if canu == canv then ((false, canu), m)
  else
    if Int.equal canu.value canv.value then
    enforce_eq_can m canu canv
  else

    let clauses' = add_clauses model canv (ClausesOf.singleton (0, [(canu.canon, 0)])) clauses in
    let clauses'' = add_clauses model canu (ClausesOf.singleton (0, [(canv.canon, 0)])) clauses' in
    ((true, canu), { model; clauses = clauses'' }) *)

type nat = int
type can_constraint = (canonical_node * nat) * (canonical_node * nat)

let can_clause_of_can_constraint (cstr : can_constraint) : can_clause =
  let (l, r) = cstr in (* l + k <= r *)
  (NeList.tip r, l)

type 'a check_function = t -> 'a -> 'a -> bool

(* @raises VacuouslyTrue if there is an undefined level in the premises *)
let min_can_premise model prem =
  let g (l, k) = (match canonical_value model l with Some v -> v | None -> raise VacuouslyTrue) - k in
  let f prem minl = min minl (g prem) in
  Premises.fold_ne f g prem

let update_model_value (m : model) can k' : model =
  let v = canonical_value m can in
  let k' = max_opt v k' in
  if Option.equal Int.equal k' v then m
  else
    (debug Pp.(fun () -> str"Updated value of " ++ pr_can m can ++ str " to " ++ pr_opt int k');
    set_canonical_value m can (Option.get k'))

(* A clause premises -> concl + k might hold in the current minimal model without being valid in all
   its extensions.

   We generate the minimal model starting from the premises. I.e. we make the premises true.
   Then we check that the conclusion holds in this minimal model.  *)

let check_one_clause model prems concl k =
  (* premise -> concl + k ? *)
  debug Pp.(fun () -> str"Checking entailment: " ++ prlist_with_sep (fun () -> str",") (pr_can_expr model) (NeList.to_list prems) ++
    str " -> " ++ pr_can_expr model (concl, k));
  (* if (Level.is_set (Index.repr concl.canon model.table)) && k == 0 then true else *)
  let model = NeList.fold (fun prem values ->
    let x, k = repr_can_expr model prem in
    update_model_value values x (Some k)) prems
    { model with values = PMap.empty }
  in
  let cls = NeList.fold (fun (prem, _k) cls -> CanSet.add prem.canon prem.clauses_fwd cls) prems CanSet.empty in
  (* We have a model where only the premise is true, check if the conclusion follows *)
  debug Pp.(fun () -> str"Launching loop-checking to check for entailment");
  match check_canset ~early_stop:(concl, k) model ~w:(w_of_canset cls) cls with
  | exception FoundImplication ->
    debug Pp.(fun () -> str"loop-checking found the implication early");
    true
  | Loop ->
    debug Pp.(fun () -> str"loop-checking found a loop");
    false
  | Model (_updates, model') ->
    debug Pp.(fun () -> str"loop-checking found a model");
    debug_check_invariants model';
    debug_model model';
    match canonical_value model' concl with
    | None ->
      debug Pp.(fun () -> str"Conclusion has no value in the minimal model, not implied");
      false
    | Some value ->
      debug Pp.(fun () -> str"Conclusion has value " ++ int value ++
        str" in the minimal model, expecting conclusion + " ++ int k ++ str " to hold");
      k <= value

let update_model ((prems, (can, k)) : can_clause) (m : model) : PSet.t * model =
  match min_can_premise m prems with
  | exception VacuouslyTrue -> (PSet.empty, m)
  | k0 ->
    let m' = update_model_value m can (Some (k + k0)) in
    if m' != m then
      let canset = CanSet.add can.canon can.clauses_fwd CanSet.empty in
      match check_clauses_with_premises canset m' with
      | Some (modified, wm) -> (modified, wm)
      | None -> (PSet.empty, m')
    else (PSet.empty, m)

let infer_clause_extension cl m =
  (* debug Pp.(fun () -> str "current model is: " ++ pr_levelmap model); *)
  debug_check_invariants m;
  let cl, m = add_can_clause_model m cl in
  let cans, m = update_model cl m in
  if PSet.is_empty cans then begin
    (* The clause is already true in the current model,
      but might not be in an extension, so we keep it *)
    debug Pp.(fun () -> str"Clause is valid in the current model");
    (* debug_clauses Pp.(fun () -> str"Clauses: " ++ pr_clauses model m.clauses); *)
    Some m
  end else begin
    (* The clauses are not valid in the current model, we have to find a new one *)
    debug Pp.(fun () -> str"Enforcing clauses requires a new inference");
    match infer_clauses_extension cans m with
    | None ->
      debug Pp.(fun () -> str"Enforcing clauses " ++ pr_can_clause m cl ++ str" resulted in a loop");
      None
    | Some _ as x -> x
  end

let infer_clause_extension cl m =
  debug_global Pp.(fun () -> str"Enforcing clause " ++ pr_can_clause m cl);
  let res = infer_clause_extension cl m in
  match res with
  | None -> debug_global Pp.(fun () -> str"Resulted in a loop"); res
  | Some m ->
    debug_check_invariants m;
    debug_global Pp.(fun () -> str" is consistent"); res

let infer_extension x y m =
  let cl = can_clause_of_can_constraint (x, y) in
  infer_clause_extension cl m

let infer_extension =
  time3 Pp.(str "infer_extension") infer_extension

(* Enforce u <= v and check if v <= u already held, in that case, enforce u = v *)
let enforce_leq_can u v m =
  let cl = (NeList.tip v, u) in
  debug_global Pp.(fun () -> str"enforce_leq " ++ pr_can_clause m cl);
  match infer_extension u v m with
  | None -> None
  | Some m' ->
    if m' != m then
      (debug_global Pp.(fun () -> str"enforce_leq did modify the model");
      let v = repr_can_expr m' v in
      let u = repr_can_expr m' u in
      Some (simplify_clauses_between m' v u))
    else Some m

let enforce_leq_level u v m =
  let m, canu = repr_compress_node m u in
  let m, canv = repr_compress_node m v in
  enforce_leq_can canu canv m

let get_proper_value m can =
  match canonical_value m can with
  | Some v -> v
  | None -> raise (Undeclared (Index.repr can.canon m.table))

let enforce_eq_level u v m =
  let canu, ku = repr_node m u in
  let canv, kv = repr_node m v in
  if canu == canv && Int.equal ku kv then Some m
  else begin
    debug_global Pp.(fun () -> str"enforce_eq: " ++ pr_with_incr (pr_can m) (canu, ku) ++ str" = " ++ pr_with_incr (pr_can m) (canv, kv));
    match Int.compare (get_proper_value m canu) (get_proper_value m canv) with
    (* | 0 -> Some (snd (enforce_eq_can m canu canv)) *)
    | x when x <= 0 ->
      (* canu.value <= canv.value, so v <= u is trivial and we cannot have u < v,
         only u <= v in the clauses.
         The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward model m.clauses (PSet.singleton canu.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses model cls); *)
      Option.bind (enforce_leq_can (canv, kv) (canu, ku) m)
        (fun m' ->
          let canu' = repr_expr_can m' (canu.canon, ku) in
          let canv' =  repr_expr_can m' (canv.canon, kv) in
          enforce_leq_can canu' canv' m')
    | _ ->
      (* canv.value < canu.value, so u <= v is trivial.
          The first enforce will be fast, the second can involve an inference *)
      (* let cls = clauses_forward model m.clauses (PSet.singleton canv.canon) in *)
      (* debug Pp.(fun () -> str"enforce_eq: clauses to move " ++ pr_clauses model cls); *)
      Option.bind (enforce_leq_can (canu, ku) (canv, kv) m)
        (fun m' ->
          let canu' = repr_expr_can m' (canu.canon, ku) in
          let canv' = repr_expr_can m' (canv.canon, kv) in
          enforce_leq_can canv' canu' m')
  end

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint u v cls =
  List.fold_right (fun (u, k) cls -> (Universe.repr v, (u, k)) :: cls) (Universe.repr u) cls

let clauses_of_constraint (u : Universe.t) k (v : Universe.t) cls =
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let can_clause_of_clause m (prems, concl) =
  let prems = NeList.of_list (List.map (fun prem -> repr_node_expr m prem) prems) in
  let concl = repr_node_expr m concl in
  (prems, concl)

let infer_extension (prems, (concl, k) as cl) m =
  match prems with
  | NeList.Tip pk ->
    (* We can only represent equations u + k = v + k' through our union-find algorithm,
      not max(l, l') = v + k constraints *)
    enforce_leq_can (concl, k) pk m
  | _ -> infer_clause_extension cl m


(* let debug_filter, _ = CDebug.create_full ~name:"loop-checking-filter" () *)

(** Simplify u <= max (Set, v) clauses to u <= v and filter away u <= ... u + n , ... clauses, always valid *)
let filter_trivial_can_clause m ((prems, (concl, k as conclk)) : can_clause) : can_clause option =
  (* Trivial ... u + k + n ... -> u + k clause *)
  if NeList.exists (fun (prem, k') -> prem == concl && k' >= k) prems then
    None
  else
    (* Filter out `Set` from max(Set, u) -> v constraints *)
    let canset = Index.find Level.set m.table in
    let prems =
      match NeList.filter (fun (prem, k) -> not (Index.equal prem.canon canset && Int.equal k 0)) prems with
      | Some prems -> prems (* There were at least two premises in the rule *)
      | None -> prems
    in
    Some (prems, conclk)

let infer_extension_filter cl m =
  match filter_trivial_can_clause m cl with
  | None -> Some m
  | Some cl -> infer_extension cl m

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint u k v [] in
  List.fold_left (fun m cl ->
    match m with
    | None -> None
    | Some m -> infer_extension_filter (can_clause_of_clause m cl) m) (Some m) cls

let enforce u k v m =
  match Universe.repr u, k, Universe.repr v with
  | [(u, 0)], Eq, [(v, 0)] -> enforce_eq_level u v m
  | [(u, 0)], Le, [(v, 0)] -> enforce_leq_level u v m
  | _, _, _ -> enforce_constraint u k v m

let enforce_eq u v m = enforce u Eq v m
let enforce_leq u v m = enforce u Le v m
let enforce_lt u v m = enforce_constraint (Universe.addn u 1) Le v m

let check_clause model cl =
  match filter_trivial_can_clause model cl with
  | None -> true
  | Some (prems, (concl, k)) -> check_one_clause model prems concl k

let check_constraint (m : t) u k u' =
  debug_global Pp.(fun () -> str"Checking " ++ Constraints.pr Level.raw_pr (Constraints.singleton (u,k,u')));
  let cls = clauses_of_constraint u k u' [] in
  let res = List.fold_left (fun check cl -> check && check_clause m (can_clause_of_clause m cl)) true cls in
  if res then (debug_global Pp.(fun () -> str" Clause holds"); res)
  else (debug_global Pp.(fun () -> str" Clause does not hold"); res)

let check_leq m u v = check_constraint m u Le v
let check_eq m u v = check_constraint m u Eq v

let enforce_constraint (u, k, v) (m : t) = enforce u k v m

exception AlreadyDeclared

let add_model u { entries; table; values; canonical } =
  if Index.mem u table then
   (debug_global Pp.(fun () -> str"Already declared level: " ++ Level.raw_pr u);
    raise AlreadyDeclared)
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx;
      clauses_fwd = PMap.empty; clauses_bwd = ClausesOf.empty } in
    let entries = PMap.add idx can entries in
    let values = PMap.add idx 0 values in
    idx, { entries; table; values; canonical = canonical + 1 }

let add ?(rank:int option) u model =
  let _r = rank in
  debug_global Pp.(fun () -> str"Declaring level " ++ Level.raw_pr u);
  let _idx, model = add_model u model in
  model

let check_declared model us =
  let check l = if not (Index.mem l model.table) then raise (Undeclared l) in
  Level.Set.iter check us

type explanation = Universe.t * (constraint_type * Universe.t) list

let get_explanation (cstr : univ_constraint) _ : explanation =
  let (_l, _, r) = cstr in
  (* TODO *)
  (r, [])

let pr_constraint_type k =
  let open Pp in
  match k with
  | Eq -> str " = "
  | Le -> str " ≤ "

let constraint_type_ord c1 c2 = match c1, c2 with
| Le, Le -> 0
| Le, Eq -> -1
| Eq, Eq -> 0
| Eq, Le -> 1

type univ_constraint = Universe.t * constraint_type * Universe.t

module UConstraintOrd =
struct
type t = univ_constraint
let compare (u,c,v) (u',c',v') =
  let i = constraint_type_ord c c' in
  if not (Int.equal i 0) then i
  else
    let i' = Universe.compare u u' in
    if not (Int.equal i' 0) then i'
    else Universe.compare v v'
end


module Constraints =
struct
  module S = Set.Make(UConstraintOrd)
  include S

  let _pr prl c =
    let open Pp in
    v 0 (prlist_with_sep spc (fun (u1,op,u2) ->
      hov 0 (prl u1 ++ pr_constraint_type op ++ prl u2))
       (elements c))
end

let constraints_of_clauses m clauses =
  ClausesBackward.fold (fun concl cls cstrs ->
    let conclp = Index.repr concl m.table in
    ClausesOf.fold (fun cli cstrs ->
      let (k, prems) = cli in
      let prems = NeList.to_list prems in
      let prems =
        List.map (fun (v, k) ->
          let vcan, vk = repr m v in
          let vp = Index.repr vcan.canon m.table in
          (vp, vk + k)) prems
      in
      let prem = Universe.of_list prems in
      Constraints.add (Universe.of_list [(conclp, k)], Le, prem) cstrs)
      cls cstrs)
    clauses Constraints.empty

let constraints_of model fold acc =
  let module UF = Unionfind.Make (LevelExpr.Set) (LevelExpr.Map) in
  let equiv = UF.create () in
  let bwd = ref ClausesBackward.empty in
  let constraints_of u v =
    match v with
    | Canonical can ->
      bwd := ClausesBackward.add (can.canon, can.clauses_bwd) !bwd
    | Equiv (v, vk) ->
      let u = Index.repr u model.table in
      let v = Index.repr v model.table in
      UF.union (u, 0) (v, vk) equiv
  in
  let () = PMap.iter constraints_of model.entries in
  let cstrs = constraints_of_clauses model !bwd in
  Constraints.fold fold cstrs acc, UF.partition equiv

type 'a constraint_fold = univ_constraint -> 'a -> 'a

let interp_univ model l =
  Universe.of_list (NeList.to_list (NeList.map (fun (idx, k) -> (Index.repr idx model.table, k)) l))

let shift_prems n p =
  if Int.equal n 0 then p
  else NeList.map (fun (x,k) -> (x, k + n)) p

(* Precondition: all mentionned universes are canonical *)
let merge_clauses premsfwd can cank premsbwd concl conclk =
  (* New constraint: premsbwd[can + k := premsfwd + k'] -> concl + conclk']  *)
  let bk = NeList._find (fun c -> c == can) premsbwd in
  let premsfwd, premsbwd, conclk =
    (* Align the clauses on the same universe by the admissible shift transform *)
    if bk <= cank then
      (* Shift the backwards clause *)
      let diff = cank - bk in
      premsfwd, shift_prems diff premsbwd, conclk + diff
    else
      shift_prems (bk - cank) premsfwd, premsbwd, conclk
  in
  let prems' = NeList.map_splice (fun (c, _) ->
    if c == can then Some premsfwd else None) premsbwd in
  (prems', (concl, conclk))

let constraints_for ~(kept:Level.Set.t) model (fold : 'a constraint_fold) (accu : 'a) : 'a * Level.Set.t =
  let add_cst u knd v (cst : 'a) : 'a =
    fold (interp_univ model u, knd, interp_univ model v) cst
  in
  debug_global Pp.(fun () -> str"constraints_for kept: " ++ Level.Set.pr Level.raw_pr kept);
  let keptp = Level.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) kept PSet.empty in
  (* rmap: partial map from canonical points to kept points *)
  let rmap, csts = PSet.fold (fun u (rmap,csts) ->
    let arcu, ku = repr model u in
    if PSet.mem arcu.canon keptp then
      let csts = if Index.equal u arcu.canon then csts
        else add_cst (NeList.tip (u, 0)) Eq (NeList.tip (arcu.canon, ku)) csts
      in
      PMap.add arcu.canon arcu.canon rmap, csts
    else
      match PMap.find arcu.canon rmap with
      | v -> rmap, add_cst (NeList.tip (u, 0)) Eq (NeList.tip (v, 0)) csts
      | exception Not_found -> PMap.add arcu.canon u rmap, csts)
    keptp (PMap.empty, accu)
  in
  let removed =
    PMap.fold
      (fun idx entry removed ->
        match entry with
        | Equiv (_, _k) ->
          (* We don't need to care about removed non-canonical universes *)
          removed
        | Canonical can ->
            if PSet.mem idx keptp then removed
            else
              if PMap.mem can.canon rmap then
                (* This canonical node is represented by a kept universe, don't remove *)
                removed
              else (* Removal of a canonical node, we need to modify the clauses *)
                PSet.add can.canon removed)
    model.entries PSet.empty
  in
  let remove_can idx model =
    let can, k = repr model idx in
    assert (Int.equal k 0 && Index.equal can.canon idx);
    let fwd = can.clauses_fwd in
    let bwd = can.clauses_bwd in
    ClausesBackward.fold (fun concl fwd model ->
      let concl, k = repr model concl in
      let fwd = ClausesOf.shift k fwd in
      ClausesOf.fold (fun (conclk, premsbwd) model ->
        (* premsbwd = ... can + k ... -> concl + conclk *)
        ClausesOf.fold (fun (cank, premsfwd) model ->
          (* premsfwd -> can + cank *)
          let premsbwd = canonical_premises model premsbwd in
          let premsfwd = canonical_premises model premsfwd in
          let cl = merge_clauses premsfwd can cank premsbwd concl conclk in
          let _, m = add_can_clause_model model cl in
          m)
        bwd model)
      fwd model)
    fwd model
  in
  (* At this point the clauses that don't mention removed universes are enough to
     derive any clause between kept universes *)
  let model = PSet.fold remove_can removed model in

  let canon_repr can =
    match PMap.find can.canon rmap with
    | v -> v
    | exception Not_found -> assert false
  in
  let can_prem_to_prem l = NeList.map (fun (x, k) -> (canon_repr x, k)) l in
  let rec add_from u csts todo = match todo with
    | [] -> csts
    | (prems,k)::todo ->
      let cprems = canonical_premises model prems in
      if not (NeList.exists (fun (v, _) -> PSet.mem v.canon removed) cprems) then
        let csts = add_cst (NeList.tip (canon_repr u, k)) Le (can_prem_to_prem cprems) csts in
        add_from u csts todo
      else add_from u csts todo
  in
  let fold u acc =
    let arc, uk = repr model u in
    let cls = arc.clauses_bwd in
    ClausesOf.fold (fun (k, prems) csts -> add_from arc csts [prems,k + uk]) cls acc
  in
  let kept = PSet.fold (fun p -> Level.Set.add (Index.repr p model.table)) keptp Level.Set.empty in
  (PSet.fold fold keptp csts, kept)

(*
  let cstrs = constraints_of_clauses model clauses in
  let cstrs = Constraints.filter (fun (l, _, r) -> Level.Set.mem l kept || Level.Set.mem r kept) cstrs in
  Constraints.fold fold cstrs acc *)

let domain model = Index.dom model.table

let choose p model p' =
  let canp' = repr_node model p' in
  let pointp' = Index.repr (fst canp').canon model.table in
  if p pointp' then Some pointp'
  else PMap.fold (fun idx e acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match e with
        | Equiv (idx', k) ->
          let canp'' = repr_expr_can model (idx', k) in
          if fst canp' == fst canp'' && Int.equal (snd canp') (snd canp'') then
            let pointp' = Index.repr idx model.table in
            if p pointp' then Some pointp'
            else acc
          else acc
        | Canonical _ -> acc)
      model.entries None


type node =
| Alias of LevelExpr.t
| Node of (int * Universe.t) list (** Nodes [(k_i, u_i); ...] s.t. u + k_i <= u_i *)

type repr = node Level.Map.t

let univ_of_expr model (l, k) =
  Universe.of_expr (Index.repr l model.table, k)

let universe_of_premise model prem =
  match prem with
  | NeList.Tip (l, k) -> univ_of_expr model (l, k)
  | NeList.Cons (e, xs) ->
    NeList.fold (fun (l, k) acc -> Universe.sup (univ_of_expr model (l, k)) acc) xs (univ_of_expr model e)

let repr model =
  PMap.fold (fun idx e acc ->
    let conclp = Index.repr idx model.table in
    let node = match e with
    | Equiv (idx, k) -> Alias (Index.repr idx model.table, k)
    | Canonical can ->
      let prems = can.clauses_bwd in
      let cls =
        ClausesOf.fold (fun cli l ->
          let (k, prem) = cli in
          let u = universe_of_premise model prem in
          (k, u) :: l) prems []
      in Node cls
    in
    Level.Map.add conclp node acc)
  model.entries Level.Map.empty

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Level.Map.add p v acc)
    pmap Level.Map.empty

let valuation_of_model (m : model) =
  let max = Option.default 0 (model_max m) in
  let valm = PMap.map (fun e -> max - Option.get (entry_value m e)) m.entries in
    pmap_to_point_map m.table valm

let valuation model = valuation_of_model model
