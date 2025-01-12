(* -*- mode: coq; coq-prog-args: ("-indices-matter"); mode: visual-line -*- *)
Set Universe Polymorphism.
Set Primitive Projections.
Close Scope nat_scope.

Record prod (A B : Type) := pair { fst : A ; snd : B }.
Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Unset Strict Universe Declaration.

Definition Type1 := Eval hnf in let gt := (Set : Type@{i}) in Type@{i}.
Definition Type2 := Eval hnf in let gt := (Type1 : Type@{i}) in Type@{i}.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (@paths _ x y) : type_scope.
Definition concat {A} {x y z : A} (p : x = y) (q : y = z) : x = z
  := match p, q with idpath, idpath => idpath end.

Definition path_prod {A B : Type} (z z' : A * B)
: (fst z = fst z') -> (snd z = snd z') -> (z = z').
Proof.
  destruct z, z'; simpl; intros [] []; reflexivity.
Defined.

Module Type TypeM.
  Parameter m@{i} : Type2@{i}.
End TypeM.

Module ProdM (XM : TypeM) (YM : TypeM) <: TypeM.
  Definition m@{i} := XM.m@{i} * YM.m@{i}.
End ProdM.

Module Type FunctionM (XM YM : TypeM).
  Parameter m@{i} : XM.m@{i} -> YM.m@{i}.
End FunctionM.

Module IdmapM (XM : TypeM) <: FunctionM XM XM.
  Definition m@{i} := (fun x => x) : XM.m@{i} -> XM.m.
End IdmapM.

Module Type HomotopyM (XM YM : TypeM) (fM gM : FunctionM XM YM).
  Parameter m@{i} : forall x, fM.m@{i} x = gM.m x.
End HomotopyM.

Module ComposeM (XM YM ZM : TypeM)
       (gM : FunctionM YM ZM) (fM : FunctionM XM YM)
       <: FunctionM XM ZM.
  Definition m@{i} := (fun x => gM.m@{i} (fM.m@{i} x)).
End ComposeM.

Module Type CorecM (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (gM : FunctionM XM ZM).
  Parameter m@{i} : XM.m@{i} -> YM.m@{i}.
  Parameter m_beta@{i} : forall x, fM.m@{i} (m@{i} x) = gM.m x.
End CorecM.

Module Type CoindpathsM (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (XM : TypeM) (hM kM : FunctionM XM YM).
  Module fhM := ComposeM XM YM ZM fM hM.
  Module fkM := ComposeM XM YM ZM fM kM.
  Declare Module mM (pM : HomotopyM XM ZM fhM fkM)
    : HomotopyM XM YM hM kM.
End CoindpathsM.

Module Type Comodality (XM : TypeM).
  Parameter m@{i} : Type2@{i}.
  Module mM <: TypeM.
    Definition m@{i} := m@{i}.
  End mM.
  Parameter from@{i} : m@{i} -> XM.m@{i}.
  Module fromM <: FunctionM mM XM.
    Definition m@{i} := from@{i}.
  End fromM.
  Declare Module corecM : CorecM mM XM fromM.
  Declare Module coindpathsM : CoindpathsM mM XM fromM.
End Comodality.

Module Comodality_Theory (F : Comodality).

  Module F_functor_M (XM YM : TypeM) (fM : FunctionM XM YM)
         (FXM : Comodality XM) (FYM : Comodality YM).
    Module f_o_from_M <: FunctionM FXM.mM YM.
      Definition m@{i} := fun x => fM.m@{i} (FXM.from x).
    End f_o_from_M.
    Module mM := FYM.corecM FXM.mM f_o_from_M.
    Definition m@{i} := mM.m@{i}.
  End F_functor_M.

  Module F_prod_cmp_M (XM YM : TypeM)
         (FXM : Comodality XM) (FYM : Comodality YM).
    Module PM := ProdM XM YM.
    Module PFM := ProdM FXM FYM.
    Module fstM <: FunctionM PM XM.
      Definition m@{i} := @fst XM.m@{i} YM.m@{i}.
    End fstM.
    Module sndM <: FunctionM PM YM.
      Definition m@{i} := @snd XM.m@{i} YM.m@{i}.
    End sndM.
    Module FPM := F PM.
    Module FfstM := F_functor_M PM XM fstM FPM FXM.
    Module FsndM := F_functor_M PM YM sndM FPM FYM.
    Definition m@{i} : FPM.m@{i} -> PFM.m@{i}
      := fun z => (FfstM.m z , FsndM.m z).
  End F_prod_cmp_M.

  Module isequiv_F_prod_cmp_M
         (XM YM : TypeM)
         (FXM : Comodality XM) (FYM : Comodality YM).
    (** The comparison map *)
    Module cmpM := F_prod_cmp_M XM YM FXM FYM.
    Module FPM := cmpM.FPM.
    (** We construct an inverse to it using corecursion. *)
    Module prod_from_M <: FunctionM cmpM.PFM cmpM.PM.
      Definition m@{i} : cmpM.PFM.m@{i} -> cmpM.PM.m@{i}
        := fun z => ( FXM.from (fst z) , FYM.from (snd z) ).
    End prod_from_M.
    Module cmpinvM <: FunctionM cmpM.PFM FPM
      := FPM.corecM cmpM.PFM prod_from_M.
    (** We prove the first homotopy *)
    Module cmpinv_o_cmp_M <: FunctionM FPM FPM
      := ComposeM FPM cmpM.PFM FPM cmpinvM cmpM.
    Module idmap_FPM <: FunctionM FPM FPM
      := IdmapM FPM.
    Module cip_FPM := FPM.coindpathsM FPM cmpinv_o_cmp_M idmap_FPM.
    Module cip_FPHM <: HomotopyM FPM cmpM.PM cip_FPM.fhM cip_FPM.fkM.
      Definition m@{i} : forall x, cip_FPM.fhM.m@{i} x = cip_FPM.fkM.m@{i} x.
      Proof.
        intros x.
        refine (concat (cmpinvM.m_beta (cmpM.m x)) _).
        apply path_prod@{i i}; simpl.
        - exact (cmpM.FfstM.mM.m_beta x).
        - exact (cmpM.FsndM.mM.m_beta x).
      Defined.
    End cip_FPHM.
  End isequiv_F_prod_cmp_M.

End Comodality_Theory.
