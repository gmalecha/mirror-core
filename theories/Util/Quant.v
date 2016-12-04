Require Import ExtLib.Data.Prop.
Require Import MirrorCore.OpenT.

Section quants.
  Context {typ : Set}.
  Variable typD : typ -> Type@{Urefl}.

  Fixpoint _foralls (ls : list typ)
  : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD l,
                              _foralls ls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD l,
                              _exists ls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> _impls ls P
    end.

  Section _and.
    Context {A B : Type}.
    Variables (a : A) (b : B).
    Fixpoint _and (ls : list (A -> B -> Prop)) :=
      match ls with
        | nil => True
        | l :: nil => l a b
        | l :: ls => l a b /\ _and ls
      end.
  End _and.

  Lemma _impls_sem
  : forall ls P,
      _impls ls P <-> (Forall (fun x => x) ls -> P).
  Proof.
    induction ls; simpl; intros.
    + intuition.
    + rewrite IHls. intuition.
      inversion H0. eapply H; eauto.
  Qed.
  Lemma _exists_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_exists ls P <-> @_exists ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply exists_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.
  Lemma _forall_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_foralls ls P <-> @_foralls ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply forall_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.

  Lemma _exists_sem
  : forall ls P,
      _exists ls P <-> exists x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. exists HList.Hnil. auto.
      destruct H. rewrite (HList.hlist_eta x) in H.
      assumption.
    - intros. split.
      + destruct 1.
        eapply IHls in H.
        destruct H. eauto.
      + destruct 1.
        exists (HList.hlist_hd x).
        eapply IHls.
        exists (HList.hlist_tl x).
        rewrite (HList.hlist_eta x) in H.
        assumption.
  Qed.
  Lemma _forall_sem
  : forall ls P,
      _foralls ls P <-> forall x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. rewrite (HList.hlist_eta x).
      assumption.
    - intros. split.
      + intros.
        rewrite (HList.hlist_eta x).
        eapply IHls in H.
        eapply H.
      + intros.
        eapply IHls.
        intros. eapply H.
  Qed.
End quants.