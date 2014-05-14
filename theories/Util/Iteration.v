Require Import Coq.Lists.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.

Set Implicit Arguments.
Set Strict Implicit.

Section iteration.
  Context (T U : Type) (f : T -> option U).

  Fixpoint first_success  (ls : list T) : option U :=
    match ls with
      | nil => None
      | l :: ls =>
        match f l with
          | None => first_success ls
          | x => x
        end
    end.

  Lemma first_success_sound
  : forall ls val,
      first_success ls = Some val ->
      exists l,
        In l ls /\ f l = Some val.
  Proof.
    induction ls; simpl; intros.
    - congruence.
    - consider (f a); intros.
      + exists a. inv_all; subst. auto.
      + apply IHls in H0. destruct H0. intuition. eauto.
  Qed.

  Variable (f' : T -> U -> option U).

  Fixpoint all_success (ls : list T) (acc : U)
  : option U :=
    match ls with
      | nil => Some acc
      | l :: ls =>
        match f' l acc with
          | None => None
          | Some x => all_success ls x
        end
    end.

  Fixpoint filter_map (ls : list T) : list U :=
    match ls with
      | nil => nil
      | l :: ls => match f l with
                     | None => filter_map ls
                     | Some x => x :: filter_map ls
                   end
    end.

  Lemma filter_map_sound
  : forall ls,
      Forall (fun x => exists l, In l ls /\ f l = Some x)
             (filter_map ls).
  Proof.
    clear. induction ls; simpl; intros.
    { constructor. }
    { assert (Forall (fun x : U => exists l : T, (a = l \/ In l ls) /\ f l = Some x)
                     (filter_map ls)).
      { eapply Forall_impl; eauto.
        simpl in *. intuition.
        destruct H as [ ? [ ? ? ] ].
        eexists; split. right. eassumption. eauto. }
      { consider (f a); intros; auto.
        constructor; eauto. } }
  Qed.

  Lemma in_filter_map_iff : forall ls x,
                              List.In x (filter_map ls) <->
                              exists y, f y = Some x /\ List.In y ls.
  Proof.
    clear.
    induction ls; simpl.
    { intuition. destruct H; intuition. }
    { intuition.
      { consider (f a); intros.
        { destruct H0. subst. eauto.
          eapply IHls in H0. destruct H0. intuition; eauto. }
        { eapply IHls in H0. destruct H0; intuition; eauto. } }
      { destruct H. destruct H.
        destruct H0; subst.
        { rewrite H. left. auto. }
        { destruct (f a); try right; apply IHls; eauto. } } }
  Qed.

End iteration.
