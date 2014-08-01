Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implict.

Section mapT_equations.
  Variables T U : Type.

  Lemma list_mapT_cons
  : forall (F : T -> option U) ls a,
      Traversable.mapT F (a :: ls) =
      match match F a with
              | Some x => Some (cons x)
              | None => None
            end with
        | Some f =>
          match Traversable.mapT F ls with
            | Some x => Some (f x)
            | None => None
          end
        | None => None
      end.
  Proof. reflexivity. Qed.

  Lemma list_mapT_nil
  : forall (F : T -> option U),
      Traversable.mapT F nil = Some nil.
  Proof. reflexivity. Qed.
End mapT_equations.

Section mapT_facts.
  Variables T U : Type.

  Lemma mapT_In
  : forall (f : T -> option U) ls ls' x,
      mapT f ls = Some ls' ->
      In x ls' ->
      exists y, f y = Some x /\ In y ls.
  Proof.
    clear.
    induction ls.
    { simpl. intros; inv_all; subst. destruct H0. }
    { intros. rewrite list_mapT_cons in H.
      forward. inv_all. subst.
      destruct H0.
      { subst. eexists; split; eauto. left. reflexivity. }
      { eapply IHls in H0; eauto.
        forward_reason. eexists; split; eauto. right; assumption. } }
  Qed.

  Lemma mapT_map
  : forall V (f : U -> option V) (g : T -> U) ls,
      mapT f (map g ls) = mapT (fun x => f (g x)) ls.
  Proof.
    clear. induction ls; try solve [ simpl; auto ].
    simpl map. do 2 rewrite list_mapT_cons.
    destruct (f (g a)); auto.
    rewrite IHls. reflexivity.
  Qed.

  Lemma map_mapT
  : forall V (f : T -> option U) (g : U -> V) ls,
      match mapT f ls with
        | None => None
        | Some x => Some (map g x)
      end = mapT (fun x => match f x with
                             | None => None
                             | Some x => Some (g x)
                           end) ls.
  Proof.
    clear. induction ls; auto.
    do 2 rewrite list_mapT_cons.
    destruct (f a); auto.
    rewrite <- IHls.
    destruct (mapT f ls); auto.
  Qed.

  Lemma mapT_ext
  : forall T U (f g : T -> option U),
      (forall x, f x = g x) ->
      forall (ls : list T),
        mapT f ls = mapT g ls.
  Proof.
    clear. induction ls; auto; intros.
    do 2 rewrite list_mapT_cons.
    rewrite H. rewrite IHls. destruct (g a); auto.
  Qed.

  Lemma mapT_success
  : forall (f : T -> option U) ls ls',
      mapT f ls = Some ls' ->
      forall x, In x ls ->
                exists y, f x = Some y /\ In y ls'.
  Proof.
    clear. induction ls.
    { rewrite list_mapT_nil. intros.
      inv_all; subst. destruct H0. }
    { rewrite list_mapT_cons.
      intros. forward. inv_all; subst.
      destruct H0.
      { subst. eexists; split; eauto. left. reflexivity. }
      { eapply IHls in H0; [ | reflexivity ].
        forward_reason. eexists; split; eauto.
        right. assumption. } }
  Qed.

End mapT_facts.