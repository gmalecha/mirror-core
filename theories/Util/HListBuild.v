Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist_build_option.
  Context {T : Type} (F : T -> Type).
  Context {U : Type}.
  Variable (f : forall x : T, U -> option (F x)).

  Fixpoint hlist_build_option (ls : list T) (ls' : list U)
  : option (hlist F ls) :=
    match ls as ls , ls' return option (hlist F ls) with
    | nil , nil => Some Hnil
    | l :: ls , l' :: ls' =>
      match hlist_build_option ls ls' with
      | None => None
      | Some res =>
        match f l l' with
        | None => None
        | Some x =>
          Some (Hcons x res)
        end
      end
    | _ , _ => None
    end.

  Lemma hlist_build_option_app_if
    : forall a b c d e f,
      length a = length c ->
      hlist_build_option (a ++ b) (c ++ d) = Some (hlist_app e f) ->
      hlist_build_option a c = Some e /\
      hlist_build_option b d = Some f.
  Proof.
    clear.
    induction a; simpl; intros.
    { intuition; destruct c; simpl in *; try congruence.
      rewrite (hlist_eta e). reflexivity.
      rewrite (hlist_eta e) in H0. simpl in H0. assumption. }
    { destruct c; simpl in *; try congruence.
      inversion H; clear H; subst.
      forward. inv_all.
      rewrite (hlist_eta e) in *.
      simpl in *.
      inv_all. subst.
      eapply IHa in H; auto.
      destruct H. rewrite H. eauto. }
  Qed.

  Lemma hlist_build_option_app_only_if
  : forall a b c d e f,
      hlist_build_option a c = Some e ->
      hlist_build_option b d = Some f ->
      hlist_build_option (a ++ b) (c ++ d) = Some (hlist_app e f).
  Proof.
    induction a; simpl; intros; forward.
    { rewrite (hlist_eta e). simpl. auto. }
    { inv_all; subst.
      simpl. eapply IHa in H0; eauto. rewrite H0. rewrite H2. reflexivity. }
  Qed.
End hlist_build_option.
