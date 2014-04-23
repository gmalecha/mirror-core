Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SubstI2.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: These should be moved **)
Lemma Forall_cons_iff
: forall {T} (F : T -> Prop) a b, Forall F (a :: b) <-> (F a /\ Forall F b).
Proof.
  split; intros. inversion H; auto. constructor; intuition.
Qed.

Theorem Forall_map {T U} (F : T -> U) (P : U -> Prop)
: forall ls,
    Forall P (map F ls) <->
    Forall (fun x => P (F x)) ls.
Proof.
  induction ls; simpl; intros.
  { split; constructor. }
  { do 2 rewrite Forall_cons_iff.
    rewrite IHls. reflexivity. }
Qed.

(** This is the simplest form of substitution, it only supports lookup.
 ** But, it is efficient to represent.
 **)
Section list_subst.

  (** the [expr] type requires a notion of unification variable **)
  Variable expr : Type.
  Let uvar : Type := nat.

  Inductive list_subst : Type :=
  | Snil : list_subst
  | Sfilled : expr -> list_subst -> list_subst
  | Sempty : list_subst -> list_subst.

  Fixpoint list_subst_lookup (u : uvar) (l : list_subst) : option expr :=
    match l with
      | Snil => None
      | Sfilled x l => match u with
                         | 0 => Some x
                         | S u => list_subst_lookup u l
                       end
      | Sempty l => match u with
                      | 0 => None
                      | S u => list_subst_lookup u l
                    end
    end.

  Fixpoint list_subst_domain' (l : list_subst) (u : uvar) : list uvar :=
    match l with
      | Snil => nil
      | Sfilled _ l => u :: list_subst_domain' l (S u)
      | Sempty l => list_subst_domain' l (S u)
    end.

  Definition list_subst_domain (l : list_subst) : list uvar :=
    list_subst_domain' l 0.

  Local Instance Subst_list_subst : @SubstI2.Subst list_subst expr :=
  { lookup := list_subst_lookup
  ; domain := list_subst_domain
  }.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : Expr typD expr.

  Definition WellTyped_for_domain (T : Type) (S : Subst T expr)
             (tus tvs : EnvI.tenv typ) (s : T) : Prop :=
    Forall (fun u =>
              match nth_error tus u , lookup u s with
                | _ , None => True
                | None , Some _ => False
                | Some t , Some e =>
                  Safe_expr tus tvs e t
              end) (domain s).

  Definition substD_for_domain (T : Type) (S : Subst T expr)
             (us vs : EnvI.env typD) (s : T) : Prop :=
    Forall (fun u =>
                match nth_error us u , lookup (expr := expr) u s with
                  | _ , None => True
                  | None , Some _ => False
                  | Some (existT t val) , Some e =>
                    match exprD us vs e t with
                      | Some v => v = val
                      | None => False
                    end
                end) (domain s).

  Lemma list_subst_domain'_gt
  : forall l u,
      Forall (fun x => x >= u) (list_subst_domain' l u).
  Proof.
    induction l; simpl; intros.
    { constructor. }
    { constructor; eauto.
      eapply Forall_impl; [ | eapply IHl ].
      simpl. intros. omega. }
    { eapply Forall_impl; [ | eapply IHl ].
      simpl. intros. omega. }
  Qed.

  Lemma list_subst_domain_ok
  : forall (s : list_subst) (ls : list nat),
      True -> domain s = ls -> forall n : nat, In n ls <-> lookup n s <> None.
  Proof.
    simpl. unfold list_subst_domain. intros s ls. intro. clear H.
    change (list_subst_domain' s 0 = ls ->
            forall n : nat, In (0 + n) ls <-> list_subst_lookup n s <> None).
    generalize 0. revert ls.
    induction s; simpl; intros.
    { subst. split. inversion 1. destruct n0; compute; auto. }
    { subst. split.
      { destruct 1.
        { assert (n0 = 0) by omega. clear H. subst. compute. congruence. }
        { specialize (IHs _ (S n) eq_refl).
          destruct n0. simpl in *. congruence.
          specialize (IHs n0).
          simpl. apply IHs.
          replace (n + S n0) with (S n + n0) in * by omega. assumption. } }
      { destruct n0.
        { simpl; intros. left. omega. }
        { simpl. intros. right.
          eapply IHs in H. 2: reflexivity.
          revert H. instantiate (1 := S n).
          replace (S n + n0) with (n + S n0) by omega. auto. } } }
    { subst; split.
      { destruct n0; simpl.
        { intro. exfalso.
          generalize (list_subst_domain'_gt s (S n)).
          intro. rewrite Forall_forall in H0.
          apply H0 in H. omega. }
        { specialize (IHs _ (S n) eq_refl n0).
          replace (S n + n0) with (n + S n0) in * by omega.
          destruct IHs; auto. } }
      { destruct n0; simpl.
        { congruence. }
        { specialize (IHs _ (S n) eq_refl n0).
          replace (S n + n0) with (n + S n0) in * by omega.
          destruct IHs; auto. } } }
  Qed.

  Lemma list_subst1
  : forall (u v : tenv typ) (s : list_subst) (uv : nat) (e : expr),
      True ->
      WellTyped_for_domain Subst_list_subst u v s ->
      lookup uv s = Some e ->
      exists t : typ, nth_error u uv = Some t /\ Safe_expr u v e t.
  Proof.
    intros.
    red in H0.
    rewrite Forall_forall in H0.
    assert (lookup uv s <> None) by congruence.
    rewrite <- (list_subst_domain_ok s I eq_refl uv) in H2.
    apply H0 in H2.
    rewrite H1 in *.
    destruct (nth_error u uv); eauto.
    inversion H2.
  Qed.

  Lemma list_subst2
  : forall (u v : env typD) (s : list_subst) (uv : nat) (e : expr),
      True ->
      lookup uv s = Some e ->
      substD_for_domain Subst_list_subst u v s ->
      exists val : sigT (typD nil),
        nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val).
  Proof.
    unfold substD_for_domain. intros.
    rewrite Forall_forall in H1.
    assert (lookup uv s <> None) by congruence.
    rewrite <- (list_subst_domain_ok s I eq_refl uv) in H2.
    apply H1 in H2.
    rewrite H0 in *.

    forward. subst.
    eexists; split; eauto.
  Qed.

  Local Instance SubstOk_list_subst : SubstOk _ Subst_list_subst :=
  { WellFormed_subst := fun _ => True
  ; WellTyped_subst := WellTyped_for_domain Subst_list_subst
  ; substD := substD_for_domain Subst_list_subst
  }.
  Proof.
    exact list_subst1.
    exact list_subst2.
    exact list_subst_domain_ok.
  Defined.

  Section add.
    Variable e : expr.

    Fixpoint list_subst_add (u : uvar) (l : list_subst) : list_subst :=
      match u with
        | 0 => Sfilled e match l with
                           | Snil => Snil
                           | Sfilled _ l => l
                           | Sempty l => l
                         end
        | S u => match l with
                   | Snil => Sempty (list_subst_add u Snil)
                   | Sfilled x l => Sfilled x (list_subst_add u l)
                   | Sempty l => Sempty (list_subst_add u l)
                 end
      end.

    Lemma list_subst_add_eq
    : forall u l,
        lookup u (list_subst_add u l) = Some e.
    Proof.
      clear. induction u; simpl; intros; auto.
      { destruct l; simpl; rewrite IHu; auto. }
    Qed.

    Lemma list_subst_add_neq
    : forall u u' l,
        u <> u' ->
        lookup u' (list_subst_add u l) = lookup u' l.
    Proof.
      clear. induction u; simpl; intros; auto.
      { destruct l; simpl.
        { destruct u'; try congruence.
          simpl. destruct u'; simpl; auto. }
        { destruct u'; try congruence. reflexivity. }
        { destruct u'; try congruence. reflexivity. } }
      { destruct l; simpl.
        { destruct u'; simpl; auto.
          rewrite IHu.
          destruct u'; reflexivity. omega. }
        { destruct u'; simpl; auto. }
        { destruct u'; simpl; auto. } }
    Qed.

  End add.

  Section to_list_subst.
    Variable T : Type.
    Variable Subst_T : Subst T expr.
    Variable SubstOk_T : SubstOk _ _.


    Section prime.
      Variable s : T.

      Fixpoint to_list_subst' (dom : list uvar) : list_subst :=
        match dom with
          | nil => Snil
          | d :: dom => match lookup d s with
                          | None => to_list_subst' dom
                          | Some e => list_subst_add e d (to_list_subst' dom)
                        end
        end.

      Definition to_list_subst : list_subst :=
        to_list_subst' (domain s).
    End prime.

    Lemma subst_to_list_subst_lookup
    : forall s, WellFormed_subst s ->
                forall n, lookup n s = lookup n (to_list_subst s).
    Proof.
      unfold to_list_subst.
      intros.
      generalize (WellFormed_domain _ H eq_refl n).
      consider (lookup n s); intros.
      { assert (Some e <> None) by congruence.
        rewrite <- H1 in H2.
        clear - H0 H2.
        revert H2.
        induction (domain s); intros.
        { inversion H2. }
        { consider (a ?[ eq ] n); intros.
          { subst. simpl.
            rewrite H0.
            rewrite list_subst_add_eq. reflexivity. }
          { simpl.
            destruct H2. congruence.
            destruct (lookup a s); rewrite IHl; auto.
            rewrite list_subst_add_neq; eauto. } } }
      { assert (~In n (domain s)).
        { rewrite H1. congruence. }
        clear - H2.
        generalize dependent n.
        induction (domain s).
        { simpl. intros.
          destruct n; reflexivity. }
        { simpl; intros.
          destruct (lookup a s).
          { rewrite list_subst_add_neq. apply IHl. intuition. intuition. }
          { apply IHl. intuition. } } }
    Qed.

    Theorem WellFormed_to_list_subst
    : forall s, WellFormed_subst s -> WellFormed_subst (to_list_subst s).
    Proof. compute. auto. Qed.

    Theorem WellTyped_to_list_subst
    : forall tus tvs s,
        WellFormed_subst s ->
        WellTyped_subst tus tvs s ->
        WellTyped_subst tus tvs (to_list_subst s).
    Proof.
      intros.
      generalize (@WellFormed_domain _ _ _ _ _ _ SubstOk_T s _ H eq_refl).
      red; simpl. red; simpl.
      intros.
      apply Forall_forall. intros.
      change (list_subst_lookup) with (@lookup _ _ Subst_list_subst).
      rewrite <- subst_to_list_subst_lookup; auto.
      consider (lookup x s); intros; forward.
      eapply WellTyped_lookup in H3; eauto.
      forward_reason. Cases.rewrite_all_goal.
      assumption.
    Qed.

    Theorem substD_to_list_subst
    : forall us vs s,
        WellFormed_subst s ->
        substD us vs s ->
        substD us vs (to_list_subst s).
    Proof.
      intros.
      unfold substD. simpl. unfold substD_for_domain.
      apply Forall_forall; intros.
      rewrite list_subst_domain_ok in H1; eauto.
      consider (lookup x (to_list_subst s)); try congruence; intros.
      rewrite <- subst_to_list_subst_lookup in H1; auto.
      generalize H.
      eapply WellFormed_domain with (n := x) in H; try reflexivity.
      rewrite H1 in *. intro.
      eapply substD_lookup in H1; eauto.
      forward_reason. Cases.rewrite_all_goal.
      destruct x0. simpl in *. Cases.rewrite_all_goal.
      reflexivity.
    Qed.
  End to_list_subst.
End list_subst.