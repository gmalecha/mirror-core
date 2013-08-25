Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Cases.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable ts : types.

  Fixpoint lift' (s l : nat) (e : expr) : expr :=
    match e with
      | Var v =>
        if NPeano.ltb v s then e
        else Var (v + l)
      | Func _ _ => e
      | App e e' => App (lift' s l e) (lift' s l e')
      | Abs t e => Abs t (lift' (S s) l e)
      | UVar u => e
      | Equal t e1 e2 => Equal t (lift' s l e1) (lift' s l e2)
      | Not e => Not (lift' s l e)
    end.

  Definition lift (s l : nat) : expr -> expr :=
    match l with
      | 0 => fun x => x
      | _ => lift' s l
    end.

  Fixpoint lower' (s l : nat) (e : expr) : option expr :=
    match e with
      | Var v =>
        if NPeano.ltb v s then Some e
        else if NPeano.ltb (v - s) l then None
             else Some (Var (v - l))
      | Func _ _ => Some e
      | App e e' =>
        match lower' s l e , lower' s l e' with
          | Some e , Some e' => Some (App e e')
          | _ , _ => None
        end
      | Abs t e =>
        match lower' (S s) l e with
          | None => None
          | Some e => Some (Abs t e)
        end
      | UVar u => Some e
      | Equal t e1 e2 =>
        match lower' s l e1 , lower' s l e2 with
          | Some e1 , Some e2 =>
            Some (Equal t e1 e2)
          | _ , _ => None
        end
      | Not e =>
        match lower' s l e with
          | Some e => Some (Not e)
          | None => None
        end
    end.

  Definition lower s l : expr -> option expr :=
    match l with
      | 0 => @Some _
      | _ => lower' s l
    end.

  Theorem lower_lower' : forall e s l,
                           lower s l e = lower' s l e.
  Proof.
    unfold lower. destruct l; simpl; auto.
    clear; revert s.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ => rewrite <- H
           end; auto.
    rewrite <- Minus.minus_n_O. destruct (NPeano.ltb v s); reflexivity.
  Qed.

  Lemma lift'_0 : forall e s, lift' s 0 e = e.
  Proof.
    induction e; simpl; intros;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end; auto.
    { consider (NPeano.ltb v s); auto. }
  Qed.

  Lemma lift_lift' : forall s l e, lift s l e = lift' s l e.
  Proof.
    destruct l; simpl; intros; auto using lift'_0.
  Qed.

  Fixpoint mentionsU (u : nat) (e : expr) {struct e} : bool :=
    match e with
      | Var _
      | Func _ _ => false
      | UVar u' => EqNat.beq_nat u u'
      | App f e => if mentionsU u f then true else mentionsU u e
      | Abs _ e => mentionsU u e
      | Equal _ e1 e2 => if mentionsU u e1 then true else mentionsU u e2
      | Not e => mentionsU u e
    end.

  Theorem lift_lower : forall e s l,
                         lower s l (lift s l e) = Some e.
  Proof.
    clear; intros.
    rewrite lower_lower'. rewrite lift_lift'.
    generalize dependent s. revert l.
    induction e; simpl; intros;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
           end;
    inv_all; subst; auto.
    { case_eq (NPeano.ltb v s); simpl; intros.
      { rewrite H. reflexivity. }
      { consider (NPeano.ltb v s); try congruence; intros.
        consider (NPeano.ltb (v + l) s); intros; try solve [ exfalso; omega ].
        consider (NPeano.ltb (v + l - s) l); intros; try solve [ exfalso; omega ].
        f_equal. f_equal.
        rewrite NPeano.Nat.add_sub. auto. } }
  Qed.

  Theorem lower_lift : forall e e' s l,
                         lower s l e = Some e' ->
                         e = lift s l e'.
  Proof.
    intros.
    rewrite lower_lower' in H. rewrite lift_lift'.
    generalize dependent s. revert l.
    revert e'.
    induction e; simpl; intros;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
           end;
    inv_all; subst; auto.
    consider (NPeano.ltb v s); intros.
    { inv_all. subst. simpl. consider (NPeano.ltb v s); intros; auto.
      exfalso; omega. }
    { consider (NPeano.ltb (v - s) l); try congruence; intros.
      inv_all; subst. simpl. consider (NPeano.ltb (v - l) s); intros.
      exfalso. omega. f_equal. rewrite NPeano.Nat.sub_add. auto. omega. }
  Qed.

  Lemma typeof_expr_lift : forall tfs us vs vs' vs'' e,
    ExprT.typeof_expr tfs us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) = 
    ExprT.typeof_expr tfs us (vs ++ vs'') e.
  Proof.
    clear. intros. rewrite lift_lift'.
    revert vs.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ =>
               erewrite H
           end; auto.
    { consider (NPeano.ltb v (length vs)); simpl; intros;
      repeat ((rewrite nth_error_app_L by omega) ||
                                                 (rewrite nth_error_app_R by omega)); auto.
      f_equal. omega. }
    { change (t :: vs ++ vs' ++ vs'') with
      ((t :: vs) ++ vs' ++ vs'').
      rewrite IHe. auto. }
  Qed.

  Lemma typeof_env_app : forall (a b : EnvI.env (typD ts)),
    EnvI.typeof_env (a ++ b) = EnvI.typeof_env a ++ EnvI.typeof_env b.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_app. reflexivity.
  Qed.
  Lemma typeof_env_length : forall (a : EnvI.env (typD ts)),
    length (EnvI.typeof_env a) = length a.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_length. reflexivity.
  Qed.


  Theorem exprD_lift : forall (fs : functions ts) us vs vs' vs'' e t,
                         exprD fs us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) t =
                         exprD fs us (vs ++ vs'') e t.
  Proof.
    intros. rewrite lift_lift'. revert t; revert vs.
    induction e; simpl; intros; autorewrite with exprD_rw; auto.
    { consider (NPeano.ltb v (length vs)); intros.
      { autorewrite with exprD_rw. unfold EnvI.lookupAs.
        repeat rewrite nth_error_app_L by auto. reflexivity. }
      { autorewrite with exprD_rw. unfold EnvI.lookupAs.
        repeat rewrite nth_error_app_R by omega.
        replace (v + length vs' - length vs - length vs') with (v - length vs) by omega.
        reflexivity. } }
    { repeat rewrite typeof_env_app.
      repeat rewrite <- typeof_env_length.
      rewrite <- lift_lift'. rewrite typeof_expr_lift. rewrite lift_lift'.
      destruct (ExprT.typeof_expr (ExprT.typeof_funcs fs) (EnvI.typeof_env us)
       (EnvI.typeof_env vs ++ EnvI.typeof_env vs'') e1); auto.
      destruct t0; auto. repeat rewrite typeof_env_length.
      rewrite IHe1. rewrite IHe2. reflexivity. }
    { destruct t0; auto.
      Require Import ExtLib.Tactics.EqDep.
      gen_refl.
      generalize (typeof_expr_eq_exprD_False fs us t0_1 
                (vs ++ vs' ++ vs'') (lift' (S (length vs)) (length vs') e)
                t0_2).
      generalize (typeof_expr_eq_exprD_False fs us t0_1 
                (vs ++ vs'') e t0_2).
      repeat rewrite typeof_env_app.
      replace (ExprT.typecheck_expr (ExprT.typeof_funcs fs) 
             (EnvI.typeof_env us)
             (t0_1
              :: EnvI.typeof_env vs ++
                 EnvI.typeof_env vs' ++ EnvI.typeof_env vs'')
             (lift' (S (length vs)) (length vs') e) t0_2)
        with (ExprT.typecheck_expr (ExprT.typeof_funcs fs) 
             (EnvI.typeof_env us)
             ((t0_1
              :: EnvI.typeof_env vs) ++
                 EnvI.typeof_env vs' ++ EnvI.typeof_env vs'')
             (lift' (length (t0_1 :: EnvI.typeof_env vs)) (length (EnvI.typeof_env vs')) e) t0_2).
      { Check typeof_expr_lift.
        unfold ExprT.typecheck_expr.
        rewrite <- lift_lift'.
        rewrite (typeof_expr_lift (ExprT.typeof_funcs fs) (EnvI.typeof_env us) (t0_1 :: EnvI.typeof_env vs) (EnvI.typeof_env vs') (EnvI.typeof_env vs'') e).
        simpl in *.
        intros.
        destruct (ExprT.typeof_expr (ExprT.typeof_funcs fs) 
           (EnvI.typeof_env us)
           (t0_1 :: EnvI.typeof_env vs ++ EnvI.typeof_env vs'') e); auto.
        consider (typ_eqb t0 t0_2); auto; intros.
        f_equal.
        Require Import FunctionalExtensionality.
        eapply functional_extensionality; intros.
        generalize dependent (f0 x).
        generalize dependent (f x).
        change (existT (typD ts nil) t0_1 x :: vs ++ vs' ++ vs'')
          with ((existT (typD ts nil) t0_1 x :: vs) ++ vs' ++ vs'').
        change (existT (typD ts nil) t0_1 x :: vs ++ vs'')
          with ((existT (typD ts nil) t0_1 x :: vs) ++ vs'').
        change (S (length vs)) with (length (existT (typD ts nil) t0_1 x :: vs)).
        specialize (IHe (existT (typD ts nil) t0_1 x :: vs) t0_2).
        gen_refl.
        match goal with
          | H : ?X = _ |- forall x y z w, match ?Y with _ => _ end _ = _ =>
            change Y with X
        end.
        match goal with
          | |- forall x y z w, match ?Y with _ => _ end _ = match ?X with _ => _ end _ =>
            destruct Y; destruct X; try congruence
        end.
        intros. exfalso; auto. }
      { f_equal. f_equal.
        simpl; rewrite typeof_env_length. auto.
        rewrite typeof_env_length. auto. } }
    { destruct t0; auto.
      rewrite IHe1. rewrite IHe2. auto. }
    { destruct t; auto. rewrite IHe; auto. }
  Qed.

(*
  Theorem lift_welltyped : forall fs vs vs' us (e : expr) t,
    WellTyped_expr fs us (vs ++ vs') e t ->
    forall vs'' s l,
      s = length vs -> l = length vs'' ->
      WellTyped_expr fs us (vs ++ vs'' ++ vs') (lift s l e) t.
  Proof.
    intros. rewrite lift_lift'. subst. revert vs''.
    generalize dependent t. revert vs.
    induction e; simpl; intros; unfold WellTyped_expr in *; simpl in *; forward;
      repeat match goal with
               | [ H : _ |- _ ] => erewrite H by eauto
             end; auto.
    { consider (NPeano.ltb v (length vs)); intros; simpl.
      rewrite nth_error_app_L in * by auto. auto.
      rewrite nth_error_app_R in * by auto.
      rewrite nth_error_app_R by omega.
      rewrite nth_error_app_R by omega.
      rewrite <- H. f_equal. omega. }
    { consider (typeof_expr fs us (vs ++ vs') e); intros.
      { erewrite IHe by eassumption.
        rewrite map_map.
        revert H1. clear - H. revert t; revert t0.
        induction H; simpl; intros; auto.
        intros. consider (typeof_expr fs us (vs ++ vs') x); intros; try congruence.
        erewrite H by eauto.
        destruct (type_of_apply t0 t1); eauto.
        solve [ eapply fold_left_monadic_fail in H2; intuition ].
        solve [ eapply fold_left_monadic_fail in H2; intuition ]. }
      { solve [ eapply fold_left_monadic_fail in H1; intuition ]. } }
    { unfold WellTyped_expr in *; simpl in *; auto.
      consider (typeof_expr fs us (t :: vs ++ vs') e); intros; try congruence.
      inversion H0; clear H0; subst.
      eapply IHe with (vs := t :: vs) in H. simpl in H. rewrite H.
      inv_all; subst. reflexivity. }
  Qed.
*)

End typed.
