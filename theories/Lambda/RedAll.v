Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.Red.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section beta_all.
  Context {sym : Type}.
  Context {typ : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym sym}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  (** NOTE: I should extend [delta] with [vars]
   ** - that means that its specification is exactly the same as [beta_all]
   **)
  Variable delta : expr typ sym -> list (expr typ sym) -> expr typ sym.

  Fixpoint get_var (v : nat) (ls : list (option (expr typ sym))) (acc : nat)
  : expr typ sym :=
    match ls with
      | nil => Var (acc + v)
      | None :: ls =>
        match v with
          | 0 => Var acc
          | S v => get_var v ls (S acc)
        end
      | Some e :: ls =>
        match v with
          | 0 => lift 0 acc e
          | S v => get_var v ls acc
        end
    end.

(*
  Lemma get_var_ok
  : forall n ls v e,
      get_var n ls v =
      (e = Var (n + v)) \/
      True.
  Proof.
    induction n; simpl.
    - destruct ls; simpl; intros.
      + left. rewrite Plus.plus_0_r in H. auto.
      + destruct o.
        * admit.
        * left. auto.
    - destruct ls; simpl; do 2 intro.
      + rewrite <- plus_n_Sm. rewrite Plus.plus_comm.
        left; auto.
      + destruct o.
        * specialize (IHn ls (S v) _ eq_refl).

             *
*)

  Fixpoint beta_all
           (args : list (expr typ sym))
           (vars : list (option (expr typ sym)))
           (e : expr typ sym) : expr typ sym :=
    match e with
      | App e' e'' =>
        beta_all (beta_all nil vars e'' :: args) vars e'
      | Abs t e' =>
        match args with
          | nil => Abs t (beta_all nil (None :: vars) e') (** args = nil **)
          | a :: args => beta_all args (Some a :: vars) e'
        end
      | Var v =>
        delta (get_var v vars 0) args
      | e => delta e args
    end.

  (** the default delta function is [apps] **)
  Definition delta_sound
  := forall e es ts tus tvs t val,
       exprD' ts tus tvs t (apps e es) = Some val ->
       exists val',
         exprD' ts tus tvs t (delta e es) = Some val' /\
         forall us vs,
           val us vs = val' us vs.

  Hypothesis deltaOk : delta_sound.

  Variable ts : list Type.

  Inductive EnvForall {A} (R : A -> forall t : typ, typD ts t -> Prop)
  : list A -> forall tvs, hlist (typD ts) tvs -> Prop :=
  | EnvForall_nil : EnvForall R nil Hnil
  | EnvForall_cons : forall e es t ts v vs,
                       R e t v ->
                       @EnvForall A R es ts vs ->
                       @EnvForall A R (e :: es) (t :: ts) (Hcons v vs).

  Lemma Forall2_sem2
  : forall T U (P : T -> U -> Prop) xs ys,
      Forall2 P xs ys ->
      forall v y,
        nth_error ys v = Some y ->
        exists x, nth_error xs v = Some x /\
                  P x y.
  Proof.
    clear. induction 1; simpl; intros.
    { destruct v; inversion H. }
    { destruct v.
      { simpl in *. eexists; split; eauto.
        inversion H1. subst. auto. }
      { simpl in *. eauto. } }
  Qed.

  Section Forall2i.
    Variables T U : Type.

    Section def.
      Variable P : nat -> T -> U -> Prop.

      Inductive Forall2i : nat -> list T -> list U -> Prop :=
      | F2i_nil : forall n, Forall2i n nil nil
      | F2i_cons : forall x xs y ys n, P n x y ->
                                       Forall2i (S n) xs ys ->
                                       Forall2i n (x :: xs) (y :: ys).
    End def.

    Variable P Q : nat -> T -> U -> Prop.
    Lemma Forall2i_shift
    : forall m n xs ys,
        (forall n x y, P n x y -> Q (m + n) x y) ->
        Forall2i P n xs ys ->
        Forall2i Q (m + n) xs ys.
    Proof.
      clear. induction 2.
      { constructor. }
      { constructor; eauto.
        replace (m + S n) with (S (m + n)) in IHForall2i by omega.
        assumption. }
    Qed.
  End Forall2i.

(*
  Lemma beta_all_respectful
  : forall args args' vars vars' e e',
      Forall
      beta_all args vars e =
      beta_all args' vars' e'
*)

  Lemma exprD'_App_Abs
  : forall ts tus tvs t t0 e ex val,
      exprD' ts tus tvs t0 (App (Abs t e) ex) = Some val ->
      exprD' ts tus tvs t0 (substitute' 0 ex e) = Some val.
  Proof.
    intros.
    autorewrite with exprD_rw in *; simpl in *.
    forward.
    autorewrite with exprD_rw in *; simpl in *.
    inv_all; subst.
    rewrite typ2_match_zeta in H0; eauto.
    rewrite eq_option_eq in H0.
    forward. inv_all; subst.
    destruct r.
    generalize (@substitute'_sound _ _ _ _ _ _ _ _ _ ts0 tus e nil ex _ eq_refl tvs t1 t0).
    simpl. Cases.rewrite_all_goal.
    intros. forward.
    f_equal. unfold Open_App.
    unfold OpenT, ResType.OpenT.
    repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
    clear - H4.
    apply functional_extensionality; intro.
    apply functional_extensionality; intro.
    repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
    specialize (H4 x Hnil x0).
    simpl in *.
    autorewrite with eq_rw. auto.
  Qed.

  Lemma Forall2i_nth_snd
  : forall T U (P : nat -> T -> U -> Prop) i xs ys,
      Forall2i P i xs ys ->
      forall n y,
        nth_error ys n = Some y ->
        exists x, nth_error xs n = Some x /\
                  P (i + n) x y.
  Proof.
    induction 1.
    - intros ? ?; rewrite nth_error_nil. congruence.
    - destruct n0; simpl; intros.
      + eexists; split; eauto.
        rewrite Plus.plus_0_r. inv_all.
        subst. assumption.
      + rewrite <- plus_n_Sm.
        simpl in *. auto.
  Qed.

  Lemma apply_sem_same
  : forall tus tvs args t f f' t' val val',
      apply_sem' (ts := ts) (tus := tus) (tvs := tvs) T2 RS t f args t' = Some val ->
      apply_sem' T2 RS t f' args t' = Some val' ->
      forall us vs,
        f us vs = f' us vs ->
        val us vs = val' us vs.
  Proof.
    induction args.
    + simpl.
      intros. forward. inv_all. subst.
      unfold Rcast, Relim, OpenT, ResType.OpenT.
      repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
      rewrite H1. reflexivity.
    + simpl. intros.

      arrow_case ts t.
    - unfold Relim, OpenT, ResType.OpenT in *; autorewrite with eq_rw in *.
      forward.
      specialize (IHargs _ _ _ _ _ _ H0 H3); clear H0 H3.
      simpl in *. eapply IHargs.
      autorewrite with eq_rw.
      rewrite H1. reflexivity.
    - congruence.
  Qed.

  Lemma apply_sem'_same_args_safe
  : forall tus tvs args t f f' t' val,
      apply_sem' (ts := ts) (tus := tus) (tvs := tvs) T2 RS t f args t' = Some val ->
      exists val', apply_sem' (ts := ts) (tus := tus) (tvs := tvs) T2 RS t f' args t' = Some val'.
  Proof.
    induction args; simpl; intros.
    + forward. eauto.
    + arrow_case ts t.
      unfold Relim, OpenT, ResType.OpenT in *.
      repeat first [ rewrite eq_Const_eq in * | rewrite eq_Arr_eq in * ].
      forward.
      eapply IHargs in H1. eapply H1. congruence.
  Qed.

(*
  Inductive EnvForall {A} (R : A -> forall t : typ, typD ts t -> Prop)
  : list A -> forall tvs, hlist (typD ts) tvs -> Prop :=
  | EnvForall_nil : EnvForall R nil Hnil
  | EnvForall_cons : forall e es t ts v vs,
                       R e t v ->
                       @EnvForall A R es ts vs ->
                       @EnvForall A R (e :: es) (t :: ts) (Hcons v vs).
*)
  Inductive EnvModels tus (us : hlist (typD ts) tus)
  : forall tvs, list (option (expr typ sym)) -> hlist (typD ts) tvs -> Prop :=
  | EnvModels_nil : @EnvModels tus us nil nil Hnil
  | EnvModels_None : forall t tvs vs val vals,
                       @EnvModels tus us tvs vs vals ->
                       @EnvModels tus us (t :: tvs) (None :: vs) (Hcons val vals)
  | EnvModels_Some : forall t tvs e vs val vals val',
                       exprD' ts tus tvs t e = Some val' ->
                       val' us vals = val ->
                       @EnvModels tus us tvs vs vals ->
                       @EnvModels tus us (t :: tvs) (Some e :: vs) (Hcons val vals).

(*
  Theorem beta_all_sound
  : forall tus e tvs t val args vars,
      Forall2i (fun n t e =>
                  match e with
                    | None => True
                    | Some e =>
                      exists val, exprD' ts tus (skipn (S n) tvs) t e = Some val
                  end) 0 tvs vars ->
      exprD' ts tus tvs t (apps (substitute e) args) = Some val ->
      exists val',
        exprD' ts tus tvs t (beta_all args vars e) = Some val' /\
        forall us vs,
          @EnvModels tus us tvs vars vs ->
          val us vs = val' us vs.


  (** TODO: This is not true **)
  Theorem beta_all_sound
  : forall tus e tvs t val args vars,
      Forall2i (fun n t e => match e with
                               | None => True
                               | Some e =>
                                 exists val, exprD' ts tus (skipn (S n) tvs) t e = Some val
                             end) 0 tvs vars ->
      exprD' ts tus tvs t (apps e args) = Some val ->
      exists val',
        exprD' ts tus tvs t (beta_all args vars e) = Some val' /\
        forall us vs,
          @EnvModels tus us tvs vars vs ->
          val us vs = val' us vs.
  Proof.
    induction e; simpl; intros.
    { rewrite exprD'_apps in H0; eauto.
      unfold apps_sem' in H0. forward.
      autorewrite with exprD_rw in H1. simpl in H1.
      forward. inv_all; subst.
      simpl in H0. destruct r.
      clear H4. unfold Rcast_val, Rcast, Relim, Rsym in H2. simpl in H2.
      { admit. } }
    { eapply deltaOk in H0.
      destruct H0 as [ ? [ ? ? ] ].
      eexists; split; eauto. }
    { generalize H0.
      rewrite exprD'_apps in H0; eauto.
      unfold apps_sem' in H0.
      forward.
      autorewrite with exprD_rw in *; simpl in *; forward.
      change e2 with (apps e2 nil) in H5.
      eapply IHe2 with (vars := vars) in H5; eauto; clear IHe2.
      forward_reason.
      assert (exists val',
                exprD' ts tus tvs t (apps (App e1 (beta_all nil vars e2)) args) = Some val' /\
             forall us vs,
               @EnvModels tus us tvs vars vs ->
               val us vs = val' us vs).
      { rewrite exprD'_apps; eauto.
        unfold apps_sem'. simpl.
        Cases.rewrite_all_goal.
        assert (typeof_expr ts tus tvs (beta_all nil vars e2) = Some t1) by admit.
        Cases.rewrite_all_goal.
        autorewrite with exprD_rw. simpl.
        Cases.rewrite_all_goal.
        inv_all; subst.
        consider (apply_sem' T2 RS t0 (Open_App o0 x) args t); intros.
        { eexists; split; eauto.
          intros.
          specialize (H8 _ _ H10).
          clear H2 H10 H.
          apply (apply_sem_same _ _ _ _ _ H3 H6 us vs).
          unfold Open_App.
          unfold Relim, OpenT, ResType.OpenT.
          repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          rewrite H8. reflexivity. }
        { exfalso.
          eapply apply_sem'_same_args_safe in H3.
          destruct H3. rewrite H3 in H6. congruence. } }
      { destruct H9 as [ ? [ ? ? ] ].
        change (apps (App e1 (beta_all nil vars e2)) args)
          with (apps e1 (beta_all nil vars e2 :: args)) in H9.
        eapply IHe1 in H9; eauto.
        forward_reason. eexists; split; eauto.
        intros. rewrite <- H11; eauto. } }
    { destruct args.
      { simpl in *.
        autorewrite with exprD_rw in *; simpl in *.
        arrow_case ts t0.
        { clear H1. red in x1. subst. simpl in *.
          rewrite eq_option_eq in *.
          forward. inv_all; subst.
          change e with (apps e nil) in H2.
          eapply IHe with (vars := None :: vars) in H2; eauto.
          { forward_reason. Cases.rewrite_all_goal.
            eexists; split; eauto.
            intros.
            unfold OpenT, ResType.OpenT.
            repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
            match goal with
              | |- match ?X with _ => _ end = match ?Y with _ => _ end =>
                change Y with X ;
                eapply match_eq_match_eq with (pf := X) (F := fun x => x)
            end.
            eapply functional_extensionality.
            intros.
            eapply H2.
            constructor; auto. }
          { constructor; auto.
            revert H.
            eapply (@Forall2i_shift _ _ _ _ 1 0). intros.
            simpl; auto. } }
        { congruence. } }
      { simpl in *.
        rewrite exprD'_apps in H0; eauto.
        unfold apps_sem' in H0; eauto. forward.
        autorewrite with exprD_rw in H1. simpl in H1.
        forward.
        assert (Forall2i
          (fun (n : nat) (t1 : typ) (e1 : option (expr typ sym)) =>
           match e1 with
           | Some e2 =>
               exists val0 : OpenT ts tus (skipn (S n) (t2 :: tvs)) (typD ts t1),
                 exprD' ts tus (skipn (S n) (t2 :: tvs)) t1 e2 = Some val0
           | None => True
           end) 0 (t2 :: tvs) (Some e0 :: vars)).
        { constructor. simpl. eauto.
          revert H.
          eapply (@Forall2i_shift _ _ _ _ 1 0).
          destruct y; auto. }
        specialize (fun val => IHe (t2 :: tvs) t0 val (map (lift 0 1) args) (Some e0 :: vars) H6).
        assert (exists ZZZ, exprD' ts tus (t2 :: tvs) t0 (apps e (map (lift 0 1) args)) = Some ZZZ).
        { rewrite exprD'_apps; eauto. admit. }

admit.
(*

        autorewrite with exprD_rw in H3; simpl in H3.
        rewrite typ2_match_zeta in H3 by eauto.
        rewrite eq_option_eq in H3. forward.
        inv_all; subst.

        admit. *) } }
    { eapply deltaOk in H0.
      forward_reason. eauto. }
  Qed. *)

End beta_all.

(*
Section test.
  Context {sym : Type}.
  Context {typ : Type}.
  Context {RT : RType typ}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym sym}.

  Context {RTOk : RTypeOk}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Context {ED_typ : EqDec _ (@eq typ)}.

  Eval compute in fun t =>
                    beta_all (@apps typ sym) nil nil (App (Abs t (App (Var 10) (Abs t (Var 1)))) (Var 0)).
*)