Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section app_full.
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk RT}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Fixpoint apps (e : expr typ sym) (ls : list (expr typ sym)) :=
    match ls with
      | nil => e
      | l :: ls => apps (App e l) ls
    end.

  Fixpoint app_full' (e : expr typ sym) (acc : list (expr typ sym)) : expr typ sym * list (expr typ sym) :=
    match e with
      | App l r =>
        app_full' l (r :: acc)
      | _ =>
        (e, acc)
    end.

  Definition app_full (e : expr typ sym) := app_full' e nil.

  Lemma apps_app_full'
  : forall e e' ls ls',
      app_full' e ls = (e', ls') ->
      apps e ls = apps e' ls'.
  Proof.
    induction e; simpl; intros; inv_all; subst; auto.
    eapply IHe1 in H. auto.
  Qed.
End app_full.

Section substitute.
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk RT}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  Fixpoint substitute' (v : var) (w : expr typ sym) (e : expr typ sym)
  : expr typ sym :=
    match e with
      | Var v' =>
        match nat_compare v v' with
          | Eq => w
          | Lt => Var (v' - 1)
          | Gt => Var v'
        end
      | UVar u => UVar u
      | Inj i => Inj i
      | App l' r' => App (substitute' v w l') (substitute' v w r')
      | Abs t e => Abs t (substitute' (S v) (lift 0 1 w) e)
    end.

  Theorem substitute'_typed
  : forall ts tus e tvs w tvs' t t',
      typeof_expr ts tus (tvs ++ tvs') w = Some t ->
      typeof_expr ts tus (tvs ++ t :: tvs') e = Some t' ->
      typeof_expr ts tus (tvs ++ tvs') (substitute' (length tvs) w e) = Some t'.
  Proof.
    induction e; simpl; intros;
    forward; inv_all; subst; Cases.rewrite_all_goal; auto.
  Admitted.

  Theorem substitute'_sound
  : forall ts tus e tvs w e',
      substitute' (length tvs) w e = e' ->
      forall tvs' (t t' : typ),
        match exprD' ts tus (tvs ++ tvs') t w
            , exprD' ts tus (tvs ++ t :: tvs') t' e
        with
          | Some wval , Some eval =>
            match exprD' ts tus (tvs ++ tvs') t' e' with
              | None => False
              | Some val' =>
                forall (us : hlist _ tus) (gs : hlist (typD ts) tvs) (gs' : hlist (typD ts) tvs'),
                  eval us (hlist_app gs (Hcons (wval us (hlist_app gs gs')) gs')) =
                  val' us (hlist_app gs gs')
            end
          | _ , _ => True
        end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw; simpl;
    forward; inv_all; subst.
    { simpl. consider (nat_compare (length tvs) v); intros.
      { apply nat_compare_eq in H. subst.
        eapply nth_error_get_hlist_nth_Some in H2.
        destruct H2. simpl in *.
        generalize x0.
        rewrite nth_error_app_R by omega.
        replace (length tvs - length tvs) with 0 by omega.
        simpl. inversion 1. subst. clear x1.
        destruct r. rewrite H0. intros.
        rewrite H. unfold Rcast_val, Rcast, Relim. simpl.
        clear.
        rewrite hlist_nth_hlist_app; eauto.
        admit. admit. }
      { apply nat_compare_lt in H.
        admit. }
      { apply nat_compare_gt in H.
        admit. } }
    { simpl. autorewrite with exprD_rw.
      unfold funcAs in *.
      generalize dependent (symD f).
      destruct (typeof_sym f).
      { intros.
        forward. destruct r.
        simpl in *. unfold Rcast in H1. simpl in *. inv_all; subst; auto. }
      { congruence. } }
    { autorewrite with exprD_rw. simpl.
      admit. }
    { autorewrite with exprD_rw. simpl.
      destruct (typ2_match_case ts t').
      { destruct H as [ ? [ ? [ ? ? ] ] ].
        rewrite H in *; clear H.
        admit. }
      { admit. } }
    { autorewrite with exprD_rw. simpl.
      rewrite H2. rewrite H3. auto. }
  Qed.

End substitute.

Section beta.
  Context {sym : Type}.
  Context {RT : RType}
          {T2 : Typ2 _ PreFun.Fun}
          {RS : RSym typD sym}.

  Context {RTOk : RTypeOk RT}
          {T2Ok : Typ2Ok T2}
          {RSOk : RSymOk RS}.

  (** This only beta-reduces the head term, i.e.
   ** (\ x . x) F ~> F
   ** F ((\ x . x) G) ~> F ((\ x . x) G)
   **)
  Fixpoint beta (e : expr typ sym) : expr typ sym :=
    match e with
      | App (Abs t e') e'' =>
        substitute' 0 e'' e'
      | App a x =>
        App (beta a) x
      | e => e
    end.

  Theorem beta_sound
  : forall ts tus tvs e t,
      match exprD' ts tus tvs t e with
        | None => True
        | Some val =>
          match exprD' ts tus tvs t (beta e) with
            | None => False
            | Some val' =>
              forall us vs, val us vs = val' us vs
          end
      end.
  Proof.
    intros ts tus tvs e t.
    match goal with
      | |- ?G =>
        cut (exprD' ts tus tvs t e = exprD' ts tus tvs t e /\ G);
          [ intuition | ]
    end.
    revert tvs e t.
    refine (@ExprFacts.exprD'_ind _ _ _ _ _ _ _
                                      (fun ts tus tvs e t val =>
                                         exprD' ts tus tvs t e = val /\
                                      match val with
                                        | Some val =>
                                          match exprD' ts tus tvs t (beta e) with
                                            | Some val' =>
                                              forall (us : hlist (typD ts) tus) (vs : hlist (typD ts) tvs),
                                                val us vs = val' us vs
                                            | None => False
                                          end
                                        | None => True
                                      end) _ _ _ _ _ _ _ _).
    { auto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      rewrite type_cast_refl; eauto. }
    { simpl; intros; autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl.
      unfold funcAs. generalize (symD i).
      Cases.rewrite_all_goal.
      rewrite type_cast_refl; eauto. simpl. auto. }
    { simpl. destruct f;
      simpl; intros; forward_reason;
      autorewrite with exprD_rw; Cases.rewrite_all_goal; simpl;
      forward; inv_all; subst.
      { split; auto. unfold Open_App.
        intros.
        unfold OpenT, ResType.OpenT.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        rewrite H5. reflexivity. }
      { split; auto.
        clear H5. unfold Open_App.
        repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
        admit. } }
    { intros. forward_reason.
      forward. simpl.
      cutrewrite (exprD' ts tus tvs (typ2 d r) (Abs d e) = Some (Open_Abs fval)); auto.
      autorewrite with exprD_rw.
      rewrite typ2_match_zeta; auto.
      rewrite type_cast_refl; auto. simpl.
      rewrite H. unfold Open_Abs.
      rewrite eq_Arr_eq. rewrite eq_Const_eq.
      rewrite eq_option_eq. reflexivity. }
  Qed.

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
        match nth_error vars v with
          | Some (Some val) => fold_left App args (lift 0 v val)
          | Some None => fold_left App args (Var v)
          | None => fold_left App args (Var (v - length vars))
        end
      | e => fold_left App args e
    end.

End beta.