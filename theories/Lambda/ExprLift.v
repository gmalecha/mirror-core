Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section types.
  Context {func : Type}.
  Context {RType_typD : RType}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym typD func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : @RTypeOk _}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Fixpoint lower (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : option (expr typ func) :=
    match e with
      | Var v => if v ?[ lt ] skip then Some (Var v)
                          else if (v - skip) ?[ lt ] _by then None
                               else Some (Var (v - _by))
      | Inj f => Some (Inj f)
      | UVar u => Some (UVar u)
      | App a b =>
        ap (ap (pure App) (lower skip _by a)) (lower skip _by b)
      | Abs t a =>
        ap (pure (Abs t)) (lower (S skip) _by a)
    end.

(*
  Theorem exprD'_lower
  : forall ts tus tvs tvs' tvs'' e t val,
      exprD' ts tus (tvs ++ tvs' ++ tvs'') t e = Some val ->
      exists val',
        exprD' ts tus (tvs ++ tvs'') t e = Some val' /\
        forall us vs vs' vs'',
          val us (hlist_app vs (hlist_app vs' vs'')) =
          val' us (hlist_app vs vs'').
*)

  Fixpoint lift (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : expr typ func :=
    match e with
      | Var v => Var (if v ?[ lt ] skip then v else (v + _by))
      | Inj f => Inj f
      | UVar u => UVar u
      | App a b =>
        App (lift skip _by a) (lift skip _by b)
      | Abs t a =>
        Abs t (lift (S skip) _by a)
    end.

  Theorem typeof_expr_lift
  : forall ts tus e tvs tvs' tvs'',
      typeof_expr ts tus (tvs ++ tvs' ++ tvs'') (lift (length tvs) (length tvs') e) =
      typeof_expr ts tus (tvs ++ tvs'') e.
  Proof.
    intros ts tus e tvs; revert tvs; induction e; simpl; intros;
    Cases.rewrite_all_goal; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { repeat rewrite ListNth.nth_error_app_L by auto.
        reflexivity. }
      { repeat rewrite ListNth.nth_error_app_R by omega.
        f_equal. omega. } }
    { specialize (IHe (t :: tvs)). simpl in *.
      rewrite IHe. reflexivity. }
  Qed.

  Theorem exprD'_lift
  : forall ts tus e tvs tvs' tvs'' t,
      match exprD' ts tus (tvs ++ tvs'') t e with
        | None => True
        | Some val =>
          match exprD' ts tus (tvs ++ tvs' ++ tvs'') t (lift (length tvs) (length tvs') e) with
            | None => False
            | Some val' => True
          end
      end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw; simpl;
    forward; inv_all; subst; Cases.rewrite_all_goal; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize H.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs' ++ tvs'') (F := typD ts) in H; eauto with typeclass_instances.
        intro.
        eapply nth_error_get_hlist_nth_appL with (tvs' := tvs'') (F := typD ts) in H3; eauto with typeclass_instances.
        forward_reason.
        revert H2. Cases.rewrite_all_goal. destruct x1.
        simpl in *.
        destruct r. rewrite H6 in *. rewrite H0 in *.
        inv_all; subst. simpl in *.
        rewrite type_cast_refl; eauto. congruence. }
      { admit. } }
    { revert H3. rewrite typeof_expr_lift. rewrite H.
      specialize (IHe1 tvs tvs' tvs'' (typ2 t0 t)).
      specialize (IHe2 tvs tvs' tvs'' t0).
      forward. }
    { destruct (typ2_match_case ts t0).
      { destruct H1 as [ ? [ ? [ ? ? ] ] ].
        rewrite H1 in *; clear H1.
        generalize dependent (typ2_cast ts x x0).
        destruct x1. simpl.

        intros. rewrite eq_option_eq in *.
        forward. inv_all; subst.
        specialize (IHe (t :: tvs) tvs' tvs'' x0).
        revert IHe. simpl. Cases.rewrite_all_goal.
        auto. }
      { rewrite H1 in *. congruence. } }
  Qed.

End types.