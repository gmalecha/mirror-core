Require Import Compare_dec.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section app_full.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Fixpoint apps (e : expr sym) (ls : list (expr sym)) :=
    match ls with
      | nil => e
      | l :: ls => apps (App e l) ls
    end.

  Fixpoint app_full' (e : expr sym) (acc : list (expr sym)) : expr sym * list (expr sym) :=
    match e with
      | App l r =>
        app_full' l (r :: acc)
      | _ =>
        (e, acc)
    end.

  Definition app_full (e : expr sym) := app_full' e nil.

  Lemma apps_app_full'
  : forall e e' ls ls',
      app_full' e ls = (e', ls') ->
      apps e ls = apps e' ls'.
  Proof.
    induction e; simpl; intros; inv_all; subst; auto.
    eapply IHe1 in H. auto.
  Qed.

  Section fold.
    Variable T : Type.
    Variable do_var : var -> T.
    Variable do_uvar : uvar -> T.
    Variable do_inj : sym -> T.
    Variable do_abs : typ -> expr sym -> T -> T.
    Variable do_app : expr sym -> T ->
                      list (expr sym * T) -> T.

    Fixpoint app_fold (e : expr sym) : T :=
      match e with
        | Var v => do_var v
        | UVar u => do_uvar u
        | Inj i => do_inj i
        | Abs t e =>
          @do_abs t e (app_fold e)
        | App l r =>
          (fix gather e (ls : list (expr sym * T)) :=
           match e with
             | App a b =>
               gather a ((b, app_fold b) :: ls)
             | e => do_app e (app_fold e) ls
           end) l ((r,app_fold r) :: nil)
      end.

    Variable R : expr sym -> T -> Prop.
    Hypothesis Hvar : forall v,
                        R (Var v) (do_var v).
    Hypothesis Huvar : forall v,
                         R (UVar v) (do_uvar v).
    Hypothesis Hinj : forall i,
                        R (Inj i) (do_inj i).
    Hypothesis Habs : forall t e e_res,
                        R e e_res ->
                        R (Abs t e) (do_abs t e e_res).
    Hypothesis Happ : forall l l_res rs,
                        R l l_res ->
                        Forall (fun x => R (fst x) (snd x)) rs ->
                        R (apps l (map fst rs))
                          (do_app l l_res rs).

    Theorem app_fold_sound : forall e result,
                               app_fold e = result ->
                               R e result.
    Proof.
      refine (expr_strong_ind _ _).
      destruct e; simpl; intros; try solve [ subst; eauto ].
      { assert (Forall (fun x => R (fst x) (snd x)) ((e2, app_fold e2) :: nil)).
        { repeat constructor; simpl. eapply H; eauto with typeclass_instances. }
        cutrewrite (App e1 e2 = apps e1 (map fst ((e2, app_fold e2) :: nil)));
          [ | reflexivity ].
        generalize dependent ((e2, app_fold e2) :: nil).
        assert (forall y : expr sym,
                  SolveTypeClass
                    (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e1) ->
                  forall result : T, app_fold y = result -> R y result).
        { clear - H. intuition.
          eapply H; eauto.
          eapply TransitiveClosure.RTStep. eapply X.
          constructor. }
        revert H0. revert result. clear H.
        induction e1; simpl; intros; subst; eauto using Happ with typeclass_instances.
        { change (apps (App e1_1 e1_2) (map fst l))
            with (apps e1_1 (map fst ((e1_2,app_fold e1_2) :: l))).
          eapply IHe1_1; eauto.
          { clear - H0.
            intros. eapply H0; eauto.
            red. eapply TransitiveClosure.RTStep. eapply X. constructor. }
          { constructor; eauto. simpl.
            eapply H0; eauto with typeclass_instances. } } }
      { subst. eapply Habs. eapply H; eauto with typeclass_instances. }
    Qed.

  End fold.

End app_full.
