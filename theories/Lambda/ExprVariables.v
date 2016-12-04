Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section parametric.
  Context {typ : Set}.
  Context {func : Set}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.

  (** UVars **)
  Global Instance ExprUVar_expr : ExprUVar (expr typ func) :=
  { UVar := UVar }.

  Lemma UVar_lambda_exprD
  : forall (tus tvs : tenv typ) (v : ExprI.uvar) (t : typ),
      match lambda_exprD tus tvs t (UVar v) with
        | Some vD =>
          exists get : OpenT typD tus (typD t),
                       nth_error_get_hlist_nth typD tus v =
                       Some (existT (fun t0 : typ => OpenT typD tus (typD t0)) t get) /\
                       (forall (us : hlist typD tus) (vs : hlist typD tvs),
                          get us = vD us vs)
        | None =>
          nth_error tus v = None \/
          (exists t' : typ, nth_error tus v = Some t' /\ ~ Rty t t')
      end.
  Proof.
    simpl. intros. autorewrite with exprD_rw. simpl.
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               match X with
                 | match _ with _ => _ end => fail 1
                 | _ => consider X; intros; subst
               end
           end.
    { destruct r. eexists; split; eauto. }
    { eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
      destruct H0; right; eauto.
      eexists; split; eauto.
      eapply type_cast_total in H; eauto.
      intro. apply H. apply Rsym. assumption. }
    { eapply nth_error_get_hlist_nth_None in H. auto. }
  Qed.

  Let Expr_expr : @ExprI.Expr typ _ (expr typ func) := @Expr_expr _ _ _ _ _.
  Local Existing Instance Expr_expr.

  Global Instance ExprUVarOk_expr : ExprUVarOk ExprUVar_expr.
  Proof.
    constructor.
    { eapply UVar_lambda_exprD. }
    { simpl. eapply EqNat.beq_nat_true_iff. }
  Qed.


  (** Vars **)
  Lemma Var_lambda_exprD
  : forall (tus tvs : tenv typ) (v : ExprI.uvar) (t : typ),
      match lambda_exprD tus tvs t (Var v) with
        | Some vD =>
          exists get : OpenT typD tvs (typD t),
                       nth_error_get_hlist_nth typD tvs v =
                       Some (existT (fun t0 : typ => OpenT typD tvs (typD t0)) t get) /\
                       (forall (us : hlist typD tus) (vs : hlist typD tvs),
                          get vs = vD us vs)
        | None =>
          nth_error tvs v = None \/
          (exists t' : typ, nth_error tvs v = Some t' /\ ~ Rty t t')
      end.
  Proof.
    simpl. intros. autorewrite with exprD_rw. simpl.
    repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               match X with
                 | match _ with _ => _ end => fail 1
                 | _ => consider X; intros; subst
               end
           end.
    { destruct r. eexists; split; eauto. }
    { eapply nth_error_get_hlist_nth_Some in H0. simpl in *.
      destruct H0; right; eauto.
      eexists; split; eauto.
      eapply type_cast_total in H; eauto.
      intro. apply H. apply Rsym. assumption. }
    { eapply nth_error_get_hlist_nth_None in H. auto. }
  Qed.

  Global Instance ExprVar_expr : ExprVar (expr typ func) :=
  { Var := Var }.

  Global Instance ExprVarOk_expr : ExprVarOk ExprVar_expr.
  Proof.
    constructor.
    { eapply Var_lambda_exprD. }
    { simpl. eapply EqNat.beq_nat_true_iff. }
  Qed.

End parametric.
