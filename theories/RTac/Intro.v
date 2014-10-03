Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable substV : (nat -> option expr) -> expr -> expr.
  Variable Var : nat -> expr.
  Variable UVar : nat -> expr.

  Inductive OpenAs :=
  | AsEx : typ -> (expr -> expr) -> OpenAs
  | AsAl : typ -> (expr -> expr) -> OpenAs
  | AsHy : expr -> expr -> OpenAs.

  Variable open : expr -> option OpenAs.

  Definition INTRO
  : rtac typ expr subst :=
    fun ctx sub gl =>
      match open gl with
        | None => Fail
        | Some (AsAl t g') =>
          let nv := countVars ctx in
          More sub (GAll t (GGoal (g' (Var nv))))
        | Some (AsEx t g') =>
          let nu := countUVars ctx in
          More sub (GEx t None (GGoal (g' (UVar nu))))
        | Some (AsHy h g') =>
          More sub (GHyp h (GGoal g'))
      end.

  Definition open_sound : Prop :=
    forall tus tvs e ot,
      open e = Some ot ->
      match ot with
        | AsAl t gl' =>
          forall eD e' e'D,
            propD tus tvs e = Some eD ->
            exprD' tus (tvs ++ t :: nil) e' t = Some e'D ->
            exists eD',
              propD tus (tvs ++ t :: nil) (gl' e') = Some eD' /\
              forall us vs,
                (forall x : typD t,
                   eD' us (hlist_app vs (Hcons (e'D us (hlist_app vs (Hcons x Hnil))) Hnil))) ->
                (eD us vs)
        | AsEx t gl' =>
          forall eD e' e'D,
            propD tus tvs e = Some eD ->
            exprD' (tus ++ t :: nil) tvs e' t = Some e'D ->
            exists eD',
              propD (tus ++ t :: nil) tvs (gl' e') = Some eD' /\
              forall us vs,
                (exists x : typD t,
                   eD' (hlist_app us (Hcons (e'D (hlist_app us (Hcons x Hnil)) vs) Hnil)) vs) ->
                (eD us vs)
        | AsHy h gl' =>
          forall eD,
            propD tus tvs e = Some eD ->
            exists eD' hD,
              propD tus tvs h = Some hD /\
              propD tus tvs gl' = Some eD' /\
              forall us vs,
                (hD us vs -> eD' us vs) ->
                (eD us vs)
      end.

  Hypothesis Hopen : open_sound.

  Theorem INTRO_sound : rtac_sound nil nil INTRO.
  Proof.
    unfold rtac_sound, INTRO.
    intros; subst.
    red in Hopen.
    specialize (@Hopen (getUVars ctx nil) (getVars ctx nil) g).
    destruct (open g); auto.
    specialize (Hopen _ eq_refl).
    destruct o; intros; split; auto.
    { simpl. forward.
      eapply exprD'_typ0_weakenU with (tus' := t :: nil) in H0; eauto.
      forward_reason.
      unfold exprD'_typ0 in H0.
      autorewrite with eq_rw in H0; forwardy.
      assert (exists eD',
                exprD' (getUVars ctx nil ++ t :: nil) (getVars ctx nil)
                       (UVar (countUVars ctx)) t = Some eD' /\
                forall us vs x,
                  eD' (hlist_app us (Hcons x Hnil)) vs = x).
      { admit. }
      forward_reason.
      specialize (@Hopen _ (UVar (countUVars ctx)) _ eq_refl H4).
      inv_all; subst.
      destruct Hopen as [ ? [ ? ? ] ].
      rewrite H3.
      simpl. autorewrite with eq_rw.
      eapply ctxD'_no_hyps; intros.
      split; eauto.
      eapply H6.
      destruct H8. exists x1. destruct H8. revert H9. revert H5. clear.
      generalize dependent (rev_involutive_trans (getUVars ctx nil)).
      generalize dependent (rev_involutive_trans (getVars ctx nil)).
      generalize dependent (getVars ctx nil).
      generalize dependent (getUVars ctx nil).
      intros.
      generalize dependent (hlist_rev us).
      generalize dependent (hlist_rev vs).
      generalize dependent (rev t1).
      generalize dependent (rev t0).
      intros. destruct e0. destruct e.
      rewrite H5. assumption. }
    { simpl. forward.
      eapply exprD'_typ0_weakenV with (tvs' := t :: nil) in H0; eauto.
      (** Same proof as above **)
      admit. }
    { simpl; forward.
      specialize (Hopen _ eq_refl).
      destruct Hopen as [ ? [ ? [ ? [ ? ? ] ] ] ]; clear Hopen.
      rewrite H2.
      rewrite H3.
      simpl.
      eapply ctxD'_no_hyps.
      intros. split; auto. }
  Qed.

End parameterized.
