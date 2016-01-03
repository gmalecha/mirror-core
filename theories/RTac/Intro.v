Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Context {typ : Type}.
  Context {expr : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Context {ExprOk_expr : ExprOk Expr_expr}.

  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprVarOk_expr : ExprVarOk ExprVar_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Variable substV : (nat -> option expr) -> expr -> expr.

  Inductive OpenAs :=
  | AsEx : typ -> (expr -> expr) -> OpenAs
  | AsAl : typ -> (expr -> expr) -> OpenAs
  | AsHy : expr -> expr -> OpenAs.

  Variable open : expr -> option OpenAs.

  Definition INTRO
  : rtac typ expr :=
    fun tus tvs nus nvs ctx sub gl =>
      match open gl with
      | None => Fail
      | Some (AsAl t g') =>
        More_ sub (GAll t (GGoal (g' (Var nvs))))
      | Some (AsEx t g') =>
        More_ sub (GEx_empty nus t (GGoal (g' (UVar nus))))
      | Some (AsHy h g') =>
        More_ sub (GHyp h (GGoal g'))
      end.

  Definition open_spec (tus tvs : tenv typ) (e : expr) (ot : OpenAs) : Prop :=
    match ot with
    | AsAl t gl' =>
      forall eD e' e'D,
        propD tus tvs e = Some eD ->
        exprD' tus (tvs ++ t :: nil) e' t = Some e'D ->
        (forall us vs x, e'D us (hlist_app vs (Hcons x Hnil)) = x) ->
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
        (forall us vs x, e'D (hlist_app us (Hcons x Hnil)) vs = x) ->
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

  Definition open_sound : Prop :=
    forall tus tvs e ot,
      open e = Some ot ->
      open_spec tus tvs e ot.

  Hypothesis Hopen : open_sound.

  Theorem INTRO_sound : rtac_sound INTRO.
  Proof.
    unfold rtac_sound, INTRO.
    intros; subst.
    do 2 red in Hopen.
    specialize (@Hopen (getUVars ctx) (getVars ctx) g).
    destruct (open g).
    { specialize (Hopen _ eq_refl).
      destruct o; intros; split; auto.
      { split.
        { constructor;
          [ eauto using WellFormed_bimap_empty | constructor ]. }
        simpl. forward.
        eapply exprD'_typ0_weakenU with (tus' := t :: nil) in H2; eauto.
        forward_reason.
        assert (exists eD',
                   exprD' (getUVars ctx ++ t :: nil) (getVars ctx)
                          (UVar (countUVars ctx)) t = Some eD' /\
                   forall us vs x,
                     eD' (hlist_app us (Hcons x Hnil)) vs = x).
        { clear - RTypeOk_typ ExprUVarOk_expr.
          rewrite countUVars_getUVars.
          destruct (exprD'_exact_uvar (getUVars ctx) nil (getVars ctx) t) as [ ? [ ? ?  ] ].
          eexists; split; eauto. }
        forward_reason.
        specialize (@Hopen _ (UVar (countUVars ctx)) _ eq_refl H4).
        inv_all; subst.
        destruct Hopen as [ ? [ ? ? ] ]; clear Hopen; eauto.
        rewrite <- countUVars_getUVars.
        rewrite H6.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. intros.
        destruct H8 as [ ? [ ? ? ] ].
        eapply H7; eauto.
        exists x2.
        rewrite H5. assumption. }
      { split.
        { do 2 constructor. }
        simpl. forward.
        eapply exprD'_typ0_weakenU with (tus' := t :: nil) in H2; eauto.
        forward_reason.
        assert (exists eD',
                   exprD' (getUVars ctx) (getVars ctx ++ t :: nil)
                          (Var (countVars ctx)) t = Some eD' /\
                   forall us vs x,
                     eD' us (hlist_app vs (Hcons x Hnil)) = x).
        { clear - RTypeOk_typ ExprVarOk_expr.
          rewrite countVars_getVars.
          destruct (exprD'_exact_var (getUVars ctx) (getVars ctx) nil t) as [ ? [ ? ?  ] ].
          eexists; split; eauto. }
        forward_reason.
        specialize (@Hopen _ (Var (countVars ctx)) _ eq_refl H4).
        inv_all; subst.
        destruct Hopen as [ ? [ ? ? ] ]; clear Hopen; eauto.
        rewrite <- countVars_getVars.
        rewrite H6.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto. }
      { split.
        { do 2 constructor. }
        simpl; forward.
        specialize (Hopen _ eq_refl).
        destruct Hopen as [ ? [ ? [ ? [ ? ? ] ] ] ]; clear Hopen.
        Cases.rewrite_all_goal.
        split; try reflexivity.
        intros.
        eapply Pure_pctxD; eauto. } }
    { exact I. }
  Qed.

End parameterized.

Arguments OpenAs _ _ : clear implicits.