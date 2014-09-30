Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.ExprDAs.
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
  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprUVar_expr : ExprUVar expr}.

  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprVarOk_expr : ExprVarOk _}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Variable substV : (nat -> option expr) -> expr -> expr.

  Inductive OpenAs :=
  | AsEx : typ -> (expr -> expr) -> OpenAs
  | AsAl : typ -> (expr -> expr) -> OpenAs
  | AsHy : expr -> expr -> OpenAs.

  Variable open : expr -> option OpenAs.

  Fixpoint vars_to (n : nat) (acc : list expr) : list expr :=
    match n with
      | 0 => acc
      | S n => vars_to n (Var n :: acc)
    end.

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
          let nv := countVars ctx in
          More sub (GEx t None (GGoal (g' (UVar nu (vars_to nv nil)))))
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
            exprD' (tus ++ mkctyp tvs t :: nil) tvs e' t = Some e'D ->
            exists eD',
              propD (tus ++ mkctyp tvs t :: nil) tvs (gl' e') = Some eD' /\
              forall us vs,
                (exists x : ctxD {| cctx := tvs ; vtyp := t |},
                   eD' (hlist_app us (Hcons x Hnil)) vs) ->
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
    specialize (@Hopen (fst (getEnvs ctx)) (snd (getEnvs ctx)) g).
    destruct (open g); auto.
    specialize (Hopen _ eq_refl).
    destruct o; intros; split; auto.
    { simpl. forward; simpl in *.
      specialize (fun e' e'D => @Hopen _ e' e'D H1).
      assert (exists eD',
                exprD' (t0 ++ {| cctx := t1; vtyp := t |} :: nil) t1
                       (UVar (countUVars ctx) (vars_to (countVars ctx) nil)) t = Some eD' /\
                forall us vs x,
                  eD' (hlist_app us (Hcons x Hnil)) vs = x vs).
      { admit. }
      inv_all. forward_reason.
      generalize (@VariablesI.UVar_exprD' _ _ _ _ _ _
                                          (t0 ++ {| cctx := t1; vtyp := t |} :: nil) t1
                 (countUVars ctx) (vars_to (countVars ctx) nil) t).
      rewrite H3.
      specialize (@Hopen _ _ H3).
      intros.
      destruct Hopen as [ ? [ ? ? ] ]; clear Hopen.
      destruct H5 as [ ? [ ? ? ] ].
      rewrite H6.
      unfold eq_rect_r, eq_rect, eq_sym.
      autorewrite with eq_rw.
      eapply ctxD'_no_hyps; intros.
      specialize (H7 (hlist_unrev us) (hlist_unrev vs)).
      split; auto.
      eapply H7.
      destruct H10. exists x2. tauto. }
    { simpl. forward.
      (** Same proof as above **)
      admit. }
    { simpl in *; forward; simpl in *.
      eapply Hopen in H1; clear Hopen.
      forward_reason.
      Cases.rewrite_all_goal.
      eapply ctxD'_no_hyps.
      intuition. }
  Qed.

End parameterized.
