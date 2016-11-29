Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.Rtac.
Require Import McExamples.Hoare.Imp.
Require Import McExamples.Hoare.ILogicFunc.

Set Universe Polymorphism.

Section parametric.
  Context {typ func : Set}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ2_RFun : Typ2 RType_typ RFun}.
  Context {Typ2Ok_RFun : Typ2Ok Typ2_RFun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ0Ok_Prop : Typ0Ok Typ0_Prop}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Context {FV : PartialView func (ilfunc typ)}.
  Variable ilo : @logic_ops  _ _.
  Variable eo : @embed_ops  _ _.
  Context {iloOk : logic_opsOk ilo}.
  Context {FVO : FuncViewOk FV RSym_func (RSym_ilfunc (RelDec_eq_typ) ilo eo _ _) }.

  Context {ilo_Prop : ilo (typ0 (F:=Prop)) =
                      lSome match eq_sym (typ0_cast (F:=Prop)) in _ = X
                                  return ILogic.ILogicOps X with
                            | eq_refl => ILogic.ILogicOps_Prop
                            end}.

  Definition bin_op {T U V W : Type} (f : T -> U -> V -> W)
             (t : ptrn func T) (l : ptrn (expr typ func) U) (r : ptrn (expr typ func) V)
  : ptrn (expr typ func) W :=
    appl (appl (inj t) (pmap (fun t x => (x,t)) l))
         (pmap (fun v tx => let '(t,x) := tx in f t x v) r).

  Instance ptrn_ok_bin_op : ltac:(PtrnOk @bin_op) := _.

Set Printing Universes.

  Definition ptrn_entails@{A X P} {T U V : Type@{A}}
             (t : ptrn@{Set A X P} typ V)
             (a : ptrn@{Set A X P} (expr typ func) (V -> T))
             (b : ptrn@{Set A X P} (expr typ func) (T -> U))
  : ptrn@{Set A X P} (expr typ func) U :=
    appl (appl (inj (ptrn_view _ (fptrn_lentails@{A X P} t))) a) b.

  Instance ptrn_entails_ok : ltac:(PtrnOk @ptrn_entails) := _.

  Definition intro_ptrn_all : ptrn (expr typ func) (OpenAs typ (expr typ func))
  :=
    por
      (appl (inj (ptrn_view FV (fptrn_lforall get (fun t => pmap (fun _ => t) ignore))))
            (pmap (fun body t => SimpleOpen_to_OpenAs (sAsAl t body)) get))
      (ptrn_entails get (pmap (fun G t => (G,t)) get)
                    (appl (inj (ptrn_view FV (fptrn_lforall get (fun t => pmap (fun _ => t) ignore))))
                          (pmap (fun body t Gt =>
                                   let '(G,l) := Gt in
                                   AsAl t (fun arg =>
                                             App (App (Inj (f_insert (ilf_entails l))) G)
                                                 (Red.beta (App body arg)))) get))).

  Definition intro_ptrn_hyp : ptrn (expr typ func) (OpenAs typ (expr typ func))
  :=
    bin_op (fun _ P Q => AsHy P Q)
           (ptrn_view _ (fptrn_limpl ignore)) get get.

  Local Existing Instance RSym_ilfunc.
  Local Existing Instance RSym_func.
  Local Existing Instance RType_typ.

  Theorem Succeeds_bin_op {T U V W : Type} f t l r e res
  : ptrn_ok t -> ptrn_ok l -> ptrn_ok r ->
    Succeeds e (@bin_op T U V W f t l r) res ->
    exists ef el er rf rl rr,
      e = App (App (Inj ef) el) er /\
      res = f rf rl rr /\
      Succeeds ef t rf /\
      Succeeds el l rl /\
      Succeeds er r rr.
  Proof.
    unfold bin_op. intros. ptrn_elim; subst.
    do 6 eexists.
    repeat (split; [ reflexivity | ]); auto.
  Qed.

Axiom todo : forall P : Prop, P.

  Theorem Succeeds_ptrn_entails@{A X P} {T U V : Type@{A}}
          (e : expr typ func) (t : ptrn@{Set A X P} _ _) (a : ptrn@{Set A X P} _ _) (b : ptrn@{Set A X P} _ _) r
  : ptrn_ok@{Set A X P} a -> ptrn_ok@{Set A X P} b -> ptrn_ok@{Set A X P} t ->
    Succeeds@{Set A X P} e (@ptrn_entails@{A X P} T U V t a b) r ->
    exists te ta tb tr ar br,
      e = App (App (Inj (f_insert (ilf_entails te))) ta) tb /\
      r = br (ar tr) /\
      Succeeds@{Set A X P} te t tr /\
      Succeeds@{Set A X P} ta a ar /\
      Succeeds@{Set A X P} tb b br.
  Proof.
    unfold ptrn_entails. intros.
    ptrn_elim; subst.
    do 6 eexists; split; eauto.
  Qed.

  Let Expr_expr := @Expr_expr _ _ RType_typ _ RSym_func.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr :=
    @ExprOk_expr _ _ RType_typ _ RSym_func _ _ _.
  Local Existing Instance ExprOk_expr.

  Local Opaque Red.beta.


  Hint Opaque pmap appl appr inj ptrn_view get ignore : typeclass_instances.


  Theorem intro_ptrn_hyp_sound : open_ptrn_sound intro_ptrn_hyp.
  Proof.
    red; intros.
    unfold intro_ptrn_hyp in H.
    eapply Succeeds_bin_op in H; eauto with typeclass_instances.
    forward_reason. subst.
    ptrn_elim; subst.
    red.
    unfold propD, exprD_typ0.
    red_exprD. intros.
    forwardy; inv_all; subst.
    assert (x = typ0 (F:=Prop) /\ x2 = typ0 (F:=Prop) /\ x6 = typ0 (F:=Prop)).
    { unfold symAs in H; simpl in H.
      destruct (ilo x6); try congruence.
      forwardy. clear H0 H.
      apply typ2_inj in y; eauto; destruct y.
      apply typ2_inj in H0; eauto; destruct H0.
      unfold Rty in *. subst. clear. tauto. }
    destruct H0 as [ ? [ ? ? ] ]; subst.
    rewrite H2. rewrite H1.
    do 2 eexists; split; [ reflexivity | split; [ reflexivity | ] ].
    clear H2 H1.
    unfold symAs in H; simpl in H.
    rewrite ilo_Prop in H.
    rewrite type_cast_refl in H; eauto.
    inv_all; subst.
    simpl.
    unfold AbsAppI.exprT_App, typ2_cast_bin.
    clear ilo_Prop.
    generalize (typ0_cast (F:=Prop)).
    generalize (typ2_cast (typ0 (F:=Prop)) (typ0 (F:=Prop))).
    generalize (typ2_cast (typ0 (F:=Prop))
                    (typ2 (typ0 (F:=Prop)) (typ0 (F:=Prop)))).
    generalize dependent (typD (typ0 (F:=Prop))).
    generalize dependent (typD (typ2 (typ0 (F:=Prop)) (typ0 (F:=Prop)))).
    generalize dependent (typD
            (typ2 (typ0 (F:=Prop)) (typ2 (typ0 (F:=Prop)) (typ0 (F:=Prop))))).
    do 8 intro; subst. simpl.
    clear. tauto.
  Qed.

  Theorem intro_ptrn_all_sound : open_ptrn_sound intro_ptrn_all.
  Proof.
    red. intros.
    unfold intro_ptrn_all in H.
    eapply Succeeds_por in H; eauto 100 with typeclass_instances.
    destruct H.
    - ptrn_elim; subst.
      eapply SimpleOpen_to_OpenAs_sound; eauto.
      simpl. unfold propD, exprD_typ0. simpl. intros.
      forwardy.
      inv_all. subst.
      unfold symAs in H. simpl in H.
      forward. inv_all; subst.
      destruct (decompose_Rty_typ2 _ _ r) as [ ? [ ? ? ] ].
      subst.
      destruct x2.
      red in x0. subst x.
      eexists; split; eauto.
      intros.
      simpl.
      specialize (iloOk (typ0 (F:=Prop))).
      rewrite H in *; clear H.
      inversion ilo_Prop; clear ilo_Prop; subst.
      revert iloOk.
      clear - H2.
      revert H2.
      unfold typ2_cast_quant, castD in *. simpl.
      generalize dependent (typ0_cast (F:=Prop)).
      generalize dependent (typ0 (F:=Prop)).
      intro.
      generalize dependent (typ2_cast x7 t).
      unfold AbsAppI.exprT_App, exprT_Inj.
      generalize dependent (typ2_cast (typ2 x7 t) t).
      generalize dependent (typD (typ2 x7 t)).
      generalize dependent (typD t).
      generalize dependent (typD (typ2 (typ2 x7 t) t)).
      intros; subst; simpl in *. auto.
    - ptrn_elim; subst.
      simpl.
      unfold propD, exprD_typ0. simpl.
      intros.
      forwardy; inv_all; subst.
      assert (x2 = typ2 x19 x18 /\ x = x18 /\ x7 = x4 /\ x = x4).
      { clear - H H3 RTypeOk_typ Typ2Ok_RFun.
        unfold symAs in *.
        simpl in *.
        destruct (ilo x18); try congruence.
        destruct (ilo x4); try congruence.
        forwardy. clear H2 H1 H H0.
        apply typ2_inj in y; eauto.
        eapply typ2_inj in y0; eauto.
        destruct y; destruct y0.
        eapply typ2_inj in H2; eauto.
        unfold Rty in *. destruct H2.
        tauto. }
      destruct H2 as [ ? [ ? [ ? ? ] ] ]; subst. subst.
      eapply exprD_weakenV with (Expr_expr:=Expr_expr)(tvs':=x19::nil) in H6; eauto.
      eapply exprD_weakenV with (Expr_expr:=Expr_expr)(tvs':=x19::nil) in H4; eauto.
      forward_reason.
      erewrite ExprTac.lambda_exprD_AppL; eauto.
      Focus 2.
      erewrite ExprTac.lambda_exprD_AppR; eauto.
      red_exprD.
      rewrite <- (@fv_compat _ _ _ _ _ _ _ FVO).
      rewrite H. reflexivity.
      generalize (Red.beta_sound tus (tvs ++ x19 :: nil) (App x21 e') x4).
      erewrite lambda_exprD_App_both_cases; eauto.
      intros; forwardy.
      rewrite H7. eexists; split; [ reflexivity | ].
      intros.
      unfold symAs in H, H3. simpl in H, H3.
      destruct (ilo x4) eqn:Hilo; try congruence.
      specialize (iloOk x4).
      rewrite Hilo in iloOk.
      rewrite type_cast_refl in *; eauto.
      inv_all; subst.
      simpl in *.
      generalize (H6 us vs); clear H6.
      generalize (H5 us vs); clear H5.
      generalize (H8 us); clear H8.
      revert H9.
      unfold AbsAppI.exprT_App.
      clear H7 H2 H4 H0.
      unfold typ2_cast_quant.
      generalize (typ0_cast (F:=Prop)).
      generalize (typ2_cast x4 (typ2 x4 (typ0 (F:=Prop)))).
      generalize (typ2_cast x4 (typ0 (F:=Prop))).
      generalize (typ2_cast x19 x4).
      generalize (typ2_cast (typ2 x19 x4) x4).
      clear ilo_Prop.
      repeat match goal with
             | |- context [ @eq Type ?X _ ] => generalize dependent X
             end.
      do 12 intro; subst; simpl.
      intros.
      eapply ILogic.lforallR.
      intros.
      rewrite (H2 (HList.Hcons x1 HList.Hnil)); clear H2.
      rewrite (H0 (HList.Hcons x1 HList.Hnil)); clear H0.
      specialize (H (HList.hlist_app vs (HList.Hcons x1 HList.Hnil))).
      specialize (H9 x1).
      rewrite H1 in *.
      rewrite H. assumption.
  Qed.

  Definition INTRO_all : rtac typ (expr typ func) :=
    INTRO_ptrn intro_ptrn_all.

  Instance RtacSound_INTRO_all : RtacSound INTRO_all.
  Proof.
    eapply INTRO_ptrn_sound; eauto.
    - eauto 100 with typeclass_instances.
    - eapply intro_ptrn_all_sound.
  Qed.

  Definition INTRO_hyp : rtac typ (expr typ func) :=
    INTRO_ptrn intro_ptrn_hyp.

  Instance RtacSound_INTRO_hyp : RtacSound INTRO_hyp.
  Proof.
    unfold INTRO_hyp.
    unfold Expr_expr.
    eapply INTRO_ptrn_sound; eauto.
    - eauto with typeclass_instances.
    - eapply intro_ptrn_hyp_sound.
  Qed.

End parametric.