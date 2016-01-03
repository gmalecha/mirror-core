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

Section parametric.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ2_RFun : Typ2 RType_typ RFun}.
  Context {Typ2Ok_RFun : Typ2Ok Typ2_RFun}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ0Ok_Prop : Typ0Ok Typ0_Prop}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Context {FV : FuncView func (ilfunc typ)}.
  Variable ilo : @logic_ops  _ _.
  Variable eo : @embed_ops  _ _.
  Context {iloOk : logic_opsOk ilo}.
  Context {FVO : FuncViewOk FV RSym_func (RSym_ilfunc (RelDec_eq_typ) ilo eo _ _) }.

  Context {ilo_Prop : ilo (typ0 (F:=Prop)) =
                      lSome match eq_sym (typ0_cast (F:=Prop)) in _ = X
                                  return ILogic.ILogicOps X with
                            | eq_refl => ILogic.ILogicOps_Prop
                            end}.

  Definition bin_op {T U V W} (f : T -> U -> V -> W)
             (t : ptrn func T) (l : ptrn (expr typ func) U) (r : ptrn (expr typ func) V)
  : ptrn (expr typ func) W :=
    appl (appl (inj t) (pmap (fun t x => (x,t)) l))
         (pmap (fun v tx => let '(t,x) := tx in f t x v) r).

  Definition ptrn_ok_bin_op {T U V W} f t l r :
    ptrn_ok t -> ptrn_ok l -> ptrn_ok r -> ptrn_ok (@bin_op T U V W f t l r).
  Proof.
    intros. unfold bin_op.
    repeat first [ eassumption
                 | eapply ptrn_ok_appl
                 | eapply ptrn_ok_inj
                 | eapply ptrn_ok_pmap ].
  Qed.

  Definition ptrn_entails {T U V}
             (t : ptrn typ V)
             (a : ptrn (expr typ func) (V -> T))
             (b : ptrn (expr typ func) (T -> U))
  : ptrn (expr typ func) U :=
    appl (appl (inj (ptrn_view _ (fptrn_lentails t))) a) b.

  Instance ptrn_entails_ok {T U V}
  : forall t a b, ptrn_ok t -> ptrn_ok a -> ptrn_ok b ->
                  ptrn_ok (@ptrn_entails T U V t a b).
  Proof.
    intros.
    unfold ptrn_entails.
    repeat first [ simple eapply ptrn_ok_appl
                 | simple eapply ptrn_ok_inj
                 | simple eapply ptrn_view_ok
                 | simple apply fptrn_lentails_ok ]; eauto.
  Qed.

  Definition intro_ptrn_all : ptrn (expr typ func) (OpenAs typ (expr typ func)) :=
    por
      (appl (inj (ptrn_view _ (fptrn_lforall get (fun t => pmap (fun _ => t) ignore))))
            (pmap (fun body t => SimpleOpen_to_OpenAs (sAsAl t body)) get))
      (ptrn_entails get (pmap (fun G t => (G,t)) get)
                    (appl (inj (ptrn_view _ (fptrn_lforall get (fun t => pmap (fun _ => t) ignore))))
                          (pmap (fun body t Gt =>
                                   let '(G,l) := Gt in
                                   AsAl t (fun arg =>
                                             App (App (Inj (f_insert (ilf_entails l))) G)
                                                 (Red.beta (App body arg)))) get))).

  Definition intro_ptrn_hyp : ptrn (expr typ func) (SimpleOpen typ func) :=
    bin_op (fun _ P Q => sAsHy P Q)
           (ptrn_view _ (fptrn_limpl ignore)) get get.

  Ltac solve_ok :=
    repeat first [ simple eapply ptrn_ok_appl
                 | simple eapply ptrn_ok_inj
                 | simple eapply ptrn_ok_pmap
                 | simple eapply ptrn_ok_ignore
                 | simple eapply ptrn_ok_get
                 | simple eapply ptrn_view_ok
                 | simple eapply fptrn_lforall_ok; intros
                 | simple eapply ptrn_entails_ok ].

  Local Existing Instance RSym_ilfunc.
  Local Existing Instance RSym_func.
  Local Existing Instance RType_typ.

  Lemma exprD'_App_both_cases : forall tus tvs tx ty f x fD xD,
      exprD' tus tvs (typ2 tx ty) f = Some fD ->
      exprD' tus tvs tx x = Some xD ->
      exprD' tus tvs ty (App f x) = Some (AbsAppI.exprT_App fD xD).
  Proof.
    intros. autorewrite with exprD_rw.
    erewrite ExprTac.exprD_typeof_Some by eassumption.
    rewrite H. rewrite H0.
    reflexivity.
  Qed.

  Ltac solve_stuff :=
    try lazymatch goal with
        | |- ptrn_ok _ => solve_ok
        | |- _ =>
          match goal with
          | H : Succeeds _ _ _ |- _ =>
            first [ simple eapply Succeeds_appl in H; [ forward_reason; subst; solve_stuff | clear H; solve_ok | clear H; solve_ok ]
                  | simple eapply Succeeds_pmap in H; [ forward_reason; subst; solve_stuff | clear H; solve_ok ]
                  | simple eapply Succeeds_get in H; subst; solve_stuff
                  | simple eapply Succeeds_inj in H; [ forward_reason; subst; solve_stuff | clear H; solve_ok ]
                  | (eapply Succeeds_ptrn_view in H;
                     [ | solve [ eauto with typeclass_instances ] | clear H ]); [ forward_reason; subst; solve_stuff | ] ]
          end
        end.

  Theorem Succeeds_ptrn_entails {T U V} e t a b r
  : ptrn_ok a -> ptrn_ok b -> ptrn_ok t ->
    Succeeds e (@ptrn_entails T U V t a b) r ->
    exists te ta tb tr ar br,
      e = App (App (Inj (f_insert (ilf_entails te))) ta) tb /\
      r = br (ar tr) /\
      Succeeds te t tr /\
      Succeeds ta a ar /\
      Succeeds tb b br.
  Proof.
    unfold ptrn_entails. intros.
    solve_stuff; try solve_ok; eauto using fptrn_lentails_ok.
    eapply (@s_elim _ _ _ _ _ (@SucceedsE_fptrn_lentails _ _ _ _ _)) in H5.
    simpl in H5. forward_reason.
    subst.
    do 6 eexists. split; [ reflexivity | ].
    split; [ reflexivity | ].
    eauto.
  Qed.

  Let Expr_expr := @Expr_expr _ _ RType_typ _ RSym_func.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr _ _ RType_typ _ RSym_func _ _ _.
  Local Existing Instance ExprOk_expr.

  Local Opaque Red.beta.

  Theorem intro_ptrn_all_sound : open_ptrn_sound intro_ptrn_all.
  Proof.
    red. intros.
    unfold intro_ptrn_all in H.
    eapply Succeeds_por in H; solve_ok.
    destruct H.
    - solve_stuff.
      eapply (@s_elim _ _ _ _ _ (@SucceedsE_fptrn_lforall _ _ _ _ _ _ _ _)) in H1.
      2: solve_ok.
      simpl in H1.
      forward_reason. subst.
      eapply SimpleOpen_to_OpenAs_sound; eauto.
      solve_stuff.
      + clear H x1.
        red.
        unfold Ctx.propD, exprD'_typ0. simpl. intros.
        forwardy.
        inv_all. subst.
        unfold symAs in H. simpl in H.
        destruct (ilo x2) eqn:?; try congruence.
        forwardy. inv_all. subst.
        generalize y. intro. clear H.
        eapply typ2_inj in y; [ | eassumption ].
        unfold Rty in y. destruct y; subst.
        eexists; split; [ eassumption | ].
        assert (i = match
                  eq_sym (typ0_cast (F:=Prop)) in (_ = X)
                  return (ILogic.ILogicOps X)
                with
                | eq_refl => ILogic.ILogicOps_Prop
                end).
        { clear - ilo_Prop Heql.
          revert Heql. change_rewrite ilo_Prop.
          inversion 1. reflexivity. }
        subst. clear - RTypeOk_typ.
        unfold castD. simpl.
        unfold typ2_cast_quant, AbsAppI.exprT_App.
        generalize dependent (typ0_cast (F:=Prop)).
        generalize dependent (typ2_cast x4 (typ0 (F:=Prop))).
        generalize dependent (typ2_cast (typ2 x4 (typ0 (F:=Prop))) (typ0 (F:=Prop))).
        rewrite (UIP_refl y0); clear y0; simpl.
        revert x1.
        generalize ((typD (typ2 x4 (typ0 (F:=Prop))))).
        generalize (typD (typ2 (typ2 x4 (typ0 (F:=Prop))) (typ0 (F:=Prop)))).
        generalize (typD (typ0 (F:=Prop))).
        intros; subst; simpl in *.
        assumption.
    - eapply Succeeds_ptrn_entails in H;
        try solve_ok; eauto using fptrn_lentails_ok, fptrn_lforall_ok.
      forward_reason; subst.
      solve_stuff;
        try solve_ok; eauto using fptrn_lentails_ok, fptrn_lforall_ok.
      eapply (@s_elim _ _ _ _ _ (SucceedsE_fptrn_lforall _ _ _ _ _)) in H3;
        try solve_ok; eauto using fptrn_lentails_ok, fptrn_lforall_ok.
      simpl in H3. forward_reason. subst.
      solve_stuff. clear ilo_Prop.
      clear H. destruct x4. simpl.
      unfold Ctx.propD, exprD'_typ0. simpl.
      intros.
      forwardy; inv_all; subst.
      assert (x2 = x0 /\ x = x11 /\ x7 = typ2 x3 x11 /\ x0 = x11).
      { clear - H H3 RTypeOk_typ Typ2Ok_RFun.
        unfold symAs in *.
        simpl in *.
        destruct (ilo x2); try congruence.
        destruct (ilo x0); try congruence.
        forwardy. clear H2 H1 H H0.
        apply typ2_inj in y; eauto.
        eapply typ2_inj in y0; eauto.
        destruct y; destruct y0.
        eapply typ2_inj in H2; eauto.
        unfold Rty in *. destruct H2.
        subst. subst.
        tauto. }
      destruct H2 as [ ? [ ? [ ? ? ] ] ]; subst.
      eapply exprD'_weakenV with (Expr_expr:=Expr_expr)(tvs':=x3::nil) in H6; eauto.
      eapply exprD'_weakenV with (Expr_expr:=Expr_expr)(tvs':=x3::nil) in H4; eauto.
      forward_reason.
      erewrite ExprTac.exprD'_AppL; eauto.
      Focus 2.
      erewrite ExprTac.exprD'_AppR; eauto.
      2: eapply H4.
      red_exprD.
      rewrite <- (@fv_compat _ _ _ _ _ _ _ FVO).
      rewrite H. reflexivity.
      generalize (Red.beta_sound tus (tvs ++ x3 :: nil) (App x1 e') x11).
      erewrite exprD'_App_both_cases; eauto.
      2: eapply H2.
      intros; forwardy.
      rewrite H7. eexists; split; [ reflexivity | ].
      intros.
      unfold symAs in H, H3. simpl in H, H3.
      destruct (ilo x11) eqn:Hilo; try congruence.
      specialize (iloOk x11).
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
      generalize (typ2_cast (typ2 x3 x11) x11).
      generalize (typ2_cast x3 x11).
      generalize (typ2_cast x11 (typ0 (F:=Prop))).
      generalize (typ2_cast x11 (typ2 x11 (typ0 (F:=Prop)))).
      generalize dependent (typD (typ2 x11 (typ2 x11 (typ0 (F:=Prop))))).
      generalize dependent (typD (typ2 x11 (typ0 (F:=Prop)))).
      generalize dependent (typD (typ2 (typ2 x3 x11) x11)).
      generalize dependent (typD (typ2 x3 x11)).
      generalize dependent (typD (typ0 (F:=Prop))).
      do 12 intro; subst; simpl.
      intros.
      eapply ILogic.lforallR.
      intros.
      rewrite (H2 (HList.Hcons x2 HList.Hnil)); clear H2.
      rewrite (H0 (HList.Hcons x2 HList.Hnil)); clear H0.
      specialize (H (HList.hlist_app vs (HList.Hcons x2 HList.Hnil))).
      specialize (H9 x2).
      rewrite H1 in *.
      rewrite H. assumption.
  Qed.

  Definition INTRO_all : rtac typ (expr typ func) :=
    INTRO_ptrn intro_ptrn_all.

  Instance RtacSound_INTRO_all : RtacSound INTRO_all.
  Proof.
    unfold INTRO_all.
    unfold Expr_expr.
    constructor.
    eapply INTRO_ptrn_sound; eauto.
    - unfold intro_ptrn_all.
      eapply ptrn_ok_por; solve_ok.
    - eapply intro_ptrn_all_sound.
  Qed.
End parametric.