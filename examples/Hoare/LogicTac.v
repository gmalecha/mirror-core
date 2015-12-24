Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.Rtac.
Require Import McExamples.Hoare.Imp.
Require Import McExamples.Hoare.ILogicFunc.

Section parametric.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ2_RFun : Typ2 _ RFun}.
  Context {Typ2Ok_RFun : Typ2Ok Typ2_RFun}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Typ0Ok_Prop : Typ0Ok Typ0_Prop}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.

  Context {FV : FuncView func (ilfunc typ)}.
  Variable ilo : @logic_ops  _ _.
  Variable eo : @embed_ops  _ _.
  Context {FVO : FuncViewOk FV RSym_func (RSym_ilfunc (RelDec_eq_typ) ilo eo _ _) }.

  Definition bin_op {T U V W} (f : T -> U -> V -> W)
             (t : ptrn func T) (l : ptrn (expr typ func) U) (r : ptrn (expr typ func) V)
  : ptrn (expr typ func) W :=
    appl (appl (inj t) (pmap (fun t x => (x,t)) l))
         (pmap (fun v tx => let '(t,x) := tx in f t x v) r).

  Definition ptrn_ok_bin_op {T U V W} f t l r :
    ptrn_ok t -> ptrn_ok l -> ptrn_ok r -> ptrn_ok (@bin_op T U V W f t l r).
  Proof. Admitted.

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
            (pmap (fun body t => AsAl t (fun arg => Red.beta (lift 0 1 (App body arg)))) get))
      (ptrn_entails get (pmap (fun G t => (G,t)) get)
                    (appl (inj (ptrn_view _ (fptrn_lforall get (fun t => pmap (fun _ => t) ignore))))
                          (pmap (fun body t Gt =>
                                   let '(G,l) := Gt in
                                   AsAl t (fun arg =>
                                             App (App (Inj (f_insert (ilf_forall t l))) (lift 0 1 G))
                                                 (Red.beta (lift 0 1 (App body arg))))) get))).

  Definition intro_ptrn_hyp : ptrn (expr typ func) (OpenAs typ (expr typ func)) :=
    bin_op (fun _ P Q => AsHy P Q)
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

  Require Import ExtLib.Tactics.
  Require Import MirrorCore.Util.Forwardy.

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

  Theorem intro_ptrn_all_sound : open_ptrn_sound intro_ptrn_all.
  Proof.
    red. intros.
    unfold intro_ptrn_all in H.
    eapply Succeeds_por in H; solve_ok.
    destruct H.
    - solve_stuff.
      eapply (@s_elim _ _ _ _ _ (@SucceedsE_fptrn_lforall _ _ _ _ _ _ _ _)) in H1.
      simpl in H1.
      forward_reason. subst.
      solve_stuff.
      + clear H x1.
        Opaque Red.beta.
        unfold Ctx.propD, exprD'_typ0. simpl. intros.
        forwardy.
        inv_all. subst.
        unfold symAs in H. simpl in H.
        destruct (ilo x2) eqn:?; try congruence.
        forwardy. inv_all. subst.
        generalize y. intro. clear H.
        eapply typ2_inj in y.
        unfold Rty in y. destruct y; subst.
        generalize (Red.beta_sound tus (tvs ++ x4 :: nil) (lift 0 1 (App x3 e')) (typ0 (F:=Prop))).
        simpl lift.
        (*
      erewrite exprD'_App_both_cases.
      4: eassumption.
         *)
        admit.
        eassumption.
      + solve_ok.
    - admit.
  Admitted.

  Definition INTRO_all : rtac typ (expr typ func) :=
    INTRO_ptrn intro_ptrn_all.

  Let Expr_expr := @Expr_expr _ _ RType_typ _ RSym_func.
  Local Existing Instance Expr_expr.
  Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr _ _ RType_typ _ RSym_func _ _ _.
  Local Existing Instance ExprOk_expr.

  Instance RtacSound_INTRO_all : RtacSound INTRO_all.
  Proof.
    unfold INTRO_all.
    unfold Expr_expr.
    constructor.
    eapply INTRO_ptrn_sound; eauto.
    - admit.
    - eapply intro_ptrn_all_sound.
  Admitted.
End parametric.