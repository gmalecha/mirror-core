Require Import Coq.Strings.String.
Require Import ExtLib.Tactics.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Rtac.
Require Import MirrorCore.Reify.Reify.
Require Import McExamples.Hoare.Imp.
Require Import McExamples.Hoare.ImpSyntax.
Require Import McExamples.Hoare.ImpMetaTheory.
Require Import McExamples.Hoare.LogicTac.
Require McExamples.Hoare.Tests.

Ltac one_of lems :=
  match lems with
  | (?X,?Y) => first [ one_of X | one_of Y ]
  | _ => exact lems
  end.

Ltac red_lemma :=
  unfold Lemma.lemmaD, Lemma.lemmaD'; simpl.

(** TODO(gmalecha): Move this **)
Ltac prove_RL lem :=
  solve [ constructor; red; simpl; eapply lem ].


Module ImpVerify (I : ImpLang).
  Module Import Syntax := ImpSyntax I.
  Module Import MetaTheory := ImpTheory I.
  Module Import Tests := Tests.TestCases I.
  Definition imp_tac := rtac typ (expr typ func).
  Definition imp_tacK := rtacK typ (expr typ func).

  Local Open Scope rtac_scope.

  Definition embed_ltrue_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
  := <:: embed_ltrue ::>.
  Definition entails_exL_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
  := <:: entails_exL ::>.
  Definition go_lower_raw_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
  := <:: go_lower_raw ::>.
  Definition pull_embed_hyp_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
  := <:: pull_embed_hyp ::>.
  Definition pull_embed_last_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
  := <:: pull_embed_last_hyp ::>.

  Local Existing Instance RType_typ.
  Local Existing Instance RTypeOk_typ.
  Local Existing Instance Typ2_Fun.
  Local Existing Instance Typ2Ok_Fun.
  Local Existing Instance CoreTypes.Typ0_Prop.
  Local Existing Instance CoreTypes.Typ0Ok_Prop.

  Section with_fs.
    Variable fs' : SymEnv.functions typ _.

    Let RS := RS fs'.
    Local Existing Instance RS.
    Let RSOk := RSOk fs'.
    Local Existing Instance RSOk.

    Let Expr_expr := Expr_expr fs'.
    Local Existing Instance Expr_expr.
    Let ExprOk_expr := ExprOk_expr fs'.
    Local Existing Instance ExprOk_expr.

    Global Instance FuncView_imp_func : PartialView func imp_func :=
      ViewSum.PartialView_left (ViewSum.PartialView_right View.PartialView_id).

    Global Instance FuncViewOk_imp_func :
      @FuncView.FuncViewOk func imp_func _ _ _ _ _.
    Proof.
      eapply ViewSum.PartialViewOk_left.
      eapply ViewSum.PartialViewOk_right.
      eapply FuncView.FuncViewOk_id.
    Qed.

    Global Instance FuncView_ilfunc : PartialView func (ILogicFunc.ilfunc typ) :=
      ViewSum.PartialView_right View.PartialView_id.

    Global Instance FuncViewOk_ilfunc
    : FuncView.FuncViewOk FuncView_ilfunc _
                          (@ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _).
    Proof.
      eapply ViewSum.PartialViewOk_right.
      eapply FuncView.FuncViewOk_id.
    Qed.

    (** * Tactics **)
    Definition ON_ENTAILMENT (yes no : imp_tac) : imp_tac :=
      let check :=
          Ptrns.run_ptrn
            (Ptrns.appr
               (Ptrns.appr
                  (Ptrns.inj
                     (ptrn_view FuncView_ilfunc
                                (ILogicFunc.fptrn_lentails
                                   (Ptrns.pmap (fun _ _ _ : unit => true) Ptrns.ignore))))
                  Ptrns.ignore) Ptrns.ignore)
            false in
      AT_GOAL (fun _ _ gl => if check gl then yes else no).
    Arguments ON_ENTAILMENT _%rtac _%rtac _ _ _.

    Definition INTRO_All : imp_tac := INTRO_all.
    Definition INTRO_Hyp : imp_tac := INTRO_hyp.
    Definition BETA_REDUCE : imp_tac :=
      SIMPL true (RedAll.red_beta RedAll.red_id).
    Definition SIMPLIFY    : imp_tac := BETA_REDUCE.

    Definition ON_ALL : rtac typ (expr typ func) -> rtacK typ (expr typ func) :=
      @ON_ALL _ _ _ _.
    Definition ON_ALL' : imp_tac -> rtacK typ (expr typ func) := ON_ALL.
    Coercion ON_ALL : rtac >-> rtacK.
    Coercion ON_ALL' : imp_tac >-> rtacK.

    Definition entailment_tac : imp_tac :=
      ON_ENTAILMENT
        (TRY (EAPPLY embed_ltrue_lemma) ;;
         TRY (EAPPLY entails_exL_lemma ;;
              INTRO_All ;;
              BETA_REDUCE) ;;
         TRY (EAPPLY go_lower_raw_lemma ;;
              BETA_REDUCE ;; INTRO_All ;; BETA_REDUCE) ;;
         SIMPLIFY ;; SIMPLIFY ;;
         REPEAT 200 (APPLY pull_embed_hyp_lemma ;; INTRO_Hyp) ;;
         ON_ALL (TRY (EAPPLY pull_embed_last_lemma ;; INTRO_Hyp)))
        IDTAC.

    Definition simplify_tac : imp_tac := SIMPLIFY.

    Definition entailment_tac_solve : imp_tac :=
      SOLVE entailment_tac.

    Definition EAPPLY_THEN a (b : imp_tac) : imp_tac :=
      EAPPLY a ;; ON_ALL b.


    Definition EAPPLY_THEN_1 a (side : imp_tac) (b : imp_tacK) : imp_tac :=
      (EAPPLY a ;; ON_ALL (TRY (SOLVE side))) ;;
      THENK MINIFY
            (ON_ALL (AT_GOAL (fun _ _ goal =>
                                match goal with
                                | App (App entails _) (App (App (App triple _) _) _) =>
                                  runTacK b
                                | _ => IDTAC
                                end))).

    Definition Assert_tail_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Assert_tail_rule ::>.
    Definition Assign_tail_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Assign_tail_rule ::>.
    Definition Skip_tail_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Skip_tail_rule ::>.
    Definition Assert_seq_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Assert_seq_rule ::>.
    Definition Skip_seq_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Skip_seq_rule ::>.
    Definition Assign_seq_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: Assign_seq_rule ::>.
    Definition triple_exL_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: I.triple_exL ::>.
    Definition SeqA_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: I.SeqA_rule ::>.

    Definition sym_eval_no_mem (n : nat) (rest : imp_tac) : imp_tac :=
      REC n (fun rec : imp_tac =>
               let rec : imp_tac := simplify_tac ;; rec in
               TRY (FIRST [ EAPPLY_THEN SeqA_lemma rec
                          | EAPPLY_THEN triple_exL_lemma
                                        (THEN INTRO_All (runOnGoals rec))
                          | EAPPLY_THEN Assign_seq_lemma rec
                          | EAPPLY_THEN Skip_seq_lemma rec
                          | EAPPLY_THEN_1 Assert_seq_lemma entailment_tac (runOnGoals rec)
                          | EAPPLY_THEN Assign_tail_lemma rest
                          | EAPPLY_THEN Skip_tail_lemma rest
                          | EAPPLY_THEN Assert_tail_lemma rest ]))
          IDTAC.

    (** TODO(gmalecha): This looks like it belongs elsewhere **)
    Lemma runTacK_sound : forall t, rtacK_sound t -> rtac_sound (runTacK t).
    Proof.
      unfold rtacK_sound, rtac_sound, runTacK, rtac_spec, rtacK_spec. intros.
      eapply H; eauto.
    Qed.

    Lemma simplify_tac_sound : rtac_sound simplify_tac.
    Proof.
      unfold simplify_tac.
      eapply SIMPLIFY_sound.
      eapply full_reducer_to_reducer_sound.
      eapply RedAll.red_beta_sound.
      eapply RedAll.red_id_sound.
    Qed.

    Theorem ON_ENTAILMENT_sound (a b : imp_tac)
      : rtac_sound a -> rtac_sound b -> rtac_sound (ON_ENTAILMENT a b).
    Proof.
      intros. eapply AT_GOAL_sound.
      intros.
      destruct (Ptrns.run_ptrn
                  (Ptrns.appr
                     (Ptrns.appr
                        (Ptrns.inj
                           (ptrn_view FuncView_ilfunc
                                      (ILogicFunc.fptrn_lentails
                                         (Ptrns.pmap (fun _ _ _ : unit => true) Ptrns.ignore))))
                        Ptrns.ignore) Ptrns.ignore) false e); assumption.
    Qed.

    Global Instance RtacSound_SIMPLIFY : RtacSound SIMPLIFY.
    Proof.
      eapply mkRtacSound.
      eapply SIMPLIFY_sound.
      eapply full_reducer_to_reducer_sound.
      eapply RedAll.red_beta_sound.
      eapply RedAll.red_id_sound.
    Qed.

    Global Instance RtacSound_INTRO_Hyp : RtacSound INTRO_Hyp.
    Proof.
      eapply (RtacSound_INTRO_hyp lops eops).
      Unshelve.
      eauto with typeclass_instances.
    Qed.

    Instance RL_embeD_ltrue : ReifiedLemma embed_ltrue_lemma.
    Proof. prove_RL embed_ltrue. Qed.
    Instance RL_entails_exL : ReifiedLemma entails_exL_lemma.
    Proof. prove_RL entails_exL. Qed.


    Lemma EAPPLY_THEN_sound : forall lem tac,
        ReifiedLemma lem -> rtac_sound tac ->
        rtac_sound (EAPPLY_THEN lem tac).
    Proof. intros; unfold EAPPLY_THEN.
           rtac_derive_soundness_default.
    Qed.


    Lemma EAPPLY_THEN_1_sound
      : forall lem tac1 tac2,
        ReifiedLemma lem ->
        rtac_sound tac1 -> rtacK_sound tac2 ->
        rtac_sound (EAPPLY_THEN_1 lem tac1 tac2).
    Proof. intros; unfold EAPPLY_THEN_1.
           rtac_derive_soundness_default; eauto with typeclass_instances.
           eapply runTacK_sound. eauto.
    Qed.

    Hint Immediate I.SeqA_rule
         Assign_seq_rule Assign_tail_rule
         I.triple_exL Skip_seq_rule
         Assert_seq_rule
         Assert_tail_rule Skip_tail_rule
      : the_hints.

    Instance INTRO_All_sound : RtacSound INTRO_All.
    Proof.
      unfold INTRO_All, INTRO_all.
      eapply INTRO_ptrn_sound.
      { unfold intro_ptrn_all.
        eauto 100 with typeclass_instances. }
      { eapply intro_ptrn_all_sound with (ilo := lops) (eo := eops).
        - eapply lops_ok.
        - eapply ViewSum.PartialViewOk_right.
          eapply FuncView.FuncViewOk_id.
        - reflexivity. }
    Qed.

    Instance RL_Assign_tail : ReifiedLemma Assign_tail_lemma.
    Proof. prove_RL Assign_tail_rule. Qed.
    Instance RL_Assign_seq : ReifiedLemma Assign_seq_lemma.
    Proof. prove_RL Assign_seq_rule. Qed.
    Instance RL_lower_raw : ReifiedLemma go_lower_raw_lemma.
    Proof. prove_RL go_lower_raw. Qed.
    Instance RL_pull_embed_hyp : ReifiedLemma pull_embed_hyp_lemma.
    Proof. prove_RL pull_embed_hyp. Qed.
    Instance RL_pull_embed_last : ReifiedLemma pull_embed_last_lemma.
    Proof. prove_RL pull_embed_last_hyp. Qed.

    Lemma entailment_tac_sound : rtac_sound entailment_tac.
    Proof.
      eapply ON_ENTAILMENT_sound; rtac_derive_soundness_default.
    Qed.

    Lemma entailment_tac_solve_sound : rtac_sound entailment_tac_solve.
    Proof. apply SOLVE_sound. apply entailment_tac_sound. Qed.

    Ltac rtac_derive_soundness_with :=
      rtac_derive_soundness'
        ltac:(fun rtac rtacK lem =>
                first [ eapply simplify_tac_sound
                      | eapply entailment_tac_sound
                      | eapply entailment_tac_solve_sound
                      | eapply EAPPLY_THEN_sound ; [ lem | rtac ]
                      | eapply EAPPLY_THEN_1_sound ; [ lem | rtac | rtacK ]
                      | eapply INTRO_All_sound
                      | match goal with
                        | |- rtac_sound match ?X with _ => _ end =>
                          destruct X; rtac
                        end ])
        ltac:(fun _ _ => fail)
        ltac:(solve [ eauto with typeclass_instances ]).

    Instance RL_SeqA : ReifiedLemma SeqA_lemma.
    Proof. prove_RL I.SeqA_rule. Qed.
    Instance RL_triple_exL : ReifiedLemma triple_exL_lemma.
    Proof. prove_RL I.triple_exL. Qed.
    Instance RL_Skip_seq : ReifiedLemma Skip_seq_lemma.
    Proof. prove_RL Skip_seq_rule. Qed.
    Instance RL_Assert_seq : ReifiedLemma Assert_seq_lemma.
    Proof. prove_RL Assert_seq_rule. Qed.
    Instance RL_Skip_tail : ReifiedLemma Skip_tail_lemma.
    Proof. prove_RL Skip_tail_rule. Qed.
    Instance RL_Assert_tail : ReifiedLemma Assert_tail_lemma.
    Proof. prove_RL Assert_tail_rule. Qed.

    Hint Opaque simplify_tac INTRO_All EAPPLY_THEN EAPPLY_THEN_1 : typeclass_instances.

    Instance sym_eval_no_mem_sound
      : forall n t, RtacSound t -> RtacSound (sym_eval_no_mem n t).
    Proof.
      intros. unfold sym_eval_no_mem.
      rtac_derive_soundness_with.
    Qed.

    (** NOTE: This starts the arithmetic reasoning solver
     ** TODO(gmalecha): This should be refactored
     **)
    Lemma eq_trans_hyp
      : forall a b c d: nat,
        a = c + 1 ->
        c = d ->
        d + 1 = b ->
        a = b.
    Proof. intros; subst. reflexivity. Qed.

    Definition andI_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: and_split ::>.
    Definition eq_trans_hyp_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: eq_trans_hyp ::>.
    Definition prove_Prop_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: prove_Prop ::>.

    Definition ptrn_plus : Ptrns.ptrn imp_func unit :=
      fun e X yes no =>
        match e with
        | natPlus => yes tt
        | x => no x
        end.

    Global Instance ptrn_ok_ptrn_plus : ltac:(Ptrns.PtrnOk ptrn_plus).
    Proof. Ptrns.solve_ok. Qed.

    Lemma Succeeds_ptrn_plus e res :
      Ptrns.Succeeds e ptrn_plus res ->
      e = natPlus /\ res = tt.
    Proof. Ptrns.solve_Succeeds. Qed.

    Global Instance SucceedsE_ptrn_plus e res
    : Ptrns.SucceedsE e ptrn_plus res :=
    { s_elim := Succeeds_ptrn_plus e res }.

    Definition ptrn_nat : Ptrns.ptrn imp_func nat :=
      fun e X yes no =>
        match e with
        | pNat v => yes v
        | x => no x
        end.

    Instance ptrn_ok_ptrn_nat : ltac:(Ptrns.PtrnOk ptrn_nat).
    Proof. Ptrns.solve_ok. Qed.

    Lemma Succeeds_ptrn_nat e res :
      Ptrns.Succeeds e ptrn_nat res ->
      e = pNat res.
    Proof.
      destruct e; compute; try solve [ refine (fun x => x _ _ (fun x => x)) ].
    Qed.

    Global Instance SucceedsE_ptrn_nat e res
    : Ptrns.SucceedsE e ptrn_nat res :=
    { s_elim := Succeeds_ptrn_nat e res }.

    Definition ptrn_eq {X : Type} (p : Ptrns.ptrn typ X)
    : Ptrns.ptrn imp_func X :=
      fun e X yes no =>
        match e with
        | pEq t => p t X yes (fun x => no (pEq x))
        | x => no x
        end.

    Global Instance ptrn_ok_ptrn_eq : ltac:(Ptrns.PtrnOk @ptrn_eq).
    Proof. Ptrns.solve_ok. Qed.

    Lemma Succeeds_ptrn_eq {T : Type} e (res : T) p :
      Ptrns.ptrn_ok p ->
      Ptrns.Succeeds e (ptrn_eq p) res ->
      exists t, e = pEq t /\
                Ptrns.Succeeds t p res.
    Proof. intro; Ptrns.solve_Succeeds. Qed.


    Require MirrorCore.Views.Ptrns.

    Definition nat_red@{} : RedAll.partial_reducer typ func :=
      let p : Ptrns.ptrn (expr typ func) (expr typ func) :=
          Views.Ptrns.pmap (fun ab : nat * nat =>
                              let (a,b) := ab in
                              mkImp (pNat (a + b)))
            (Ptrns.app (Ptrns.appl (Ptrns.inj (ptrn_view _ ptrn_plus))
                                   (Views.Ptrns.pmap (fun (x : nat) (_ : unit) => x) (Ptrns.inj (ptrn_view _ ptrn_nat)))) (Ptrns.inj (ptrn_view _ ptrn_nat)))
      in fun f xs =>
           let e := AppN.apps f xs in
           Ptrns.run_ptrn p e e.

    Ltac solve_ok :=
      repeat first [ eapply Ptrns.ptrn_ok_pmap
                   | eapply Ptrns.ptrn_ok_app
                   | eapply Ptrns.ptrn_ok_appl
                   | eapply Ptrns.ptrn_ok_inj
                   | eapply View.ptrn_view_ok
                   | eauto with typeclass_instances
                   ].

    Typeclasses Transparent FuncView.FuncViewOk.
    Definition TypeView_FuncView : forall F A pv ty (rty : RType ty) s1 s2,
        @FuncView.FuncViewOk F A pv ty rty s1 s2 ->
        View.PartialViewOk pv (FuncView.func_equiv _ _) :=
      fun _ _ _ _ _ _ _ x => x.

    Hint Extern 1 (@View.PartialViewOk _ _ _ _) =>
    eapply TypeView_FuncView; eauto 1 with typeclass_instances
                                           : typeclass_instances.

    Theorem nat_red_sound@{} : RedAll.partial_reducer_ok nat_red.
    Proof.
      red. intros. simpl.
      unfold nat_red.
      revert H.
      eapply Ptrns.run_ptrn_sound.
      { refine _. }
      { red. red. red. intros; subst. reflexivity. }
      { intros.
        Ptrns.ptrn_elim. subst. subst.
        generalize dependent (AppN.apps e es); intros; subst.
        destruct x; simpl in *.
        assert (t = CoreTypes.tyBase0 tyValue).
        { autorewrite with exprD_rw in H0.
          cbn in H0.
          destruct (CoreTypes.ctyp_cast tsym _ t
                     (CoreTypes.tyBase0 tyValue)). auto. inversion H0. }
        subst. cbn in H0.
        inv_all. subst.
        cbn. eexists; split; eauto. }
      { intros. eexists; split; try eassumption.
        auto. }
    Qed.

    Lemma refl_eq_nat : forall a : nat, a = a.
    Proof. reflexivity. Qed.

    Definition eq_nat_refl_lemma : Lemma.lemma typ (expr typ func) (expr typ func)
    := <:: refl_eq_nat ::>.
    Instance RL_eq_nat_refl_lemma : ReifiedLemma eq_nat_refl_lemma :=
      mkRL eq_nat_refl_lemma refl_eq_nat.

    Definition prove_eq_tac : imp_tac :=
      SIMPL true (RedAll.red_partial nat_red) ;;
            ON_ALL (EAPPLY eq_nat_refl_lemma).

    Instance RtacSound_prove_eq_tac : RtacSound prove_eq_tac.
    Proof.
      unfold prove_eq_tac.
      rtac_derive_soundness_with.
      eapply RtacSound_SIMPL.
      eapply RedAll.red_partial_ok.
      eapply nat_red_sound.
    Qed.
    (** TODO(gmalecha): This ends the arithmetic reasoning solver **)


    Fixpoint THENS (ls : list imp_tac) : imp_tac :=
      match ls with
      | nil => IDTAC
      | l :: ls => THEN l (runOnGoals (THENS ls))
      end.

    Definition the_final_tactic : imp_tac :=
      THEN (THENS (sym_eval_no_mem 100 (TRY entailment_tac) ::
                   REPEAT 1000 (EAPPLY andI_lemma) ::
                   TRY (EAPPLY prove_Prop_lemma) ::
                   TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                               TRY EASSUMPTION :: nil)) ::
                   INSTANTIATE :: TRY prove_eq_tac :: nil)) MINIFY.

    Definition PHASE1 : imp_tac :=
      sym_eval_no_mem 100 IDTAC.

    Definition PHASE2 : imp_tac :=
      sym_eval_no_mem 100 SIMPLIFY ;; MINIFY.

    Definition PHASE3 : imp_tac :=
      sym_eval_no_mem 100
        (THENS (TRY (EAPPLY embed_ltrue_lemma) ::
                TRY (THENS (EAPPLY entails_exL_lemma ::
                            INTRO_All ::
                            BETA_REDUCE :: nil)) ::
                TRY (THENS (EAPPLY go_lower_raw_lemma ::
                            BETA_REDUCE :: INTRO_All ::
                            BETA_REDUCE :: nil)) ::
                SIMPLIFY :: SIMPLIFY ::
                REPEAT 200
                (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil)) ::
                TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil)) ::
                REPEAT 1000 (EAPPLY andI_lemma) ::
                TRY (EAPPLY prove_Prop_lemma) ::
                TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                            TRY EASSUMPTION :: nil)) ::
                INSTANTIATE :: TRY prove_eq_tac :: nil))  ;; MINIFY.

    Instance THENS_sound : forall ls,
        Forall RtacSound ls ->
        RtacSound (THENS ls).
    Proof.
      induction 1.
      - intros. simpl. rtac_derive_soundness_with.
      - simpl. rtac_derive_soundness_with.
    Qed.

    Instance RL_andI : ReifiedLemma andI_lemma.
    Proof. prove_RL and_split. Qed.
    Instance RL_proveProp : ReifiedLemma prove_Prop_lemma.
    Proof. prove_RL prove_Prop. Qed.
    Instance RL_eq_trans_hyp : ReifiedLemma eq_trans_hyp_lemma.
    Proof. prove_RL eq_trans_hyp. Qed.

    Typeclasses Opaque THENS sym_eval_no_mem.

    Theorem PHASE2_sound : RtacSound PHASE2.
    Proof.
      unfold PHASE2.
      rtac_derive_soundness_with; eauto with typeclass_instances.
    Qed.

    Instance RtacSound_BETA_REDUCE : RtacSound BETA_REDUCE.
    Proof. unfold BETA_REDUCE. eapply RtacSound_SIMPL.
           eapply RedAll.red_beta_sound.
           eapply RedAll.red_id_sound.
    Qed.

    Typeclasses Opaque INTRO_Hyp SIMPLIFY INSTANTIATE BETA_REDUCE
                sym_eval_no_mem.

    Typeclasses Opaque rtacK_sound rtac_sound.

    Theorem PHASE3_sound : RtacSound PHASE3.
    Proof.
      unfold PHASE3.
      eapply THEN_sound.
      simple eapply sym_eval_no_mem_sound.
      rtac_derive_soundness_with.
      eapply THENS_sound;
        rtac_derive_soundness_with; eauto with typeclass_instances.
      rtac_derive_soundness_with; eauto with typeclass_instances.
    Qed.

  End with_fs.

  Create HintDb reduce_stuff.
  Hint Rewrite locals_get_locals_upd eval_iexpr_iPlus
       eval_iexpr_iConst eval_iexpr_iVar land_apply : reduce_stuff.
  Hint Rewrite get_upd_not using congruence : reduce_stuff.


  Ltac ltac_finish :=
    (intros; eapply embed_ltrue;
     eapply ILogic.lexistsL; intros;
     eapply I.go_lower_raw; intro;
     autorewrite with reduce_stuff;
     repeat (eapply pull_embed_hyp; intros);
     try (eapply pull_embed_last_hyp; intros);
     subst;
     repeat eapply and_split; eapply prove_Prop; assumption).

  Require Import MirrorCore.Reify.Reify.

  Ltac run_tactic_env tac tac_sound :=
    match goal with
    | |- ?goal =>
      let k tbl g :=
          let result := constr:(runRtac typ (expr typ func) nil nil g (tac tbl)) in
          let resultV := eval vm_compute in result in
          lazymatch resultV with
          | Solved _ =>
            change (@propD _ _ _ (@CoreTypes.Typ0_Prop _ _) (Expr_expr tbl) nil nil g) ;
              cut(result = resultV) ;
              [ exact (@rtac_Solved_closed_soundness _ _ _ _ _ _ (tac_sound tbl) nil nil g)
              | vm_cast_no_check (@eq_refl _ resultV) ]
          | More_ _ ?g' =>
            pose (g'V := g') ;
            let post := constr:(match @goalD _ _ _ (@CoreTypes.Typ0_Prop _ _) (Expr_expr tbl) nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                                end) in
            let post := reduce_propD tbl g'V post in
            let G := post in
            cut G ;
              [ change (@closedD _ _ _ (@CoreTypes.Typ0_Prop _ _) (Expr_expr tbl) nil nil g g'V) ;
                cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                [ exact (@rtac_More_closed_soundness _ _ _ _ _ _ (tac_sound tbl) nil nil g g'V)
                | vm_cast_no_check (@eq_refl _ resultV) ]
              | try clear g'V tbl g ]
          | Fail => fail "tactic failed"
          end
      in
      reify_expr_bind reify_imp k
                      [[ (fun x : mk_dvar_map term_table (@SymEnv.F typ RType_typ) => True) ]]
                      [[ goal ]]
    end.

  Notation "P //\\ Q" := (@ILogic.land _ _ P Q) (at level 80).

(*
  Goal let lst := (tonums (seq 1)) in
       @ILogic.lentails I.SProp I.ILogicOps_SProp (@ILogic.ltrue I.SProp I.ILogicOps_SProp)
                        (I.triple (assign_linear 0 lst)
                                  (increment_all lst)
                                  (assign_linear 1 lst)).
  Proof.
    reducer.
    (* Time (run_tactic PHASE1; ltac_finish).
Time (run_tactic PHASE2; ltac_finish). *)
    Time run_tactic_env PHASE3 PHASE3_sound.
  (* Time run_tactic (PHASE3_tauto). *)
  (* Time run_tactic (PHASE3_tauto2). *)
    intros. rewrite eval_iexpr_iPlus in H.
    rewrite eval_iexpr_iVar in H.
    rewrite eval_iexpr_iConst in H.
    rewrite locals_get_locals_upd in *.
    rewrite H.
    tauto.
  Time Qed.
*)

  (** This is setting up the demo **)
  Fixpoint cycle' fst (ls : list string) : list (string * string) :=
    match ls with
    | nil => nil
    | lst :: rst =>
      match rst with
      | nil => (lst,fst) :: nil
      | nxt :: _ =>
        (lst,nxt) :: cycle' fst rst
      end
    end.

  Definition cycle ls : list (string * string) :=
    match ls with
    | nil => nil
    | x :: _ => cycle' x ls
    end.

  Eval compute in cycle ("a"::"b"::"c"::"d"::"e"::"f"::"g"::nil)%string.

  Fixpoint assign_linear from (ls : list string) : I.lprop :=
    match ls with
    | nil => (@ILogic.ltrue _ I.ILogicOps_lprop)
    | l :: nil => (fun mem => @ILogic.embed _ _ I.EmbedOp_Prop_HProp  (I.locals_get l mem = from))
    | l :: ls =>
      (@ILogic.land _ I.ILogicOps_lprop)
        (assign_linear (S from) ls)
        (fun mem => @ILogic.embed _ _ I.EmbedOp_Prop_HProp  (I.locals_get l mem = from))
    end.

  (** TODO(gmalecha): Necessary? *)
  Ltac just_reify tac :=
    match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e tac) in
          let resultV := eval vm_compute in result in
      pose resultV
        in
          reify_expr_bind reify_imp k [[ True ]] [[ goal ]]
    end.

  Fixpoint increment_all (ls : list string) : I.icmd :=
    match ls with
    | nil => I.Skip
    | l :: nil => (I.Assign l (I.iPlus (I.iVar l) (I.iConst 1)))
    | l :: ls => I.Seq (I.Assign l (I.iPlus (I.iVar l) (I.iConst 1))) (increment_all ls)
    end.

  Fixpoint seq (n : nat) : list nat :=
    match n with
    | 0 => nil
    | S n => n :: seq n
    end.

  Definition tonums (ls : list nat) : list string :=
    map (fun n => String (Ascii.ascii_of_nat (65 + n)) EmptyString) ls.

  Ltac reducer :=
    unfold seq, tonums, map, Ascii.ascii_of_nat, Ascii.ascii_of_N, plus, BinNat.N.of_nat, increment_all, Swap_n, cycle, cycle', assign_linear, Datatypes.length;
    simpl; unfold Ascii.ascii_of_pos; unfold Ascii.shift; unfold Ascii.one.


  (* refl + ltac *)
  Goal let lst := (tonums (seq 2)) in
       @ILogic.lentails I.SProp I.ILogicOps_SProp (@ILogic.ltrue I.SProp I.ILogicOps_SProp)
                        (I.triple (assign_linear 0 lst)
                                  (increment_all lst)
                                  (assign_linear 1 lst)).
  Proof.
    reducer.
    Time run_tactic_env PHASE2 PHASE2_sound (* (sym_eval_no_mem 100) *).
    Time ltac_finish.
  Time Qed.
End ImpVerify.

  (*
Definition PHASE3_tauto : imp_tac :=
  let leaf :=
      (THENS (   SIMPLIFY

              :: EAPPLY go_lower_raw_lemma
              :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
              :: REPEAT 200
                   (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil))
              :: TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil))
              :: TRY (EAPPLY prove_Prop_lemma)
              :: TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                             TRY EASSUMPTION :: nil))
              :: INSTANTIATE
              :: TRY prove_eq_tac
              :: nil))
  in
  sym_eval_no_mem 100
     (THENS (   SIMPLIFY
             :: EAPPLY embed_ltrue_lemma
             :: EAPPLY entails_exL_lemma
             :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
             :: tauto_tac leaf :: nil)).
   *)

  (*
Fixpoint parse_ands (e : expr typ func) : list (expr typ func) :=
  match e with
    | App (App (Inj (inr (ILogicFunc.ilf_and (CoreTypestyBase0 tyProp)))) P) Q =>
      parse_ands P ++ parse_ands Q
    | _ => e :: nil
  end.
Definition intro_hyps : imp_tac :=
  fun _ _ _ _ _ sub g =>
    match g with
      | App (App (Inj (inr (ILogicFunc.ilf_entails tyProp))) P) Q =>
        let hyps := parse_ands P in
        let goals := parse_ands Q in
        More sub (List.fold_right GHyp (GConj_list (List.map GGoal goals)) hyps)
      | _ => More_ sub (GGoal g)
    end.

Definition PHASE3_tauto2 : imp_tac :=
  let leaf :=
      (THENS ( intro_hyps ::
               EAPPLY eq_trans_hyp_lemma ::
               TRY EASSUMPTION :: INSTANTIATE ::
               TRY prove_eq_tac
              :: nil))
  in
  sym_eval_only 100
     (THENS (   SIMPLIFY
             :: EAPPLY embed_ltrue_lemma
             :: EAPPLY entails_exL_lemma
             :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
             :: EAPPLY go_lower_raw_lemma :: INTRO_All :: BETA_REDUCE
             :: SIMPLIFY :: BETA_REDUCE :: tauto_tac leaf :: nil)).
   *)
