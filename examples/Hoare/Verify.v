Require Import Coq.Strings.String.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Rtac.
Require Import McExamples.Hoare.Imp.
Require Import McExamples.Hoare.ImpSyntax.
Require Import McExamples.Hoare.ImpMetaTheory.
Require Import McExamples.Hoare.LogicTac.
Require McExamples.Hoare.Tests.

Module ImpVerify (I : ImpLang).
  Module Import Syntax := ImpSyntax I.
  Module Import MetaTheory := ImpTheory I.
  Module Import Tests := Tests.TestCases I.
  Definition imp_tac := rtac typ (expr typ func).
  Definition imp_tacK := rtacK typ (expr typ func).

  Definition ON_ENTAILMENT (yes no : imp_tac) : imp_tac :=
    let check :=
        Ptrns.run_ptrn
          (Ptrns.appr
             (Ptrns.appr
                (Ptrns.inj
                   (FuncView.ptrn_view FuncView_ilfunc
                                       (ILogicFunc.fptrn_lentails
                                          (Ptrns.pmap (fun _ _ _ : unit => true) Ptrns.ignore))))
                Ptrns.ignore) Ptrns.ignore)
          false in
    AT_GOAL (fun _ _ gl => if check gl then yes else no).
  Arguments ON_ENTAILMENT _%rtac _%rtac _ _ _ _ _ _ _.

  Local Open Scope rtac_scope.

  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    embed_ltrue_lemma : embed_ltrue.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    entails_exL_lemma : entails_exL.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    go_lower_raw_lemma : go_lower_raw.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    pull_embed_hyp_lemma : pull_embed_hyp.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    pull_embed_last_lemma : pull_embed_last_hyp.

  Local Existing Instance RType_typ.
  Local Existing Instance RTypeOk_typ.
  Local Existing Instance Typ2_Fun.
  Local Existing Instance Typ2Ok_Fun.
  Local Existing Instance Typ0_Prop.
  Local Existing Instance Typ0Ok_Prop.

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

  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Assert_tail_lemma : Assert_tail_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Assign_tail_lemma : Assign_tail_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Skip_tail_lemma : Skip_tail_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Assert_seq_lemma : Assert_seq_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Skip_seq_lemma : Skip_seq_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    Assign_seq_lemma : Assign_seq_rule.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    triple_exL_lemma : I.triple_exL.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    SeqA_lemma : I.SeqA_rule.



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

  Theorem ON_ENTAILMENT_sound (a b : imp_tac) : rtac_sound a -> rtac_sound b -> rtac_sound (ON_ENTAILMENT a b).
  Proof.
    intros. eapply AT_GOAL_sound.
    intros.
    destruct (Ptrns.run_ptrn
         (Ptrns.appr
            (Ptrns.appr
               (Ptrns.inj
                  (FuncView.ptrn_view FuncView_ilfunc
                     (ILogicFunc.fptrn_lentails
                        (Ptrns.pmap (fun _ _ _ : unit => true) Ptrns.ignore))))
               Ptrns.ignore) Ptrns.ignore) false e); assumption.
  Qed.

  Instance RtacSound_SIMPLIFY : RtacSound SIMPLIFY.
  Proof.
    eapply mkRtacSound.
    eapply SIMPLIFY_sound.
    eapply full_reducer_to_reducer_sound.
    eapply RedAll.red_beta_sound.
    eapply RedAll.red_id_sound.
  Qed.

  Instance RtacSound_INTRO_Hyp : RtacSound INTRO_Hyp.
  Proof.
    eapply (RtacSound_INTRO_hyp lops eops).
    Unshelve.
    2: reflexivity.
    eapply ViewSum.FuncViewOk_right.
    eapply FuncView.FuncViewOk_id.
  Qed.

  Instance RL_embeD_ltrue : ReifiedLemma embed_ltrue_lemma.
  Proof.
    constructor. unfold Lemma.lemmaD. simpl.
    eapply embed_ltrue.
  Defined.
  Instance RL_entails_exL : ReifiedLemma entails_exL_lemma.
  Proof. constructor; unfold Lemma.lemmaD. simpl.
         eapply entails_exL.
  Qed.

  Ltac one_of lems :=
    match lems with
    | (?X,?Y) => first [ one_of X | one_of Y ]
    | _ => exact lems
    end.

  Lemma EAPPLY_THEN_sound : forall lem tac,
      ReifiedLemma lem -> rtac_sound tac ->
      rtac_sound (EAPPLY_THEN lem tac).
  Proof. intros; unfold EAPPLY_THEN.
         rtac_derive_soundness_default.
  Qed.

  Ltac red_lemma :=
    unfold Lemma.lemmaD, Lemma.lemmaD'; simpl; (*
    unfold ExprDsimul.ExprDenote.exprT_App, ExprDsimul.ExprDenote.exprT_Abs,
           exprT_Inj, SymEnv.funcD, ExprDsimul.ExprDenote.Rcast_val,
           ExprDsimul.ExprDenote.Rcast; simpl.
                                                *)
    idtac.

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
      repeat first [ simple eapply Ptrns.ptrn_ok_por
                   | simple eapply Ptrns.ptrn_ok_pmap
                   | simple eapply Ptrns.ptrn_ok_ignore
                   | simple eapply Ptrns.ptrn_ok_get
                   | simple eapply Ptrns.ptrn_ok_appl
                   | simple eapply Ptrns.ptrn_ok_inj
                   | simple eapply FuncView.ptrn_view_ok
                   | simple eapply ILogicFunc.fptrn_lforall_ok ; intros
                   | simple eapply ptrn_entails_ok ]. }
    { eapply intro_ptrn_all_sound with (ilo := lops) (eo := eops).
      - eapply lops_ok.
      - eapply ViewSum.FuncViewOk_right.
        eapply FuncView.FuncViewOk_id.
      - reflexivity. }
  Qed.


  Instance RL_Assign_tail : ReifiedLemma Assign_tail_lemma.
  Proof. constructor; red; simpl. eapply Assign_tail_rule. Qed.

  Instance RL_Assign_seq : ReifiedLemma Assign_seq_lemma.
  Proof. constructor; red; simpl. apply Assign_seq_rule. Qed.

  Instance RL_lower_raw : ReifiedLemma go_lower_raw_lemma.
  Proof. constructor. unfold Lemma.lemmaD. simpl.
         eapply go_lower_raw.
  Qed.

  Instance RL_pull_embed_hyp : ReifiedLemma pull_embed_hyp_lemma.
  Proof. constructor. unfold Lemma.lemmaD. simpl.
         eapply pull_embed_hyp.
  Qed.

  Instance RL_pull_embed_last : ReifiedLemma pull_embed_last_lemma.
  Proof. constructor. unfold Lemma.lemmaD. simpl.
         eapply pull_embed_last_hyp.
  Qed.

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
                    ltac:(try solve [ red_lemma; eauto with the_hints
                                    | one_of I.triple_exL
                                    | eauto with typeclass_instances ]).


  Instance RL_SeqA : ReifiedLemma SeqA_lemma.
  Proof. constructor; red; simpl. eapply I.SeqA_rule. Qed.
  Instance RL_triple_exL : ReifiedLemma triple_exL_lemma.
  Proof. constructor; red; simpl. eapply I.triple_exL. Qed.
  Instance RL_Skip_seq : ReifiedLemma Skip_seq_lemma.
  Proof. constructor; red; simpl. eapply Skip_seq_rule. Qed.
  Instance RL_Assert_seq : ReifiedLemma Assert_seq_lemma.
  Proof. constructor; red; simpl. eapply Assert_seq_rule. Qed.
  Instance RL_Skip_tail : ReifiedLemma Skip_tail_lemma.
  Proof. constructor; red; simpl. eapply Skip_tail_rule. Qed.
  Instance RL_Assert_tail : ReifiedLemma Assert_tail_lemma.
  Proof. constructor; red; simpl. eapply Assert_tail_rule. Qed.

  Theorem sym_eval_no_mem_sound
  : forall n t, RtacSound t -> RtacSound (sym_eval_no_mem n t).
  Proof.
    intros. unfold sym_eval_no_mem.
    rtac_derive_soundness_with.
  Qed.

  Ltac reduce_propD tbl g e := eval cbv beta iota zeta delta
    [ tbl g Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      RS ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip
e tbl Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym
      mkExt mkLogic mkImp

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym Syntax.RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip


  var uvar typeof_sym type_cast typD typ2_match typ2_cast typ2 tenv
      symD symAs
      HList.nth_error_get_hlist_nth ExprDsimul.ExprDenote.lambda_exprD
      HList.hlist_tl HList.hlist_hd
      ExprDsimul.ExprDenote.func_simul
      exprT_UseU exprT_UseV exprT_Inj
      ExprDsimul.ExprDenote.exprT_GetVAs
      ExprDsimul.ExprDenote.exprT_GetUAs
      AbsAppI.exprT_App
      exprT
      eq_trans
      eq_sym
      Rty
      Rsym
      Relim
      RFun
      OpenT
      ExprDsimul.ExprDenote.Rcast_val
      ExprDsimul.ExprDenote.Rcast

      BinPos.Pos.succ
      SymEnv.from_list
      FMapPositive.PositiveMap.empty
      FMapPositive.PositiveMap.add


      (* RS Dependencies *)
      Vector.vector_tl
      Vector.vector_hd
      Vector.vector_map
      Vector.vector_dec
      typeof_sym_imp
      typeof_sym
      ILogicFunc.typeof_func
      ModularTypes.type_for_arity
      type_cast
      typD
      ILogicFunc.typ2_cast_quant
      ILogicFunc.typ2_cast_bin
      typ2_cast
      typ2
      typ0
      typ0_cast
      typ
      tyLProp
      tsym_tag
      tsym_neq

      tsym_dec
      tsymD

      sym_eqb
      symD
      sumbool_rect
      sumbool_rec
      BinPos.Pos.succ
      String.string_dec
      RelDec.rel_dec
      Applicative.pure
      projT2
      projT1
      Nat.pred


      not
      nat_rect
      nat_rec
      nat_eq_eqdec
      ModularTypes.mtyp_dec
      ModularTypes.mtyp_cast
      ModularTypes.mtypD

      lops
      SymEnv.join_functions
      EqdepFacts.internal_eq_sym_involutive
      EqdepFacts.internal_eq_sym_internal
      EqdepFacts.internal_eq_rew_r_dep
      Injection.injection

      imp_func_eq
      SymEnv.func_typeof_sym
      SymEnv.funcD
      ILogicFunc.funcD
      SymEnv.ftype
      fs
      SymEnv.from_list
      FMapPositive.PositiveMap.find
      SymEnv.fdenote
      f_equal_nat
      f_equal
      BinPos.Pos.eqb
      PeanoNat.Nat.eqb
      eq_trans
      eq_sym
      eq_rect
      eq_ind_r
      eq_ind
      eq_equivalence
      PeanoNat.Nat.eq_dec
      eq_add_S
      eq_Transitive
      eq_Symmetric
      eq_Reflexive
      eops
      FMapPositive.PositiveMap.empty
      ILogic.embed
      complement
      bool_rect
      bool_rec
      Bool.bool_dec
      Ascii.ascii_rect
      Ascii.ascii_rec
      Ascii.ascii_dec
      ModularTypes.applyn'
      ModularTypes.applyn
      Applicative.ap
      andb
      and_rect
      and_ind
      FMapPositive.PositiveMap.add
      Nat.add
      Typ2_Fun
      ModularTypes.Typ2_Fun
      ModularTypes.Typ0_sym
      Typ0_Prop
      Rty
      String.RelDec_string
      Positive.RelDec_peq
      ILogicFunc.RelDec_ilfunc
      RelDec_eq_typ
      SymEnv.RelDec_eq_func
      Nat.RelDec_eq
      RelDec_Rty
      RType_typ
      ModularTypes.RType_mtyp
      SymSum.RSym_sum
      RSym_imp_func
      RSym_ilfunc
      ILogicFunc.RSym_ilfunc
      SymEnv.RSym_func
      RS
      RFun
      ModularTypes.Injective_tyApp
      I.ILogicOps_lprop
      Fun
      EqdepFacts.Eq_rect_eq_on
      EqdepFacts.Eq_rect_eq
      EqdepFacts.Eq_dep_eq_on
      EqdepFacts.Eq_dep_eq
      ILogic.EmbedOp_refl
      ILogic.EmbedOp_Fun
      Applicative_Fun
    ] in e.

(*
Ltac the_solver :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e (sym_eval_no_mem 100)) in
          let resultV := eval vm_compute in result in
      match resultV with
        | Solved _ =>
          change (propD _ _ nil nil e) ;
            cut(result = resultV) ;
            [ set (pf := @rtac_Solved_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (sym_eval_no_mem 100)
                           (sym_eval_no_mem_sound 100) nil nil e)
              ; exact pf
            | vm_cast_no_check (@eq_refl _ resultV) ]
        | More_ _ ?g' =>
          pose (g'V := g') ;
          let post := constr:(match @goalD _ _ _ _ _ nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                              end) in
          let post := reduce_propD g'V post in
          match post with
            | ?G =>
              cut G ;
              [ try (change (@closedD _ _ _ _ _ nil nil g g'V) ;
                cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                [ set (pf := @rtac_More_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (sym_eval_no_mem 100)
                           (sym_eval_no_mem_sound 100) nil nil e g'V) ;
                  exact pf
                | vm_cast_no_check (@eq_refl _ resultV) ])
              | clear g'V e ]
          end
      end
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.
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

  Require Import MirrorCore.Reify.Reify.

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

  Lemma eq_trans_hyp
  : forall a b c d: nat,
      a = c + 1 ->
      c = d ->
      d + 1 = b ->
      a = b.
  Proof. intros; subst. reflexivity. Qed.


  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    andI_lemma : and_split.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    eq_trans_hyp_lemma : eq_trans_hyp.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    prove_Prop_lemma : prove_Prop.

(*
  Fixpoint nat_red (e : expr typ func) : expr typ func :=
    match e with
    | App (App (Inj (inl (inr natPlus))) (Inj (inl (inr (pNat l))))) (Inj (inl (inr (pNat r)))) =>
      Inj (inl (inr (pNat (l + r))))
    | _ => e
    end.
*)

  Definition ptrn_plus : Ptrns.ptrn imp_func unit :=
    fun e X yes no =>
      match e with
      | natPlus => yes tt
      | x => no x
      end.

  Instance ptrn_ok_ptrn_plus : Ptrns.ptrn_ok ptrn_plus.
  Proof. red. destruct x; simpl; auto;
              try solve [ right; compute; reflexivity
                        | left; eexists; compute; reflexivity ].
  Qed.

  Lemma Succeeds_ptrn_plus e res :
    Ptrns.Succeeds e ptrn_plus res ->
    e = natPlus /\ res = tt.
  Proof.
    destruct res; split; auto.
    revert H.
    destruct e; compute;
      try solve [ refine (fun x => x _ (fun _ => natPlus) (fun x => x)) ].
  Qed.

  Definition ptrn_nat : Ptrns.ptrn imp_func nat :=
    fun e X yes no =>
      match e with
      | pNat v => yes v
      | x => no x
      end.

  Instance ptrn_ok_ptrn_nat : Ptrns.ptrn_ok ptrn_nat.
  Proof. red. destruct x; simpl; auto;
              try solve [ right; compute; reflexivity
                        | left; eexists; compute; reflexivity ].
  Qed.

  Lemma Succeeds_ptrn_nat e res :
    Ptrns.Succeeds e ptrn_nat res ->
    e = pNat res.
  Proof.
    destruct e; compute; try solve [ refine (fun x => x _ _ (fun x => x)) ].
  Qed.


  Definition ptrn_eq {X : Type} (p : Ptrns.ptrn typ X) : Ptrns.ptrn imp_func X :=
    fun e X yes no =>
      match e with
      | pEq t => p t X yes (fun x => no (pEq x))
      | x => no x
      end.

  Instance ptrn_ok_ptrn_eq {X : Type} (p : Ptrns.ptrn typ X)
    : Ptrns.ptrn_ok p -> Ptrns.ptrn_ok (ptrn_eq p).
  Proof.
    red. destruct x; simpl; auto;
           try solve [ right; compute; reflexivity
                     | left; eexists; compute; reflexivity ].
    destruct (H t); [ left | right ].
    { destruct H0. exists x. compute. red in H0.
      intros. rewrite H0. reflexivity. }
    { compute. intros. rewrite H0. reflexivity. }
  Qed.

  Lemma Succeeds_ptrn_eq {T : Type} e (res : T) p :
    Ptrns.ptrn_ok p ->
    Ptrns.Succeeds e (ptrn_eq p) res ->
    exists t, e = pEq t /\
      Ptrns.Succeeds t p res.
  Proof.
    intros.
    destruct e; compute in H0;
      try solve [ specialize (H0 _ (fun _ => true) (fun _ => false));
                  inversion H0 ].
    destruct (H t).
    { destruct H1. exists t. split; auto.
      red in H1.
      setoid_rewrite H1 in H0.
      red. intros. rewrite H1. eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      specialize (H0 _ (fun _ => true) (fun _ => false));
        inversion H0. }
  Qed.

  Instance FuncView_imp_func : FuncView.FuncView func imp_func :=
    ViewSum.FuncView_left (ViewSum.FuncView_right FuncView.FuncView_id).

  Instance FuncViewOk_imp_func : @FuncView.FuncViewOk func imp_func _ _ _ _ _.
  Proof.
    eapply ViewSum.FuncViewOk_left.
    eapply ViewSum.FuncViewOk_right.
    eapply FuncView.FuncViewOk_id.
  Qed.

  Require MirrorCore.Views.Ptrns.

  Definition nat_red : RedAll.partial_reducer typ func :=
    let p : Ptrns.ptrn (expr typ func) (expr typ func) :=
        Views.Ptrns.pmap (fun ab : nat * nat => let (a,b) := ab in
                                                mkImp (pNat (a + b)))
                         (Ptrns.app (Ptrns.appl (Ptrns.inj (FuncView.ptrn_view _ ptrn_plus))
                                                (Views.Ptrns.pmap (fun x _ => x) (Ptrns.inj (FuncView.ptrn_view _ ptrn_nat)))) (Ptrns.inj (FuncView.ptrn_view _ ptrn_nat)))
    in fun f xs =>
         let e := AppN.apps f xs in
         Ptrns.run_ptrn p e e.

  Require Import ExtLib.Tactics.
  Require Import ExtLib.Core.RelDec.

  Ltac solve_ok :=
    repeat first [ eapply Ptrns.ptrn_ok_pmap
                 | eapply Ptrns.ptrn_ok_app
                 | eapply Ptrns.ptrn_ok_appl
                 | eapply Ptrns.ptrn_ok_inj
                 | eapply FuncView.ptrn_view_ok
                 | eauto with typeclass_instances
                 ].

  Theorem nat_red_sound : RedAll.partial_reducer_ok nat_red.
  Proof.
    red. intros. simpl.
    unfold nat_red.
    revert H.
    eapply Ptrns.run_ptrn_sound.
    { solve_ok. }
    { red. red. red. intros; subst. reflexivity. }
    { intros.
      repeat match goal with
             | H : Ptrns.Succeeds _ _ _ |- _ =>
               first [ simple eapply Ptrns.Succeeds_pmap in H ; [ | solve [ solve_ok ] ]
                     | simple eapply Ptrns.Succeeds_app in H ; [ | solve [ solve_ok ] | solve [ solve_ok ] ]
                     | eapply Ptrns.Succeeds_appl in H ; [ | solve [ solve_ok ] | solve [ solve_ok ] ]
                     | eapply Ptrns.Succeeds_inj in H ; [ | solve [ solve_ok ] ]
                     | eapply FuncView.Succeeds_ptrn_view in H ;
                       [
                       | eauto with typeclass_instances
                       | eauto with typeclass_instances
                       | solve [ solve_ok ] ]
                     | eapply Succeeds_ptrn_nat in H
                     | eapply Succeeds_ptrn_plus in H
                     ] ; forward_reason
             end; subst.
      generalize dependent (AppN.apps e es); intros; subst.
      destruct x; simpl in *.
      assert (t = ModularTypes.tyBase0 tyValue).
      { autorewrite with exprD_rw in H0.
        cbn in H0.
        destruct (ModularTypes.mtyp_cast tsym (@tsym_dec) t
                     (ModularTypes.tyBase0 tyValue)). auto. inversion H0. }
      subst. cbn in H0.
      inv_all. subst.
      cbn. eexists; split; eauto. }
    { intros. eexists; split; try eassumption.
      auto. }
  Qed.

  Lemma refl_eq_nat : forall a : nat, a = a.
  Proof. reflexivity. Qed.

  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
     eq_nat_refl_lemma : refl_eq_nat.
  Instance RL_eq_nat_refl_lemma : ReifiedLemma eq_nat_refl_lemma :=
    mkRL eq_nat_refl_lemma refl_eq_nat.

  Definition prove_eq_tac : imp_tac :=
    SIMPL true (RedAll.red_partial nat_red) ;;
    ON_ALL (EAPPLY eq_nat_refl_lemma).
(*
    fun _ _ _ _ _ sub e =>
      match e with
      | App (App (Inj (inl (inr (pEq t)))) L) R =>
        let l' := nat_red L in
        let r' := nat_red R in
        if l' ?[ eq ] r' then Solved sub
        else More_ sub (GGoal (App (App (Inj (inl (inr (pEq t)))) l') r'))
      | _ => Fail
      end.
*)

  Instance RtacSound_prove_eq_tac : RtacSound prove_eq_tac.
  Proof.
    unfold prove_eq_tac.
    rtac_derive_soundness_with.
    eapply RtacSound_SIMPL.
    eapply RedAll.red_partial_ok.
    eapply nat_red_sound.
  Qed.


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
                 INSTANTIATE :: TRY prove_eq_tac :: nil)) (MINIFY).

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
  Proof. constructor. red; simpl. eapply and_split. Qed.
  Instance RL_proveProp : ReifiedLemma prove_Prop_lemma.
  Proof. constructor; red; simpl. eapply prove_Prop. Qed.
  Instance RL_eq_trans_hyp : ReifiedLemma eq_trans_hyp_lemma.
  Proof. constructor; red; simpl. eapply eq_trans_hyp. Qed.

  Theorem PHASE2_sound : RtacSound PHASE2.
  Proof.
    unfold PHASE2.
    rtac_derive_soundness_with.
    eapply sym_eval_no_mem_sound.
    2: eauto with typeclass_instances.
    2: eauto with typeclass_instances.
    2: eauto with typeclass_instances.
    rtac_derive_soundness_with.
  Qed.


  Theorem PHASE3_sound : RtacSound PHASE3.
  Proof.
    unfold PHASE3.
    rtac_derive_soundness_with.
    2: eauto with typeclass_instances.
    2: eauto with typeclass_instances.
    2: eauto with typeclass_instances.
    eapply sym_eval_no_mem_sound.
    eapply THENS_sound.
    rtac_derive_soundness_with.
    eapply RtacSound_INSTANTIATE.
  Qed.

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
    | App (App (Inj (inr (ILogicFunc.ilf_and (ModularTypestyBase0 tyProp)))) P) Q =>
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


  Create HintDb reduce_stuff.
  Hint Rewrite locals_get_locals_upd eval_iexpr_iPlus
       eval_iexpr_iConst eval_iexpr_iVar land_apply : reduce_stuff.
  Hint Rewrite get_upd_not using congruence : reduce_stuff.

  Let tyNat := ModularTypes.tyBase0 tyValue.
  Let tyArr := @ModularTypes.tyArr tsym.
  Let tyLocals := ModularTypes.tyBase0 tyLocals.
  Let tyHProp := ModularTypes.tyBase0 tyHProp.
  Let tyProp := ModularTypes.tyBase0 tyProp.

(*
  Eval vm_compute in
      doIt (THENS (   SIMPLIFY
                   :: EAPPLY entails_exL_lemma :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
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
                   :: nil)).
*)

  End with_fs.

  Ltac reducer :=
    unfold seq, tonums, map, Ascii.ascii_of_nat, Ascii.ascii_of_N, plus, BinNat.N.of_nat, increment_all, Swap_n, cycle, cycle', assign_linear, Datatypes.length;
    simpl; unfold Ascii.ascii_of_pos; unfold Ascii.shift; unfold Ascii.one.

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

  Ltac reduce_propD tbl g e := eval cbv beta iota zeta delta
    [ tbl g Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      RS ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip

      tbl Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym
      mkExt mkLogic mkImp

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym Syntax.RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip


  var uvar typeof_sym type_cast typD typ2_match typ2_cast typ2 tenv
      symD symAs
      HList.nth_error_get_hlist_nth ExprDsimul.ExprDenote.lambda_exprD
      HList.hlist_tl HList.hlist_hd
      ExprDsimul.ExprDenote.func_simul
      exprT_UseU exprT_UseV exprT_Inj
      ExprDsimul.ExprDenote.exprT_GetVAs
      ExprDsimul.ExprDenote.exprT_GetUAs
      AbsAppI.exprT_App
      exprT
      eq_trans
      eq_sym
      Rty
      Rsym
      Relim
      RFun
      OpenT
      ExprDsimul.ExprDenote.Rcast_val
      ExprDsimul.ExprDenote.Rcast

      BinPos.Pos.succ
      SymEnv.from_list
      FMapPositive.PositiveMap.empty
      FMapPositive.PositiveMap.add


      (* RS Dependencies *)
      Vector.vector_tl
      Vector.vector_hd
      Vector.vector_map
      Vector.vector_dec
      typeof_sym_imp
      typeof_sym
      ILogicFunc.typeof_func
      ModularTypes.type_for_arity
      type_cast
      typD
      ILogicFunc.typ2_cast_quant
      ILogicFunc.typ2_cast_bin
      typ2_cast
      typ2
      typ0
      typ0_cast
      typ
      tyLProp
      tsym_tag
      tsym_neq

      tsym_dec
      tsymD
      sym_eqb
      symD
      sumbool_rect
      sumbool_rec
      BinPos.Pos.succ
      String.string_dec
      RelDec.rel_dec
      Applicative.pure
      projT2
      projT1
      Nat.pred


      not
      nat_rect
      nat_rec
      nat_eq_eqdec
      ModularTypes.mtyp_dec
      ModularTypes.mtyp_cast
      ModularTypes.mtypD

      lops
      SymEnv.join_functions
      EqdepFacts.internal_eq_sym_involutive
      EqdepFacts.internal_eq_sym_internal
      EqdepFacts.internal_eq_rew_r_dep
      Injection.injection

      imp_func_eq
      SymEnv.func_typeof_sym
      SymEnv.funcD
      ILogicFunc.funcD
      SymEnv.ftype
      fs
      SymEnv.from_list
      FMapPositive.PositiveMap.find
      SymEnv.fdenote
      f_equal_nat
      f_equal
      BinPos.Pos.eqb
      PeanoNat.Nat.eqb
      eq_trans
      eq_sym
      eq_rect
      eq_ind_r
      eq_ind
      eq_equivalence
      PeanoNat.Nat.eq_dec
      eq_add_S
      eq_Transitive
      eq_Symmetric
      eq_Reflexive
      eops
      FMapPositive.PositiveMap.empty
      complement
      bool_rect
      bool_rec
      Bool.bool_dec
      Ascii.ascii_rect
      Ascii.ascii_rec
      Ascii.ascii_dec
      ModularTypes.applyn'
      ModularTypes.applyn
      Applicative.ap
      andb
      and_rect
      and_ind
      FMapPositive.PositiveMap.add
      Typ2_Fun
      ModularTypes.Typ2_Fun
      ModularTypes.Typ0_sym
      Typ0_Prop
      Rty
      String.RelDec_string
      Positive.RelDec_peq
      ILogicFunc.RelDec_ilfunc
      RelDec_eq_typ
      SymEnv.RelDec_eq_func
      Nat.RelDec_eq
      RelDec_Rty
      RType_typ
      ModularTypes.RType_mtyp
      SymSum.RSym_sum
      RSym_imp_func
      RSym_ilfunc
      ILogicFunc.RSym_ilfunc
      SymEnv.RSym_func
      RS
      RFun
      ModularTypes.Injective_tyApp
      Fun
      ILogic.EmbedOp_refl
      ILogic.EmbedOp_Fun
      Applicative_Fun
      UIP_trans.uip_trans
      UIP_trans.uip_prop_trans
      RS
      RFun
      ModularTypes.Injective_tyApp
      Fun
      Applicative_Fun
      Traversable.mapT
      List.Traversable_list Option.Applicative_option
      List.mapT_list
      Ctx.propD exprD_typ0 exprD Expr_expr app
      Quant._impls
      List.map
      HList.hlist_app
      amap_substD FMapSubst.SUBST.raw_substD UVarMap.MAP.fold FMapPositive.PositiveMap.fold FMapPositive.PositiveMap.xfoldi HList.nth_error_get_hlist_nth UVarMap.MAP.from_key FMapPositive.append Nat.pred BinPos.Pos.to_nat BinPos.Pos.iter_op Nat.add
      tsym_dec Quant._exists exprT_Inj
      UVarMap.MAP.from_key
      Nat.pred BinPos.Pos.to_nat BinPos.Pos.iter_op Nat.add  ModularTypes.mtyp_cast
    ] in e.

  Ltac run_tactic_env tac tac_sound :=
    match goal with
    | |- ?goal =>
      let k tbl g :=
          let result := constr:(runRtac typ (expr typ func) nil nil g (tac tbl)) in
          let resultV := eval vm_compute in result in
          lazymatch resultV with
          | Solved _ =>
            change (@propD _ _ _ Typ0_Prop (Expr_expr tbl) nil nil g) ;
              cut(result = resultV) ;
              [ exact (@rtac_Solved_closed_soundness _ _ _ _ _ _ (tac_sound tbl) nil nil g)
              | vm_cast_no_check (@eq_refl _ resultV) ]
          | More_ _ ?g' =>
            pose (g'V := g') ;
            let post := constr:(match @goalD _ _ _ Typ0_Prop (Expr_expr tbl) nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                                end) in
            let post := reduce_propD tbl g'V post in
            let G := post in
            cut G ;
              [ change (@closedD _ _ _ Typ0_Prop (Expr_expr tbl) nil nil g g'V) ;
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

  (* refl + ltac *)
  Goal let lst := (tonums (seq 1)) in
       @ILogic.lentails I.SProp I.ILogicOps_SProp (@ILogic.ltrue I.SProp I.ILogicOps_SProp)
                        (I.triple (assign_linear 0 lst)
                                  (increment_all lst)
                                  (assign_linear 1 lst)).
  Proof.
    reducer.
    Time run_tactic_env PHASE2 PHASE2_sound (* (sym_eval_no_mem 100) *).
    admit.
(*
    Time (intros; subst;
          repeat eapply and_split; eapply prove_Prop; assumption).
*)
  Time Admitted.
End ImpVerify.
