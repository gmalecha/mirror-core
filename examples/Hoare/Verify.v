Require Import Coq.Strings.String.
Require Import MirrorCore.RTac.RTac.
(*Require Import MirrorCharge.Imp.Goal.*)
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Rtac.
Require Import McExamples.Hoare.Imp.
(*Require Import MirrorCharge.Imp.SymEvalLemmas.*)
(*Require MirrorCharge.Imp.STacCancel. *)
Require Import McExamples.Hoare.ImpSyntax.
Require Import McExamples.Hoare.ImpMetaTheory.
Require Import McExamples.Hoare.LogicTac.
Require McExamples.Hoare.Tests.
(*Require Import MirrorCharge.Imp.RTacTauto. *)

(*
Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.
*)
(*
Definition runTacK (tac : imp_tacK) : imp_tac :=
  fun a b c d e f g => tac a b c d e f (GGoal g).
*)


(*
Fixpoint THENS (ls : list (rtac typ (expr typ func))) : imp_tac :=
  match ls with
    | nil => IDTAC
    | l :: ls => THEN l (runOnGoals (THENS ls))
  end.
*)
(*
Definition side_solver : imp_tac :=
  THENS (TRY (THENS (EAPPLY go_lower_lemma ::
                            INTRO_All ::
                            BETA_REDUCE :: nil)) ::
             TRY (EAPPLY embed_ltrue_lemma) ::
             SIMPLIFY ::
             STacCancel.stac_cancel ::
             SIMPLIFY :: tauto_tac :: nil).
*)


Module ImpVerify (I : ImpLang).
  Module Import Syntax := ImpSyntax I.
  Module Import MetaTheory := ImpTheory I.
  Module Import Tests := Tests.TestCases I.
  Definition imp_tac := rtac typ (expr typ func).
  Definition imp_tacK := rtacK typ (expr typ func).

  Definition ON_ENTAILMENT (yes no : imp_tac) : imp_tac :=
    let check :=
        Ptrns.run_default (X:=expr typ func) (T:=bool)
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
    destruct (Ptrns.run_default
         (Ptrns.appr
            (Ptrns.appr
               (Ptrns.inj
                  (FuncView.ptrn_view FuncView_ilfunc
                     (ILogicFunc.fptrn_lentails
                        (Ptrns.pmap (fun _ _ _ : unit => true) Ptrns.ignore))))
               Ptrns.ignore) Ptrns.ignore) false e); assumption.
  Qed.

  Lemma entailment_tac_sound : rtac_sound entailment_tac.
  Proof.
    eapply ON_ENTAILMENT_sound.
    - rtac_derive_soundness_default.
      all: admit.
    - eapply IDTAC_sound.
  Admitted.

  Lemma entailment_tac_solve_sound : rtac_sound entailment_tac_solve.
  Proof. apply SOLVE_sound. apply entailment_tac_sound. Qed.

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
  Theorem INTRO_All_sound : RtacSound INTRO_All.

  Ltac rtac_derive_soundness_with :=
    rtac_derive_soundness'
      ltac:(fun rtac rtacK lem =>
              first [ eapply EAPPLY_THEN_sound ; [ lem | rtac ]
                    | eapply EAPPLY_THEN_1_sound ; [ lem | rtac | rtacK ]
                    | eapply simplify_tac_sound
                    | eapply entailment_tac_sound
                    | eapply entailment_tac_solve_sound
(*                    | eapply INTRO_All_sound *)
                    | match goal with
                      | |- rtac_sound match ?X with _ => _ end =>
                        destruct X; rtac
                      end ])
             ltac:(fun _ _ => fail)
                    ltac:(try solve [ red_lemma; eauto with the_hints
                                    | one_of I.triple_exL ]).

  Theorem sym_eval_no_mem_sound
  : forall n t, RtacSound t -> rtac_sound (sym_eval_no_mem n t).
  Proof.
    intros. unfold sym_eval_no_mem.
(*
    rtac_derive_soundness_with.
  Qed.
*)
  Admitted.

Ltac reduce_propD g e := eval cbv beta iota zeta delta
    [ g Quant._foralls goalD Ctx.propD exprD'_typ0 exprD' Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.exprD' symAs typ0_cast
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

  Lemma and_split
    : forall G P Q : I.HProp,
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G P ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G Q ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       G
                       (@ILogic.land I.HProp I.ILogicOps_HProp P Q).
  Admitted.
  Lemma eq_trans_hyp
    : forall a b c d: nat,
      a = c + 1 ->
      c = d ->
      d + 1 = b ->
      a = b.
  Proof. intros; subst. reflexivity. Qed.
  Lemma prove_Prop :
    forall P : Prop,
      P ->
      @ILogic.lentails I.HProp I.ILogicOps_HProp
                       (@ILogic.ltrue I.HProp I.ILogicOps_HProp)
                       (@ILogic.embed Prop I.HProp I.EmbedOp_Prop_HProp P).
  Proof. Admitted.

  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    andI_lemma : and_split.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    eq_trans_hyp_lemma : eq_trans_hyp.
  Reify BuildLemma < reify_imp_typ reify_imp reify_imp >
    prove_Prop_lemma : prove_Prop.

  Fixpoint nat_red (e : expr typ func) : expr typ func :=
    match e with
    | App (App (Inj (inl (inr natPlus))) (Inj (inl (inr (pNat l))))) (Inj (inl (inr (pNat r)))) =>
      Inj (inl (inr (pNat (l + r))))
    | _ => e
    end.

  Require Import ExtLib.Core.RelDec.
  Definition prove_eq_tac : imp_tac :=
    fun _ _ _ _ _ sub e =>
      match e with
      | App (App (Inj (inl (inr (pEq t)))) L) R =>
        let l' := nat_red L in
        let r' := nat_red R in
        if l' ?[ eq ] r' then Solved sub
        else More_ sub (GGoal (App (App (Inj (inl (inr (pEq t)))) l') r'))
      | _ => Fail
      end.

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
    sym_eval_no_mem 100 SIMPLIFY.

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

  Ltac reducer :=
    unfold seq, tonums, map, Ascii.ascii_of_nat, Ascii.ascii_of_N, plus, BinNat.N.of_nat, increment_all, Swap_n, cycle, cycle', assign_linear, Datatypes.length;
    simpl; unfold Ascii.ascii_of_pos; unfold Ascii.shift; unfold Ascii.one.

  Lemma land_apply
    : forall P Q x,
      @ILogic.land I.lprop I.ILogicOps_lprop P Q x =
      @ILogic.land I.HProp I.ILogicOps_HProp (P x) (Q x).
  Admitted.
  Lemma get_upd_not
    : forall x y x0 m,
      x <> y ->
      I.locals_get x (I.locals_upd y x0 m) =
      I.locals_get x m.
  Admitted.
  Create HintDb reduce_stuff.
  Hint Rewrite locals_get_locals_upd eval_iexpr_iPlus
       eval_iexpr_iConst eval_iexpr_iVar land_apply : reduce_stuff.
  Hint Rewrite get_upd_not using congruence : reduce_stuff.

  Let tyNat := ModularTypes.tyBase0 tyValue.
  Let tyArr := @ModularTypes.tyArr tsym.
  Let tyLocals := ModularTypes.tyBase0 tyLocals.
  Let tyHProp := ModularTypes.tyBase0 tyHProp.
  Let tyProp := ModularTypes.tyBase0 tyProp.

  Definition doIt (todo : imp_tac) :=
    todo nil nil 0 0 (CTop nil nil)
         (TopSubst
            (expr typ
                  (BinNums.positive + imp_func +
                   ILogicFunc.ilfunc typ)) nil nil)
         (App
            (App
               (Inj
                  (inr
                     (ILogicFunc.ilf_entails
                        (tyArr tyLocals tyHProp))))
               (App
                  (Inj
                     (inr
                        (ILogicFunc.ilf_exists tyNat
                                               (tyArr tyLocals tyHProp))))
                  (Abs tyNat
                       (Abs tyLocals
                            (App
                               (App
                                  (Inj
                                     (inr
                                        (ILogicFunc.ilf_and tyHProp)))
                                  (App
                                     (Inj
                                        (inr
                                           (ILogicFunc.ilf_embed
                                              tyProp tyHProp)))
                                     (App
                                        (App
                                           (Inj
                                              (inl (inr (pEq tyNat))))
                                           (Var 1))
                                        (Inj (inl (inr (pNat 0)))))))
                               (App
                                  (Inj
                                     (inr
                                        (ILogicFunc.ilf_embed
                                           tyProp tyHProp)))
                                  (App
                                     (App
                                        (Inj
                                           (inl (inr (pEq tyNat))))
                                        (App
                                           (App
                                              (Inj
                                                 (inl (inr pLocals_get)))
                                              (Inj
                                                 (inl
                                                    (inr (pVar "A"%string)))))
                                           (Var 0)))
                                     (App
                                        (App
                                           (Inj (inl (inr natPlus)))
                                           (Var 1))
                                        (Inj (inl (inr (pNat 1))))))))))))
            (Abs tyLocals
                 (App
                    (Inj
                       (inr
                          (ILogicFunc.ilf_embed tyProp
                                                tyHProp)))
                    (App
                       (App (Inj (inl (inr (pEq tyNat))))
                            (App
                               (App
                                  (Inj
                                     (inl (inr pLocals_get)))
                                  (Inj
                                     (inl
                                        (inr (pVar "A"%string)))))
                               (Var 0)))
                       (Inj (inl (inr (pNat 1)))))))).

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

  Ltac ltac_finish :=
    (intros; eapply embed_ltrue;
     eapply ILogic.lexistsL; intros;
     eapply I.go_lower_raw; intro;
     autorewrite with reduce_stuff;
     repeat (eapply pull_embed_hyp; intros);
     try (eapply pull_embed_last_hyp; intros);
     subst;
     repeat eapply and_split; eapply prove_Prop; assumption).

  Ltac run_tactic tac :=
    match goal with
    | |- ?goal =>
      let k tbl g :=
(*
          let result := constr:(runRtac typ (expr typ func) nil nil g tac) in
          let resultV := eval vm_compute in result in
          match resultV with
          | Solved _ =>
            change (@propD _ _ _ Typ0_Prop Expr_expr nil nil g) ;
              cut(result = resultV) ;
              [ admit
              | vm_cast_no_check (@eq_refl _ resultV) ]
          | More_ _ ?g' =>
            pose (g'V := g') ;
            let post := constr:(match @goalD _ _ _ Typ0_Prop Expr_expr nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                                end) in
            let post := reduce_propD g'V post in
            match post with
            | ?G =>
              cut G ;
                [ change (@closedD _ _ _ Typ0_Prop Expr_expr nil nil g g'V) ;
                  cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                  [ admit
                  | vm_cast_no_check (@eq_refl _ resultV) ]
                | try clear g'V g ]
            end 
          | Fail => idtac "failed"
          end
*)
          idtac
      in
      reify_expr_bind reify_imp k
                      [[ (fun x : mk_dvar_map term_table (@SymEnv.F typ RType_typ) => True) ]]
                      [[ goal ]]
    end.


Goal let lst := (tonums (seq 1)) in
         @ILogic.lentails I.SProp I.ILogicOps_SProp (@ILogic.ltrue I.SProp I.ILogicOps_SProp)
     (I.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
Proof.
  reducer.
  Notation "P //\\ Q" := (@ILogic.land _ _ P Q) (at level 80).
  (* Time (run_tactic PHASE1; ltac_finish).
Time (run_tactic PHASE2; ltac_finish). *)
  Time run_tactic (PHASE3).
About Expr_expr.
Eval compute in exprD' nil nil e (typ0(F:=Prop)).
  
  (* Time run_tactic (PHASE3_tauto). *)
  (* Time run_tactic (PHASE3_tauto2). *)
Time Qed.


(* refl + ltac *)
Goal let lst := (tonums (seq 3)) in
         @ILogic.lentails I.SProp I.ILogicOps_SProp (@ILogic.ltrue I.SProp I.ILogicOps_SProp)
     (I.triple (assign_linear 0 lst)
        (increment_all lst)
        (assign_linear 1 lst)).
reducer.
Time run_tactic (sym_eval_no_mem 100).
Time (intros; subst;
repeat eapply and_split; eapply prove_Prop; assumption).
Time Qed.
