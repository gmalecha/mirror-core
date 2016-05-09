Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.RTac.IdtacK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Polymorphic.
Require Import MirrorCore.Lambda.PolyInst.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  (** This starts plugins for the rewriter **)
  (******************************************)

  Definition func_sdec (a b : func) : bool :=
    match sym_eqb a b with
    | Some x => x
    | _ => false
    end.

  Definition expr_sdec : expr typ func -> expr typ func -> bool :=
    @expr_eq_sdec typ func _ func_sdec.

  Lemma expr_sdec_sound
  : forall a b : expr typ func, expr_sdec a b = true -> a = b.
  Proof using RSymOk_func RelDec_Correct_eq_typ.
    eapply expr_eq_sdec_ok; eauto.
    unfold func_sdec.
    intros. generalize (sym_eqbOk a b); eauto with typeclass_instances.
    destruct (sym_eqb a b); intros; subst; auto.
    inversion H.
  Qed.

  (* This is just a "special" version of the rewriting lemma *)
  Record Proper_concl : Type :=
  { relation : R
  ; term     : expr typ func
  }.

  (* TODO(mario): explain the difference between the following two functions *)
  Definition Proper_conclD (tus tvs : tenv typ) (p : Proper_concl)
  : option (exprT tus tvs Prop) :=
    match typeof_expr tus tvs p.(term) with
    | Some t =>
      match RD RbaseD p.(relation) t
          , lambda_exprD tus tvs t p.(term)
      with
      | Some rD , Some eD =>
        Some (fun us vs => rD (eD us vs) (eD us vs))
      | _ , _ => None
      end
    | None => None
    end.

  Definition Proper_conclP (pc : Proper_concl) : Prop :=
    match pc with
    | Build_Proper_concl r e =>
      match typeof_expr nil nil e with
      | Some t =>
        match RD RbaseD r t with
        | Some rD =>
          match lambda_exprD nil nil t e with
          | Some eD =>
            Morphisms.Proper rD (eD HList.Hnil HList.Hnil)
          | None => False
          end
        | None => False
        end
      | None => False
      end
    end.

  Local Lemma Proper_conclD_Proper_conclP
  : forall x,
    Proper_conclP x ->
    Proper_conclD nil nil x = Some (fun _ _ => Proper_conclP x).
  Proof using.
    destruct x; simpl.
    unfold Proper_conclD. simpl.
    forward.
    f_equal.
    do 2 (apply FunctionalExtensionality.functional_extensionality; intros).
    rewrite (hlist_eta x). rewrite (hlist_eta x0).
    reflexivity.
  Qed.

  (** A "lemma" representing [Proper ...] that can be polymorphic and
   ** use typeclasses.
   **)
  Inductive HintProper : Type :=
  | PPr_tc : forall {n : nat},
      Polymorphic.polymorphic typ n Proper_concl ->
      Polymorphic.polymorphic typ n bool ->
      HintProper.

  (* TODO(mario): this is duplicated in HintDbs.v. We should find a long-term home for it *)
  (* no-op typeclass, used to construct polymorphic types without constraints *)
  Definition tc_any (n : nat) : polymorphic typ n bool :=
    make_polymorphic (fun _ => true).

  Definition with_typeclasses {T : Type} (TD : T -> Prop) {n}
             (tc : polymorphic typ n bool) (pc : polymorphic typ n T)
  : polymorphic typ n Prop :=
    make_polymorphic (fun args =>
                        if inst tc args
                        then TD (inst pc args)
                        else True).

  (* TODO(mario): end duplicated code *)

  Definition ProperHintOk (hp : HintProper) : Prop :=
    match hp with
    | PPr_tc pc tc =>
      polymorphicD (fun x => x) (with_typeclasses Proper_conclP tc pc)
    end.

  (** Convenience constructors for building lemmas that do not use
   ** polymorphism.
   **)
  Definition Pr (pc : Proper_concl) :=
    PPr_tc (n:=0) pc true.

  Theorem Pr_sound (pc : Proper_concl)
  : Proper_conclP pc ->
    ProperHintOk (Pr pc).
  Proof using.
    clear. destruct pc; simpl.
    unfold polymorphicD, with_typeclasses. simpl.
    tauto.
  Qed.

  (** polymorphic proper hint without typeclass constraints *)
  Definition PPr {n : nat} (pc : polymorphic typ n Proper_concl) :=
    PPr_tc (n:=n) pc (tc_any n).

  Theorem PPr_sound {n : nat} (pc : polymorphic typ n Proper_concl)
  : polymorphicD Proper_conclP pc ->
    ProperHintOk (PPr pc).
  Proof using.
    clear.
    unfold ProperHintOk, with_typeclasses. simpl.
    intros. unfold tc_any. eapply polymorphicD_make_polymorphic.
    intros. rewrite inst_make_polymorphic. eapply inst_sound.
    eauto.
  Qed.

  Theorem PPr_tc_sound {n : nat} (pc : polymorphic typ n Proper_concl) tc
  : polymorphicD (fun x => x) (with_typeclasses Proper_conclP tc pc) ->
    ProperHintOk (PPr_tc pc tc).
  Proof using.
    clear. simpl. tauto.
  Qed.


  (** A list of [HintProper]s representing a "database" *)
  Definition ProperDb := list HintProper.

  Definition ProperDbOk (pdb : ProperDb) : Prop :=
    Forall ProperHintOk pdb.

  Local Definition Proper_lemma := Lemma.lemma typ (expr typ func) Proper_concl.

  (* This splits a relation into a relation arity and a relation *)
  Local Fixpoint split_R (r : R) : list R * R :=
    match r with
    | Rrespects l r =>
      let (ls, r) := split_R r in
      (l :: ls, r)
    | _ => (nil, r)
    end.

  Local Lemma split_R_sound : forall r_end r rs,
      split_R r = (rs, r_end) ->
      fold_right Rrespects r_end rs = r.
  Proof using.
    induction r; simpl; intros; inv_all; subst; simpl; try reflexivity.
    destruct (split_R r2). inv_all. subst.
    specialize (IHr2 _ eq_refl).
    simpl. rewrite IHr2. reflexivity.
  Qed.

  Local Definition apply_respectful (lem : Proper_lemma)
             (tacK : rtacK typ (expr typ func))
  : respectful_dec _ _ _ :=
    let (rs,r_final) := split_R lem.(Lemma.concl).(relation) in
    match lem.(Lemma.vars) with
    | nil => match lem.(Lemma.premises) with
             | nil => fun e r =>
                        match expr_sdec e lem.(Lemma.concl).(term)
                            , Req_dec Rbase_eq r r_final
                        with
                        | true , true => rw_ret rs
                        | _ , _ => rw_fail
                        end
             | _ :: _ => fun e r =>
                           (** TODO(gmalecha): Handle this *)
                           rw_fail
             end
    | _ :: _ => fun _ _ => (** TODO(gmalecha): Handle this *)
                  rw_fail
    end.

  Local Theorem apply_respectful_sound : forall lem tacK,
      Lemma.lemmaD Proper_conclD nil nil lem ->
      forall Htac : rtacK_sound tacK,
        respectful_spec RbaseD (apply_respectful lem tacK).
  Proof using RSymOk_func RTypeOk_typD Rbase_eq_ok RelDec_Correct_eq_typ
        Typ2Ok_Fun.
    red; intros.
    unfold apply_respectful in H0.
    consider (split_R (relation (Lemma.concl lem))); intros.
    destruct (Lemma.vars lem) eqn:?.
    { destruct (Lemma.premises lem) eqn:?; try solve [ inversion H2 ].
      generalize (expr_sdec_sound e lem.(Lemma.concl).(term)).
      generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r r0).
      destruct (expr_sdec e (term (Lemma.concl lem))); try solve [ inversion H2 ].
      destruct (Req_dec Rbase_eq r r0); try solve [ inversion H2 ].
      unfold rw_ret in H2. inv_all.
      intros. specialize (H2 eq_refl). specialize (H5 eq_refl).
      subst.
      split; auto. intros.
      forward.
      red in H.
      simpl in H.
      unfold Lemma.lemmaD' in H.
      forwardy. inv_all. subst.
      generalize dependent lem.(Lemma.vars); intros; subst.
      generalize dependent lem.(Lemma.premises); intros; subst.
      simpl in *.
      unfold Proper_conclD in H6.
      forwardy.
      inv_all. subst.
      simpl in *.
      erewrite split_R_sound by eassumption.
      destruct (ExprFacts.lambda_exprD_weaken _ _ _
                   (getUVars ctx) (tvs'++getVars ctx) H8) as [ ? [ ? ? ] ].
      simpl in H.
      generalize (@lambda_exprD_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H4).
      unfold Rty. intros.
      revert H5.
      subst y. intros.
      rewrite H7.
      split; [ reflexivity | ].
      intros.
      eapply Pure_pctxD; eauto.
      intros.
      specialize (@H9 HList.Hnil HList.Hnil us0 (HList.hlist_app vs' vs0)); simpl in H9.
      rewrite H9 in H5.
      rewrite H4 in H.
      inv_all. subst. eapply H5. }
    { inversion H2. }
  Qed.

  Definition or_respectful
             (a b : expr typ func -> R -> mrw typ func (list R))
    : respectful_dec _ _ _ :=
    fun e r => rw_orelse (a e r) (b e r).

  Theorem or_respectful_sound : forall a b,
      respectful_spec RbaseD a ->
      respectful_spec RbaseD b ->
      respectful_spec RbaseD (or_respectful a b).
  Proof using.
    unfold or_respectful. intros.
    red. intros.
    eapply rw_orelse_case in H1; destruct H1; [ eapply H | eapply H0 ];
      eassumption.
  Qed.

  Definition fail_respectful : respectful_dec typ func Rbase :=
    fun _ _ => rw_fail.

  Theorem fail_respectful_sound : respectful_spec RbaseD fail_respectful.
  Proof using.
    red. intros. inversion H.
  Qed.

  Section for_polymorphism.

  Variable unify_function : typ -> typ -> FMapPositive.pmap typ -> option (FMapPositive.pmap typ).
  Variable mkVar : BinNums.positive -> typ.

  Local Definition get_Proper {n : nat}
             (p : polymorphic typ n Proper_concl)
             (tc : polymorphic typ n bool)
             (e : expr typ func)
  : option Proper_concl :=
    let p' := Functor.fmap term p in
    match @get_inst _ _ _ _ mkVar unify_function n p' e with
    | Some args =>
      if Polymorphic.inst tc args
      then Some (Polymorphic.inst p args)
      else None
    | None => None
    end.

  Local Lemma get_Proper_sound :
    forall n (p : polymorphic _ n _) (tc : polymorphic _ _ _) e x,
      get_Proper p tc e  = Some x ->
      polymorphicD (fun x => x) (with_typeclasses Proper_conclP tc p) ->
      Proper_conclP x.
  Proof using.
    unfold get_Proper. simpl. intros.
    forwardy.
    destruct (inst tc y) eqn:Hitc; [|congruence].
    inversion H1. subst. clear H1.
    eapply inst_sound with (v := y) in H0.
    unfold with_typeclasses in H0.
    rewrite inst_make_polymorphic in H0.
    rewrite Hitc in H0.
    assumption.
  Qed.


  Local Definition do_one_prespectful (h : HintProper) : respectful_dec typ func Rbase :=
    match h with
    | PPr_tc pc tc =>
      (fun (e : expr typ func) =>
         match get_Proper pc tc e with
         | Some lem =>
           apply_respectful {| vars := nil
                             ; premises := nil
                             ; concl := lem |} IDTACK e
         | None => fail_respectful e
         end)
    end.

  Local Lemma do_one_prespectful_sound :
    forall hp : HintProper,
      ProperHintOk hp ->
      respectful_spec RbaseD (do_one_prespectful hp).
  Proof using RSymOk_func RTypeOk_typD Rbase_eq_ok RelDec_Correct_eq_typ
        Typ2Ok_Fun.
    intros.
    unfold do_one_prespectful.
    destruct hp.
    red. intros.
    generalize (@get_Proper_sound n p p0 e).
    destruct (get_Proper p p0 e).
    { intros.
      eapply apply_respectful_sound; eauto using IDTACK_sound.
      red. simpl.
      red. simpl.
      specialize (H2 _ eq_refl H).
      rewrite Proper_conclD_Proper_conclP; assumption. }
    { intros.
      apply fail_respectful_sound; auto. }
  Qed.

  (** This is the main entry point for the file *)
  Fixpoint do_prespectful (pdb : ProperDb) : respectful_dec typ func Rbase :=
    match pdb with
    | nil => fail_respectful
    | p :: pdb' =>
      or_respectful (do_one_prespectful p) (fun e => do_prespectful pdb' e)
    end.

  Theorem do_prespectful_sound
  : forall propers,
      ProperDbOk propers ->
      respectful_spec RbaseD (do_prespectful propers).
  Proof using RTypeOk_typD Typ2Ok_Fun RSymOk_func RelDec_Correct_eq_typ Rbase_eq_ok.
    induction 1.
    { eapply fail_respectful_sound. }
    { simpl. eapply or_respectful_sound; eauto using do_one_prespectful_sound. }
  Qed.

  End for_polymorphism.

  (** This is the non-polymorphic entry point *)
  Definition do_respectful : ProperDb -> respectful_dec typ func Rbase :=
    do_prespectful (fun _ _ => Some) (fun _ => typ0 (F:=Prop)).

  Theorem do_respectful_sound
  : forall propers,
      ProperDbOk propers ->
      respectful_spec RbaseD (do_respectful propers).
  Proof using RTypeOk_typD Typ2Ok_Fun RSymOk_func RelDec_Correct_eq_typ Rbase_eq_ok.
    eapply do_prespectful_sound.
  Qed.

End setoid.
