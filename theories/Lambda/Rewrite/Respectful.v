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

  Definition Proper_lemma := Lemma.lemma typ (expr typ func) Proper_concl.

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

  Definition apply_respectful (lem : Proper_lemma)
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

  Theorem apply_respectful_sound : forall lem tacK,
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
      destruct (ExprFacts.lambda_exprD_weaken _ _ _ (getUVars ctx) (tvs'++getVars ctx) H8) as [ ? [ ? ? ] ].
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

  Definition apply_prespectful {T : Type}
             (get : expr typ func -> R -> option T)
             (lem : T -> Proper_lemma) (tacK : rtacK _ _)
    : respectful_dec _ _ _ :=
    fun e r =>
      match get e r with
      | Some t => apply_respectful (lem t) tacK e r
      | _ => rw_fail
      end.

  Theorem apply_prespectful_sound : forall {T} get (lem : T -> _) (tacK : _),
      (forall e r x,
          get e r = Some x ->
          forall tus tvs t eD,
            lambda_exprD tus tvs t e = Some eD ->
            Lemma.lemmaD Proper_conclD nil nil (lem x)) ->
      rtacK_sound tacK ->
      respectful_spec RbaseD (apply_prespectful get lem tacK).
  Proof using RSymOk_func RTypeOk_typD Rbase_eq_ok RelDec_Correct_eq_typ
        Typ2Ok_Fun.
    intros. unfold apply_prespectful.
    red. intros.
    destruct (get e r) eqn:?; try solve [ inversion H1 ].
    (** above *)
    unfold apply_respectful in H1.
    destruct (split_R t.(lem).(concl).(relation)) eqn:?.
    eapply split_R_sound in Heqp.
    destruct (t.(lem).(vars)) eqn:Hvars; [ | inversion H1 ].
    destruct (t.(lem).(premises)) eqn:Hprems; [ | inversion H1 ].
    generalize (expr_sdec_sound e t.(lem).(concl).(term)).
    destruct (expr_sdec e t.(lem).(concl).(term)); [ | inversion H1 ].
    generalize (Req_dec_ok _ Rbase_eq_ok r r0).
    destruct (Req_dec Rbase_eq r r0); [ | inversion H1 ].
    intro X; specialize (X eq_refl); subst.
    intro X; specialize (X eq_refl); subst.
    inversion H1; clear H1; subst.
    split; auto.
    intros.
    forward.
    eapply H in Heqo; [ | eapply H4 ].
    rename Heqo into Hlem.
    red in Hlem.
    simpl in Hlem.
    red in Hlem. rewrite Hprems in *. rewrite Hvars in *.
    simpl in Hlem. red in Hlem.
    revert Hlem.
    forward. inv_all. subst.
    destruct (ExprFacts.lambda_exprD_weaken _ _ _ (getUVars ctx) (tvs'++getVars ctx) H8) as [ ? [ ? ? ] ].
    simpl in H.
    generalize (@lambda_exprD_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H6 H4).
    intro. red in H10. revert Hlem. subst.
    simpl in *.
    rewrite Heqp in *.
    rewrite H7 in *.
    rewrite H4 in *.
    inv_all. subst.
    intros.
    intros; split; [ reflexivity | ].
    intros. eapply Pure_pctxD; eauto.
    intros. red.
    rewrite (H9 Hnil Hnil us0 (hlist_app vs' vs0)) in Hlem.
    eapply Hlem.
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

  Fixpoint do_respectful (propers : list (expr typ func * R))
  : respectful_dec _ _ _ :=
    match propers with
    | nil => fail_respectful
    | (f,rel) :: propers =>
      or_respectful
        (apply_respectful {| vars := nil
                           ; premises := nil
                           ; concl := {| relation := rel
                                       ; term := f |}
                           |} IDTACK)
        (fun x => do_respectful propers x)
    end.

  Theorem do_respectful_sound
    : forall propers,
      Forall (fun er =>
                let '(e,r) := er in
                match typeof_expr nil nil e with
                | None => False
                | Some t =>
                  match RD RbaseD r t
                        , lambda_exprD nil nil t e
                  with
                  | Some rD , Some eD =>
                    Proper rD (eD Hnil Hnil)
                  | _ , _ => False
                  end
                end) propers ->
      respectful_spec RbaseD (do_respectful propers).
  Proof using RTypeOk_typD Typ2Ok_Fun RSymOk_func RelDec_Correct_eq_typ Rbase_eq_ok.
    induction 1.
    { eapply fail_respectful_sound. }
    { simpl. destruct x. eapply or_respectful_sound.
      { apply apply_respectful_sound.
        { clear - H.
          red. simpl. unfold lemmaD'. simpl.
          unfold Proper_conclD. simpl.
          forward. }
        { apply IDTACK_sound. } }
      { eauto. } }
  Qed.

End setoid.
