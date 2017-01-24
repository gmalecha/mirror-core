Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Polymorphic.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Set}.
  Context {func : Set}.
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

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable Rbase : Set.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Inductive R : Set :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R)
  | Rpointwise (t : typ) (r : R)
  | Rflip (r : R).

  Definition Rflip' (r : R) : R :=
    match r with
    | Rflip r => r
    | _ => Rflip r
    end.

  Fixpoint Rflip'' (r : R) : R :=
    match r with
    | Rflip r => r
    | Rinj e => Rflip (Rinj e)
    | Rrespects r1 r2 => Rrespects (Rflip'' r1) (Rflip'' r2)
    | Rpointwise t r => Rpointwise t (Rflip'' r)
    end.

  Fixpoint Req_dec (a b : R) : bool :=
    match a , b with
    | Rinj a , Rinj b => Rbase_eq a b
    | Rrespects l r , Rrespects l' r' =>
      if Req_dec l l' then Req_dec r r' else false
    | Rpointwise t a , Rpointwise t' a' =>
      if t ?[ eq ] t' then Req_dec a a' else false
    | Rflip a , Rflip b => Req_dec a b
    | _ , _ => false
    end.

  Theorem Req_dec_ok : forall x y : R, Req_dec x y = true -> x = y.
  Proof.
    clear - RTypeOk_typD Rbase_eq_ok RelDec_Correct_eq_typ.
    induction x; destruct y; simpl; try solve [ congruence ].
    { intros.
      eapply Rbase_eq_ok in H. destruct H; reflexivity. }
    { specialize (IHx1 y1).
      specialize (IHx2 y2).
      destruct (Req_dec x1 y1); intros; try congruence.
      destruct (Req_dec x2 y2); intros; try congruence.
      f_equal; tauto. }
    { consider (t ?[ eq ] t0); intros.
      { subst. f_equal; eauto. } }
    { intros. eapply IHx in H. f_equal. assumption. }
  Qed.

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  (** This is due to universe problems! **)
  Definition respectful :=
    fun (A B : Type) (R : A -> A -> Prop) (R' : B -> B -> Prop)
        (f g : A -> B) =>
      forall x y : A, R x y -> R' (f x) (g y).

  Definition pointwise_relation :=
    fun (A B : Type) (R : B -> B -> Prop) (f g : A -> B) =>
      forall a : A, R (f a) (g a).

  Definition flip (A : Type) (R : A -> A -> Prop) : A -> A -> Prop :=
    fun x y => R y x.

  Fixpoint RD (r : R) (t : typ) : option (typD t -> typD t -> Prop) :=
    match r with
      | Rinj r => RbaseD r t
      | Rrespects l r =>
        typ2_match (F:=RFun) (fun T => option (T -> T -> Prop)) t
                   (fun lt rt =>
                      match RD l lt , RD r rt with
                        | Some l , Some r => Some (respectful l r)
                        | _ , _ => None
                      end)
                   None
      | Rpointwise _t r =>
        typ2_match (F:=RFun) (fun T => option (T -> T -> Prop)) t
                   (fun lt rt =>
                      match type_cast lt _t with
                        | Some _ =>
                          match RD r rt with
                            | Some r => Some (pointwise_relation (A:=typD lt) r)
                            | _ => None
                          end
                        | None => None
                      end)
                   None
      | Rflip r =>
        match RD r t with
        | Some rD => Some (flip rD)
        | None => None
        end
    end.

  Theorem RD_single_type
  : forall r t1 t2 rD1 rD2,
      RD r t1 = Some rD1 ->
      RD r t2 = Some rD2 ->
      t1 = t2.
  Proof using tyArr RbaseD_single_type Typ2Ok_Fun.
    induction r; simpl; intros.
    { eapply RbaseD_single_type; eauto. }
    { destruct (typ2_match_case t2) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
        rewrite H1 in *; [ clear H1 | congruence ].
      destruct (typ2_match_case t1) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
        rewrite H1 in *; [ clear H1 | congruence ].
      revert H; revert H0.
      red in x4; red in x1; subst.
      simpl.
      autorewrite_with_eq_rw.
      intros; forwardy; inv_all; subst.
      f_equal; eauto. }
    { destruct (typ2_match_case t2) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
        rewrite H1 in *; [ clear H1 | congruence ].
      destruct (typ2_match_case t1) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
        rewrite H1 in *; [ clear H1 | congruence ].
      revert H; revert H0.
      red in x4; red in x1; subst.
      simpl.
      autorewrite_with_eq_rw.
      intros; forwardy; inv_all; subst.
      red in y0, y3; subst.
      f_equal; eauto. }
    { forwardy.
      inv_all. subst. eauto. }
  Qed.

  (** Patterns *)
  Definition ptrnRinj {T : Type} (p : ptrn Rbase T) : ptrn R T :=
    fun r _T good bad =>
      match r with
      | Rinj a => p a _T good (fun x => bad (Rinj x))
      | Rrespects a b => bad (Rrespects a b)
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => bad (Rflip a)
      end.

  Global Instance ptrn_ok_ptrnRinj {T} p : ptrn_ok p -> ptrn_ok (@ptrnRinj T p).
  Proof using.
    unfold ptrnRinj; red; intros.
    destruct x; simpl; try solve [ right; red; eauto ].
    destruct (H r).
    { left; destruct H0. exists x. red. eauto. }
    { right. red. red in H0. intros.
      setoid_rewrite H0. reflexivity. }
  Qed.

  Theorem Succeeds_ptrnRinj {T} p x res
  : ptrn_ok p ->
    Succeeds x (@ptrnRinj T p) res ->
    exists y, Succeeds y p res /\ x = Rinj y.
  Proof using.
    destruct x; unfold Succeeds; simpl; intros;
    try solve [ ptrn_contradict ].
    eexists; split; eauto.
    intros.
    destruct (H r) as [ [ ? ? ] | ? ].
    { red in H1. setoid_rewrite H1 in H0. setoid_rewrite H1. eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      ptrn_contradict. }
  Qed.

  Global Instance SucceedsE_ptrnRinj {T} p x res
  : ptrn_ok p -> SucceedsE x (@ptrnRinj T p) res :=
  { s_result := exists y, Succeeds y p res /\ x = Rinj y }.
  intros.  eauto using Succeeds_ptrnRinj.
  Defined.

  Definition ptrnRflip {T : Type} (p : ptrn R T)
  : ptrn R T :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rrespects a b => bad (Rrespects a b)
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => p a _T good (fun x => bad (Rflip x))
      end.

  Global Instance ptrn_ok_ptrnRflip {T} p : ptrn_ok p -> ptrn_ok (@ptrnRflip T p).
  Proof using.
    unfold ptrnRflip; red; intros.
    destruct x; simpl; try solve [ right; red; eauto ].
    destruct (H x).
    { left; destruct H0. exists x0. red. eauto. }
    { right. red. red in H0. intros.
      setoid_rewrite H0. reflexivity. }
  Qed.

  Theorem Succeeds_ptrnRflip {T} p x res
  : ptrn_ok p ->
    Succeeds x (@ptrnRflip T p) res ->
    exists y, Succeeds y p res /\ x = Rflip y.
  Proof using.
    destruct x; unfold Succeeds; simpl; intros;
    try solve [ ptrn_contradict ].
    eexists; split; eauto.
    intros.
    destruct (H x) as [ [ ? ? ] | ? ].
    { red in H1. setoid_rewrite H1 in H0. setoid_rewrite H1. eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      ptrn_contradict. }
  Qed.

  Global Instance SucceedsE_ptrnRflip {T} p x res
  : ptrn_ok p -> SucceedsE x (@ptrnRflip T p) res :=
  { s_result := exists y, Succeeds y p res /\ x = Rflip y }.
  intros.  eauto using Succeeds_ptrnRflip.
  Defined.

  Definition ptrnRrespectsL {T U : Type}
             (pd : ptrn R (T -> U))
             (pr : ptrn R T)
  : ptrn R U :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rrespects a b => pr b _T (fun x => pd a _T (fun y => good (y x))
                                              (fun a => bad (Rrespects a b)))
                            (fun b => bad (Rrespects a b))
      | Rpointwise a b => bad (Rpointwise a b)
      | Rflip a => bad (Rflip a)
      end.

  Global Instance ptrn_ok_ptrnRrespectsL {T U} pl pr
  : ptrn_ok pl -> ptrn_ok pr -> ptrn_ok (@ptrnRrespectsL T U pl pr).
  Proof using.
    unfold ptrnRrespectsL; red; intros.
    destruct x; simpl; try solve [ right; red; eauto ].
    destruct (H x1); destruct (H0 x2).
    { forward_reason. left.
      unfold Succeeds in *. exists (x0 x). intros.
      setoid_rewrite H2. setoid_rewrite H1. reflexivity. }
    { right. red. red in H2.
      setoid_rewrite H2. eauto. }
    { right. destruct H2. red in H1, H2.
      red. setoid_rewrite H2. setoid_rewrite H1. eauto. }
    { right. red in H1, H2.
      red. setoid_rewrite H2. eauto. }
  Qed.

  Theorem Succeeds_ptrnRrespectsL {T U} pl pr x res
  : ptrn_ok pl -> ptrn_ok pr ->
    Succeeds x (@ptrnRrespectsL T U pl pr) res ->
    exists y z resL resR, Succeeds y pl resL /\ Succeeds z pr resR /\
                          x = Rrespects y z /\ res = resL resR.
  Proof using.
    destruct x; unfold Succeeds; simpl; intros;
    try solve [ ptrn_contradict ].
    exists x1; exists x2.
    destruct (H0 x2).
    { destruct H2; red in H2. setoid_rewrite H2 in H1.
      destruct (H x1).
      { destruct H3; red in H3; setoid_rewrite H3 in H1.
        do 2 eexists. split; eauto. split; eauto.
        split; eauto.
        specialize (H1 _ (fun x => x) (fun _ => res)).
        symmetry; assumption. }
      { red in H3. setoid_rewrite H3 in H1.
        ptrn_contradict. } }
    { red in H2. setoid_rewrite H2 in H1. ptrn_contradict. }
  Qed.

  Global Instance SucceedsE_ptrnRrespectsL {T U} pl pr x res
  : ptrn_ok pl -> ptrn_ok pr -> SucceedsE x (@ptrnRrespectsL T U pl pr) res :=
  { s_result := exists y z resL resR, Succeeds y pl resL /\ Succeeds z pr resR /\
                          x = Rrespects y z /\ res = resL resR }.
  intros.  eauto using Succeeds_ptrnRrespectsL.
  Defined.

  Definition ptrnRpointwiseL {T U : Type}
             (pd : ptrn typ (T -> U))
             (pr : ptrn R T)
  : ptrn R U :=
    fun r _T good bad =>
      match r with
      | Rinj a => bad (Rinj a)
      | Rpointwise a b => pr b _T (fun x => pd a _T (fun y => good (y x))
                                              (fun a => bad (Rpointwise a b)))
                            (fun b => bad (Rpointwise a b))
      | Rrespects a b => bad (Rrespects a b)
      | Rflip a => bad (Rflip a)
      end.

  Global Instance ptrn_ok_ptrnRpointwiseL {T U} pl pr
  : ptrn_ok pl -> ptrn_ok pr -> ptrn_ok (@ptrnRpointwiseL T U pl pr).
  Proof using.
    unfold ptrnRpointwiseL; red; intros.
    destruct x; simpl; try solve [ right; red; eauto ].
    destruct (H t); destruct (H0 x).
    { forward_reason. left.
      unfold Succeeds in *. setoid_rewrite H2.
      setoid_rewrite H1. eauto. }
    { right. red. red in H2.
      setoid_rewrite H2. eauto. }
    { right. destruct H2. red in H1, H2.
      red. setoid_rewrite H2. setoid_rewrite H1. eauto. }
    { right. red in H1, H2.
      red. setoid_rewrite H2. eauto. }
  Qed.

  Theorem Succeeds_ptrnRpointwiseL {T U} pl pr x res
  : ptrn_ok pl -> ptrn_ok pr ->
    Succeeds x (@ptrnRpointwiseL T U pl pr) res ->
    exists y z resL resR, Succeeds y pl resL /\ Succeeds z pr resR /\
                          x = Rpointwise y z /\ res = resL resR.
  Proof using.
    destruct x; unfold Succeeds; simpl; intros;
    try solve [ ptrn_contradict ].
    exists t; exists x.
    destruct (H0 x).
    { destruct H2; red in H2. setoid_rewrite H2 in H1.
      destruct (H t).
      { destruct H3; red in H3; setoid_rewrite H3 in H1.
        do 2 eexists. split; eauto. split; eauto.
        split; eauto.
        specialize (H1 _ (fun x => x) (fun _ => res)).
        symmetry; assumption. }
      { red in H3. setoid_rewrite H3 in H1.
        ptrn_contradict. } }
    { red in H2. setoid_rewrite H2 in H1. ptrn_contradict. }
  Qed.

  Global Instance SucceedsE_ptrnRpointwiseL {T U} pl pr x res
  : ptrn_ok pl -> ptrn_ok pr -> SucceedsE x (@ptrnRpointwiseL T U pl pr) res :=
  { s_result := exists y z resL resR, Succeeds y pl resL /\ Succeeds z pr resR /\
                          x = Rpointwise y z /\ res = resL resR }.
  intros.  eauto using Succeeds_ptrnRpointwiseL.
  Defined.

  Section refl_trans_types.
    Context {T} (RD : T -> forall t : typ, option (typD t -> typD t -> Prop)).

    Definition refl_dec : Type := T -> bool.
    Definition trans_dec : Type := T -> bool.
    Definition refl_dec_ok (rd : refl_dec) : Prop :=
      forall r t rD, rd r = true -> RD r t = Some rD -> Reflexive rD.
    Definition trans_dec_ok (rd : trans_dec) : Prop :=
      forall r t rD, rd r = true -> RD r t = Some rD -> Transitive rD.
  End refl_trans_types.

  Arguments refl_dec _ : clear implicits.
  Arguments trans_dec _ : clear implicits.

  (** Reflexivity and transitivity *)
  Section is_refl.
    Lemma Refl_pointwise : forall {T U : Type} (R : T -> T -> Prop),
      Reflexive R -> Reflexive (pointwise_relation (A:=U) R).
    Proof using.
      compute. auto.
    Qed.

    Variable is_refl : refl_dec Rbase.
    Definition is_reflR : refl_dec R :=
      fix is_reflR (r : R) : bool :=
        match r with
        | Rinj r => is_refl r
        | Rpointwise _ x => is_reflR x
        | Rflip r => is_reflR r
        | _ => false
        end.

    Hypothesis is_reflOk : refl_dec_ok RbaseD is_refl.

    Theorem is_reflROk : refl_dec_ok RD is_reflR.
    Proof using Typ2Ok_Fun is_reflOk.
      red.
      induction r; simpl; intros; eauto; try congruence.
      { simpl. intros.
        destruct (typ2_match_case t0) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
          rewrite H1 in *; [ clear H1 | congruence ].
        revert H0.
        red in x1; subst; simpl.
        autorewrite_with_eq_rw.
        intros. forwardy; inv_all; subst.
        eapply IHr in H; [ | eassumption ].
        red.
        intro. autorewrite_with_eq_rw.
        eapply Refl_pointwise. eassumption. }
      { forwardy; inv_all; subst.
        red. intros. unfold flip. eapply IHr; eauto. }
    Qed.
  End is_refl.

  Section is_trans.
    Lemma Trans_pointwise : forall {T U : Type} (R : T -> T -> Prop),
        Transitive R -> Transitive (pointwise_relation (A:=U) R).
    Proof using.
      compute. eauto.
    Qed.

    Variable is_trans : trans_dec Rbase.
    Definition is_transR : trans_dec R :=
      fix is_transR (r : R) : bool :=
        match r with
        | Rinj r => is_trans r
        | Rpointwise _ x => is_transR x
        | Rflip r => is_transR r
        | _ => false
        end.

    Hypothesis is_transOk : trans_dec_ok RbaseD is_trans.

    Theorem is_transROk : trans_dec_ok RD is_transR.
    Proof using Typ2Ok_Fun is_transOk.
      red.
      induction r; simpl; intros; eauto; try congruence.
      { simpl. intros.
        destruct (typ2_match_case t0) as [ [ ? [ ? [ ? H1 ] ] ] | H1 ];
          rewrite H1 in *; [ clear H1 | congruence ].
        revert H0.
        red in x1; subst; simpl.
        autorewrite_with_eq_rw.
        intros. forwardy; inv_all; subst.
        eapply IHr in H; [ | eassumption ].
        red.
        do 3 intro. autorewrite_with_eq_rw.
        eapply Trans_pointwise. eassumption. }
      { forwardy; inv_all; subst.
        red. intros. unfold flip. eapply IHr; eauto. }
    Qed.
  End is_trans.

  (** Rewriting Lemmas **)
  Section lemmas.
    (** Note: This could be parameterized by the type of expressions
     **)
    Existing Instance Expr_expr.

    Record rw_concl : Type :=
    { lhs : expr typ func
    ; rel : R
    ; rhs : expr typ func }.

    Definition rw_lemma : Set :=
      Lemma.lemma typ (expr typ func) rw_concl.

    Definition rw_conclD (tus tvs : tenv typ) (c : rw_concl)
    : option (exprT tus tvs Prop) :=
      match typeof_expr tus tvs c.(lhs) with
      | None => None
      | Some t =>
        match lambda_exprD tus tvs t c.(lhs)
            , lambda_exprD tus tvs t c.(rhs)
            , RD c.(rel) t
        with
        | Some lhs , Some rhs , Some rel =>
          Some (fun us vs => rel (lhs us vs) (rhs us vs))
        | _ , _ , _ => None
        end
      end.

    Lemma rw_concl_weaken
    : forall (tus tvs : tenv typ) (l : rw_concl) (lD : exprT tus tvs Prop),
        rw_conclD tus tvs l = Some lD ->
        forall tus' tvs' : list typ,
        exists lD' : exprT (tus ++ tus') (tvs ++ tvs') Prop,
          rw_conclD (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          (forall (us : hlist typD tus) (us' : hlist typD tus')
                  (vs : hlist typD tvs) (vs' : hlist typD tvs'),
              lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs')).
    Proof.
      unfold rw_conclD. simpl. intros.
      forwardy. inv_all. subst.
      erewrite ExprFacts.typeof_expr_weaken by eauto.
      eapply ExprFacts.lambda_exprD_weaken in H0; eauto.
      destruct H0 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      eapply ExprFacts.lambda_exprD_weaken in H1; eauto.
      destruct H1 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      rewrite H2. eexists; split; eauto.
      intros. simpl. rewrite <- H0. rewrite <- H1. reflexivity.
    Qed.


    Definition flip_rw_concl (a : rw_concl) : rw_concl :=
    {| lhs := a.(rhs)
     ; rel := Rflip' a.(rel)
     ; rhs := a.(lhs)
     |}.

    Definition flip_rw_lemma (lem : rw_lemma) : rw_lemma :=
    {| vars := lem.(vars)
     ; premises := lem.(premises)
     ; concl := flip_rw_concl lem.(concl) |}.

    Lemma RD_Rflip'_Rflip : forall a b,
        RD (Rflip' a) b = RD (Rflip a) b.
    Proof.
      destruct a; simpl; eauto.
      intros. destruct (RD a b); reflexivity.
    Qed.

    Theorem flip_rw_lemma_sound
    : forall (lem : rw_lemma),
        lemmaD rw_conclD nil nil lem ->
        lemmaD rw_conclD nil nil (flip_rw_lemma lem).
    Proof using RTypeOk_typD Typ2Ok_Fun RSymOk_func.
      unfold lemmaD, lemmaD'. simpl.
      intros. forwardy.
      Cases.rewrite_all_goal.
      destruct (concl lem); simpl in *.
      unfold flip_rw_concl. simpl.
      unfold rw_conclD in *. simpl in *.
      forwardy.
      erewrite lambda_exprD_typeof_Some; eauto.
      Cases.rewrite_all_goal.
      rewrite RD_Rflip'_Rflip.
      simpl.
      Cases.rewrite_all_goal.
      inv_all.
      subst. unfold flip. eauto.
    Qed.

  End lemmas.

  Section poly_rewrite.

    Definition ptc_rel_lem_typ x ignores :=
      polymorphic typ x (tc_lemma typ (expr typ func) rw_concl ignores).

  End poly_rewrite.

End setoid.

Arguments ptc_rel_lem_typ : clear implicits.
Arguments rw_concl typ func Rbase : rename, clear implicits.
Arguments rw_lemma typ func Rbase : rename, clear implicits.
Arguments R typ Rbase : rename, clear implicits.
Arguments Rrespects {_ _} _ _.
Arguments Rpointwise {_ _} _ _.
Arguments Rflip {_ _} _.
Arguments Rinj {_ _} _.
Arguments refl_dec _ : clear implicits.
Arguments trans_dec _ : clear implicits.

Require Import MirrorCore.Reify.ReifyClass.

Section reify_R.
  Variables Ty Rbase : Set.
  Context {Reify_Ty : Reify Ty}.
  Context {Reify_Rbase : Reify Rbase}.

(*
  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).
*)

  Set Printing Universes.

  Definition reify_R : Command (R Ty Rbase) :=
    CFix
      (CFirst (   CPattern (ls:=_::_::nil)
                           (RApp (RApp (RApp (RApp (RExact (@Morphisms.respectful)) RIgnore) RIgnore) (RGet 0 RIgnore)) (RGet 1 RIgnore))
                           (fun a b : function (CRec 0) => Rrespects (typ:=Ty) (Rbase:=Rbase) a b)
               :: CPattern (ls:=_::_::nil)
                           (RApp (RApp (RApp (RExact (@Morphisms.pointwise_relation)) (RGet 0 RIgnore)) RIgnore) (RGet 1 RIgnore))
                           (fun (a : function@{Set} (CCall (reify_scheme Ty))) (b : function (CRec 0)) =>
                              Rpointwise a b)
               :: CPattern (ls:=_::nil)
                           (RApp (RApp (RApp (RApp (RExact (@Basics.flip)) RIgnore) RIgnore) RIgnore) (RGet 0 RIgnore))
                           (fun a : function (CRec 0) => Rflip a)
               :: CMap (@Rinj Ty _) (reify_scheme Rbase)
               :: nil)).

  Global Instance Reify_R : Reify (R Ty Rbase) :=
  { reify_scheme := CCall reify_R }.
End reify_R.

Section Reify_Proper_concl.
  Variables Ty func Rbase : Set.
  Context {Reify_Ty : Reify Ty}.
  Context {Reify_expr_typ_func : Reify (expr Ty func)}.
  Context {Reify_Rbase : Reify Rbase}.

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  Definition reify_rw_concl :=
    CPattern (ls:=_::_::_::nil)
             (?0 @ ?1 @ ?2)
             (fun (a : function (reify_scheme (R Ty Rbase))) (b c : function (CCall (reify_scheme (expr Ty func)))) =>
                @Build_rw_concl Ty func Rbase b a c).

  Global Instance Reify_rw_concl : Reify (rw_concl Ty func Rbase) :=
  { reify_scheme := CCall reify_rw_concl }.

End Reify_Proper_concl.
