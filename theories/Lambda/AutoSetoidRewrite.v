Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.AppN.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable Rbase : Type.
  Variable Req : Rbase -> Rbase -> bool.

  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R)
  | Rpointwise (t : typ) (r : R).

  Variable RbaseD : Rbase -> forall t : typ, option (relation (typD t)).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  Fixpoint RD (r : R) (t : typ) : option (relation (typD t)) :=
    match r with
      | Rinj r => RbaseD r t
      | Rrespects l r =>
        typ2_match (F:=Fun) (fun T => option (relation T)) t
                   (fun lt rt =>
                      match RD l lt , RD r rt with
                        | Some l , Some r => Some (respectful l r)
                        | _ , _ => None
                      end)
                   None
      | Rpointwise _t r =>
        typ2_match (F:=Fun) (fun T => option (relation T)) t
                   (fun lt rt =>
                      match type_cast t _t with
                        | Some _ =>
                          match RD r rt with
                            | Some r => Some (pointwise_relation (typD lt) r)
                            | _ => None
                          end
                        | None => None
                      end)
                   None
    end.

  Theorem RD_single_type
  : forall r t1 t2 rD1 rD2,
      RD r t1 = Some rD1 ->
      RD r t2 = Some rD2 ->
      t1 = t2.
  Proof.
    clear - RbaseD_single_type Typ2Ok_Fun.
    induction r; simpl; intros.
    { eapply RbaseD_single_type; eauto. }
    { arrow_case_any; try congruence.
      red in x1. subst.
      destruct (typ2_match_case t1); forward_reason.
      { rewrite H2 in H. clear H1 H2.
        red in x3. subst.
        simpl in *.
        autorewrite with eq_rw in *. forward.
        inv_all; subst. specialize (IHr1 _ _ _ _ H H0).
        specialize (IHr2 _ _ _ _ H2 H5). subst; reflexivity. }
      { rewrite H2 in *. congruence. } }
    { arrow_case_any; try congruence.
      destruct (typ2_match_case t1); forward_reason.
      { rewrite H2 in *.
        red in x1; red in x4. subst.
        clear H2 H1. simpl in *.
        autorewrite with eq_rw in *.
        forward. }
      { rewrite H2 in *. congruence. } }
  Qed.

  Definition mrw (T : Type) : Type :=
    option T.
  Definition rw_ret {T} (val : T) : mrw T :=
    Some val.
  Definition rw_bind {T U} (c : mrw T) (k : T -> mrw U) : mrw U :=
    match c with
      | None => None
      | Some v => k v
    end.
  Definition rw_orelse {T} (c1 c2 : mrw T) : mrw T :=
    match c1 with
      | None => c2
      | z => z
    end.
  Definition rw_fail {T} : mrw T := None.

  Section rw_map2.
    Context {T U V : Type}.
    Variable f : T -> U -> mrw V.

    Fixpoint rw_map2 (ts : list T) (us : list U) : mrw (list V) :=
      match ts , us with
        | nil , nil => rw_ret nil
        | t :: ts , u :: us =>
          rw_bind (f t u) (fun v =>
                             rw_bind (rw_map2 ts us)
                                     (fun vs => rw_ret (v :: vs)))
        | _ , _ => rw_fail
      end.
  End rw_map2.


  Let rewrite_expr :=
    forall (es : list (expr typ func * (R -> mrw (expr typ func))))
           (rg : R),
      mrw (expr typ func).

  Definition setoid_rewrite_spec (rw : _) : Prop :=
    forall tus tvs e e' r t eD rD,
      rw e r = Some e' ->
      RD r t = Some rD ->
      exprD' tus tvs t e = Some eD ->
      exists eD',
        exprD' tus tvs t e' = Some eD' /\
        forall us vs,
          rD (eD us vs) (eD' us vs).
  Definition respectful_spec (respectful : _) : Prop :=
    forall tus tvs e r rs t ts rD eD,
      respectful e r = Some rs ->
      RD r t = Some rD ->
      exprD' tus tvs (fold_right (typ2 (F:=Fun)) t ts) e = Some eD ->
      exists rD',
        RD (fold_right Rrespects r rs) (fold_right (typ2 (F:=Fun)) t ts) = Some rD' /\
        forall us vs,
          Proper rD' (eD us vs).

  Section setoid_rewrite.
    Variable respectfulness
    : expr typ func -> rewrite_expr.


    Fixpoint setoid_rewrite (e : expr typ func)
             (es : list (expr typ func * (R -> mrw (expr typ func)))) (rg : R)
    : mrw (expr typ func) :=
      match e with
        | App f x =>
          setoid_rewrite f ((x, setoid_rewrite x nil) :: es) rg
        | Abs t e' =>
          match es with
            | nil => match rg with
                       | Rpointwise _t (*=t*) rg' =>
                         rw_bind (setoid_rewrite e' nil rg')
                                 (fun e'' => rw_ret (Abs t e''))
                       | _ => respectfulness (Abs t e') es rg
                     end
            | _ => respectfulness (Abs t e') es rg
          end
        | Var v => respectfulness (Var v) es rg
        | UVar u => respectfulness (UVar u) es rg
        | Inj i => respectfulness (Inj i) es rg
      end.

    Definition setoid_rewrite_rec tus tvs (ls : list (expr typ func * (R -> mrw (expr typ func)))) : Prop :=
      Forall (fun e =>
                forall t eD,
                  exprD' tus tvs t (fst e) = Some eD ->
                  forall r e' rD,
                    snd e r = Some e' ->
                    RD r t = Some rD ->
                    exists eD',
                      exprD' tus tvs t e' = Some eD' /\
                      forall us vs,
                        rD (eD us vs) (eD' us vs)) ls.

    Hypothesis respectfulness_sound
    : forall e e' tus tvs t es rg rD eesD,
        respectfulness e es rg = Some e' ->
        RD rg t = Some rD ->
        exprD' tus tvs t (apps e (map fst es)) = Some eesD ->
        setoid_rewrite_rec tus tvs es ->
        exists eesD',
          exprD' tus tvs t e' = Some eesD' /\
          forall us vs,
            rD (eesD us vs) (eesD' us vs).

    Theorem setoid_rewrite_sound
    : forall e e' tus tvs t es rg rD eesD,
        setoid_rewrite e es rg = Some e' ->
        RD rg t = Some rD ->
        exprD' tus tvs t (apps e (map fst es)) = Some eesD ->
        setoid_rewrite_rec tus tvs es ->
        exists eesD',
          exprD' tus tvs t e' = Some eesD' /\
          forall us vs,
            rD (eesD us vs) (eesD' us vs).
    Proof.
      induction e; simpl; intros; eauto using respectfulness_sound.
      { (* App *)
        eapply IHe1 in H; eauto.
        constructor; eauto.
        simpl. intros. eapply IHe2; eauto. constructor. }
      { (* Abs *)
        destruct es; eauto.
        destruct rg; eauto.
        unfold rw_bind in H.
        consider (setoid_rewrite e nil rg).
        - intros. inversion H3; clear H3; subst.
          rewrite exprD'_apps in H1; eauto. simpl in H1.
          unfold apps_sem' in H1.
          simpl in H1.
          { consider (typeof_expr tus (t :: tvs) e); intros.
            - consider (exprD' tus tvs (typ2 t t2) (Abs t e)); intros.
              + consider (type_cast (typ2 t t2) t0); intros.
                * inv_all. subst.
                  revert H3.
                  autorewrite with exprD_rw. simpl.
                  destruct r.
                  repeat rewrite typ2_match_iota; eauto.
                  repeat rewrite type_cast_refl; eauto.
                  consider (exprD' tus (t :: tvs) t2 e); intros.
                  { autorewrite with eq_rw in H5.
                    inv_all; subst.
                    simpl in H0. rewrite typ2_match_iota in H0; eauto.
                    consider (type_cast (typ2 t t2) t1); intros.
                    - generalize dependent (typ2_cast t t2).
                      intro e1. autorewrite with eq_rw.
                      consider (RD rg t2); intros.
                      + inv_all; subst.
                        eapply IHe in H; eauto.
                        2: constructor.
                        forward_reason.
                        change_rewrite H.
                        eexists; split; eauto.
                        destruct r. unfold Rcast. simpl.
                        unfold relation. intros.
                        Require Import MirrorCore.Util.Compat.
                        autorewrite_with_eq_rw.
                        red. intros.
                        do 2 rewrite Eq.match_eq_sym_eq with (pf:=e1).
                        eapply H6.
                      + inversion H6.
                    - clear - H5. autorewrite with eq_rw in H5. inversion H5. }
                  { autorewrite with eq_rw in H5. inversion H5. }
                * inversion H5.
              + inversion H4.
            - inversion H3. }
        - inversion 2. }
    Qed.
  End setoid_rewrite.

  Section top_bottom.
    Context (reflexive transitive : R -> bool)
            (rw : expr typ func -> R -> option (expr typ func))
            (respectful : expr typ func -> R -> option (list R)).

    Hypothesis reflexiveOk
    : forall r t rD, reflexive r = true -> RD r t = Some rD -> Reflexive rD.
    Hypothesis transitiveOk
    : forall r t rD, transitive r = true -> RD r t = Some rD -> Transitive rD.

    Hypothesis rwOk : setoid_rewrite_spec rw.
    Hypothesis respectfulOk : respectful_spec respectful.

    Lemma exprD'_App
    : forall tus tvs td tr f x fD xD,
        exprD' tus tvs (typ2 (F:=Fun) td tr) f = Some fD ->
        exprD' tus tvs td x = Some xD ->
        exprD' tus tvs tr (App f x) = Some (AbsAppI.exprT_App fD xD).
    Proof.
      clear - Typ2Ok_Fun RSymOk_func RTypeOk_typD.
      intros.
      autorewrite with exprD_rw; simpl.
      erewrite exprD_typeof_Some by eauto.
      rewrite H. rewrite H0. reflexivity.
    Qed.
    Fixpoint apply_fold tus tvs t ts
             (es : HList.hlist (fun t => ExprI.exprT tus tvs (typD t)) ts)
    : ExprI.exprT tus tvs (typD (fold_right (typ2 (F:=Fun)) t ts))
      -> ExprI.exprT tus tvs (typD t) :=
      match es in HList.hlist _ ts
            return ExprI.exprT tus tvs (typD (fold_right (typ2 (F:=Fun)) t ts))
                   -> ExprI.exprT tus tvs (typD t)
      with
        | HList.Hnil => fun f => f
        | @HList.Hcons _ _ t' ts x xs => fun f =>
                                      @apply_fold tus tvs t ts xs (AbsAppI.exprT_App f x)
      end.
    Lemma apps_exprD'_fold_type
    : forall tus tvs es e t eD,
        exprD' tus tvs t (apps e es) = Some eD ->
        exists ts fD esD,
          exprD' tus tvs (fold_right (typ2 (F:=Fun)) t ts) e = Some fD /\
          hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                      (fun t e => exprD' tus tvs t e) ts es = Some esD /\
          forall us vs,
            eD us vs = @apply_fold _ _ _ _ esD fD us vs.
    Proof.
      clear - Typ2Ok_Fun RTypeOk_typD RSymOk_func.
      intros.
      rewrite exprD'_apps in H; eauto.
      unfold apps_sem' in H. forward. clear H.
      revert H0; revert H1; revert eD; revert t; revert e0; revert e.
      revert t0.
      induction es; simpl; intros.
      { exists nil. exists eD. exists HList.Hnil.
        simpl. split; eauto.
        forward. destruct r. inv_all; subst. assumption. }
      { arrow_case_any.
        { clear H.
          red in x1. subst.
          simpl in H1. autorewrite_with_eq_rw_in H1.
          forward; inv_all; subst.
          admit. (*
          eapply IHes with (e := App e a) in H1; eauto.
          { forward_reason.
            assert (x0 = fold_right (typ2 (F:=Fun)) t x1).
            { autorewrite with exprD_rw in H1; simpl in H1.
              forward; inv_all; subst.
              eapply exprD_typeof_Some in H0; eauto.
              eapply exprD_typeof_Some in H4; eauto.
              rewrite H0 in H4.
              inv_all. assumption. }
            { subst.
              eexists (x :: x1). exists e0.
              eexists. split; eauto.
              split. simpl.
              rewrite H2. rewrite H. reflexivity.
              simpl. intros.
              erewrite exprD'_App in H1; eauto.
              inv_all; subst. eauto. } }
          { erewrite exprD'_App; eauto.
            unfold exprT_App. autorewrite with eq_rw.
            reflexivity. } }
        { inversion H1. } } *)
    Admitted.

    Inductive Forall3 {T U V : Type} (P : T -> U -> V -> Prop)
    : list T -> list U -> list V -> Prop :=
    | Forall3_nil : Forall3 P nil nil nil
    | Forall3_cons : forall t u v ts us vs,
                       P t u v -> Forall3 P ts us vs ->
                       Forall3 P (t :: ts) (u :: us) (v :: vs).

    Theorem rw_map2_sound
    : forall T U V (f : T -> U -> mrw V) (P : T -> U -> V -> Prop) ts us vs,
        rw_map2 f ts us = Some vs ->
        (forall a b c, f a b = rw_ret c -> P a b c) ->
        Forall3 P ts us vs.
    Proof. clear. intros. revert H. revert vs; revert us.
           induction ts; destruct us; simpl in *;
           try solve [ inversion 1 ]; intros.
           { inversion H. constructor. }
           { specialize (H0 a u).
             destruct (f a u); [ simpl in H | inversion H ].
             specialize (IHts us).
             destruct (rw_map2 f ts us); inversion H.
             constructor; eauto. }
    Qed.

    Fixpoint recursive_rewrite (f : expr typ func)
             (es : list (expr typ func * (R -> mrw (expr typ func))))
             (rs : list R)
    : mrw (expr typ func) :=
      match es , rs with
        | nil , nil => rw_ret f
        | e :: es , r :: rs =>
          rw_bind ((snd e) r)
                  (fun e' => recursive_rewrite (App f e') es rs)
        | _ , _ => rw_fail
      end.

    Lemma rw_bind_assoc
    : forall {T U V} (c : mrw T) (k : T -> mrw U) (k' : U -> mrw V),
        rw_bind (rw_bind c k) k' =
        rw_bind c (fun x => rw_bind (k x) k').
    Proof. clear.
           destruct c; simpl; intros; auto.
    Qed.
    Lemma Proper_rw_bind (T U : Type)
    : Proper (@eq (mrw T) ==> (pointwise_relation T (@eq (mrw U))) ==> @eq (mrw U)) (@rw_bind T U).
    Proof.
      clear. compute. intros; subst.
      destruct y; auto.
    Qed.
    Lemma rw_bind_rw_ret
    : forall {T U} (x : T) (k : T -> mrw U),
        rw_bind (rw_ret x) k = k x.
    Proof. clear. reflexivity. Qed.

    Theorem recursive_rewrite_is_map2
    : forall f es rs,
        recursive_rewrite f es rs =
        rw_bind (rw_map2 (fun e r => snd e r) es rs)
                (fun es' => rw_ret (apps f es')).
    Proof.
      clear.
      intros f es; revert f.
      induction es; destruct rs; simpl; intros; auto.
      rewrite rw_bind_assoc.
      eapply Proper_rw_bind; auto.
      red; intros.
      rewrite IHes.
      rewrite rw_bind_assoc.
      eapply Proper_rw_bind; auto.
      red; intros.
      rewrite rw_bind_rw_ret. reflexivity.
    Qed.

    Inductive Forall2_hlist2 {T U : Type} (F : U -> Type)
              (P : T -> forall u : U,F u -> F u -> Prop)
    : list T -> forall us : list U, HList.hlist F us -> HList.hlist F us -> Prop :=
    | Forall2_hlist2_nil : Forall2_hlist2 P nil HList.Hnil HList.Hnil
    | Forall2_hlist2_cons : forall t u x y ts us xs ys,
                              P t u x y ->
                              Forall2_hlist2 P ts xs ys ->
                              @Forall2_hlist2 T U F P (t :: ts) (u :: us)
                                              (HList.Hcons x xs)
                                              (HList.Hcons y ys).

    Lemma rw_map2_for_rewrite_recursive
    : forall es rs es',
        rw_map2 (fun ef r => snd ef r) es rs = Some es' ->
        forall tus tvs ts esD,
          setoid_rewrite_rec tus tvs es ->
          Forall2 (fun t r => exists rD, RD r t = Some rD) ts rs ->
          hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                      (fun t e => exprD' tus tvs t (fst e)) ts es = Some esD ->
          exists esD',
            hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                        (fun t e => exprD' tus tvs t e) ts es' = Some esD' /\
            Forall2_hlist2 (fun r t (e e' : ExprI.exprT tus tvs (typD t)) =>
                              forall us vs rD,
                                RD r t = Some rD ->
                                rD (e us vs) (e' us vs)) rs esD esD'.
    Proof.
      induction es; destruct ts; destruct rs; simpl in *; intros;
      try solve [ inversion H | inversion H1 ].
      { inversion H2; subst. inversion H.
        eexists; split; eauto. constructor. }
      { unfold rw_bind in H.
        forwardy. inv_all; subst.
        inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        eapply IHes in H5; eauto.
        forward_reason.
        eapply H6 in H3; eauto.
        forward_reason.
        Cases.rewrite_all_goal.
        eexists; split; eauto.
        constructor; eauto.
        { intros. rewrite H1 in *. inv_all. subst. eauto. } }
    Qed.

    Theorem recursive_rewrite_sound
    : forall tus tvs t r rD',
        RD r t = Some rD' ->
        forall es f f' rs e',
        recursive_rewrite f' es rs = rw_ret e' ->
        forall ts fD rD eD fD'
               (Hrws : setoid_rewrite_rec tus tvs es),
          exprD' tus tvs t (apps f (map fst es)) = Some eD ->
          exprD' tus tvs (fold_right (typ2 (F:=Fun)) t ts) f = Some fD ->
          exprD' tus tvs (fold_right (typ2 (F:=Fun)) t ts) f' = Some fD' ->
          RD (fold_right Rrespects r rs) (fold_right (typ2 (F:=Fun)) t ts) = Some rD ->
          exists eD',
            exprD' tus tvs t e' = Some eD' /\
            forall us vs,
              rD (fD us vs) (fD' us vs) ->
              rD' (eD us vs) (eD' us vs).
    Proof. (*
      clear reflexiveOk transitiveOk rwOk respectfulOk.
      clear rw respectful reflexive transitive.
      induction es; destruct rs; simpl in *.
      { inversion 1; subst. clear H0.
        intros.
        match goal with
          | H : RD _ ?t = _ , H' : RD _ ?t' = _ |- _ =>
            let HH := fresh in
            (assert (HH : t = t')); [ | destruct HH ]
        end.
        { (* [R] has at most 1 type *)
          eapply (RD_single_type _ _ _ H H3). }
        revert H0. revert H3.
        Cases.rewrite_all_goal. intros; inv_all; subst.
        eexists; split; eauto. }
      { inversion 1. }
      { inversion 1. }
      { intros.
        consider (snd a r0); simpl; intros.
        { arrow_case_any.
          unfold Relim in H4; autorewrite with eq_rw in H4.
          forwardy; inv_all; subst.
          destruct ts.
          { (** False **)
            simpl in *. red in x1. subst.
            clear IHes. exfalso. clear H6.
            revert H9 H. clear - Typ2Ok_Fun RTypeOk_typD.
            (* [R] has at most 1 type *)
            assert ((TransitiveClosure.leftTrans (@tyAcc _ _)) x0 (typ2 x x0)).
            { constructor.
              eapply tyAcc_typ2R; eauto. }
            generalize dependent (typ2 x x0).
            clear - Typ2Ok_Fun RTypeOk_typD.
            revert r x0 y2.
            induction rs.
            { intros; simpl in *.
              specialize (RD_single_type _ _ _ H9 H0).
              intros; subst.
              eapply (@Facts.wf_anti_sym _ _ (wf_leftTrans (@wf_tyAcc typ _ _))) in H.
              assumption. }
            { intros; simpl in *.
              arrow_case_any.
              { red in x2. subst. simpl in *. clear H1.
                autorewrite with eq_rw in *.
                forward. inv_all; subst.
                eapply IHrs.
                2: eapply H2. 2: eassumption.
                eapply TransitiveClosure.LTStep.
                2: eassumption.
                eapply tyAcc_typ2R; eauto. }
              { congruence. } } }
          { simpl in x1. red in x1.
            generalize dependent x1.
            intro. generalize x1.
            inv_all; subst; intros.
            generalize H1.
            rewrite exprD'_apps in H1; eauto.
            unfold apps_sem' in H1.
            forwardy.
            generalize (exprD'_typeof_expr _ (or_introl H2)).
            simpl in H1. intro.
            rewrite H10 in H1. unfold type_of_apply in H1.
            forwardy. simpl in H11.
            rewrite typ2_match_iota in H11; eauto.
            autorewrite with eq_rw in H11. forwardy.
            inv_all; subst.
            autorewrite with exprD_rw in H7. simpl in H7.
            revert H7. Cases.rewrite_all_goal.
            destruct y4.
            change_rewrite H2. intro.
            forwardy. inv_all; subst.
            intro. inversion Hrws; clear Hrws; subst.
            specialize (H15 _ _ H7 _ _ _ H0 H4).
            forward_reason.
            eapply IHes in H5; [ | eauto | eauto | eauto using exprD'_App
                                 | eauto using exprD'_App
                                 | eauto ].
            forward_reason.
            eexists; split; eauto.
            clear - H14 H15 RelDec_Correct_eq_typ.
            intros us vs.
            unfold relation.
            autorewrite with eq_rw.
            unfold exprT_App in *.
            generalize dependent (typ2_cast x (fold_right (typ2 (F:=Fun)) t ts)).
            revert x1. revert y2.
            simpl in *.
            intros.
            rewrite (UIP_refl x1) in H; clear x1.
            generalize dependent (typD (typ2 x (fold_right (typ2 (F:=Fun)) t ts))).
            intros; subst.
            eapply H15; clear H15.
            eapply H. eauto. }
          { inversion H4. } }
        { inversion H5. } }
    Qed. *)
    Admitted.

    Definition bottom_up (e : expr typ func) (r : R) : option (expr typ func) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
	     match respectful e r with
	       | None => rw (apps e es) r
	       | Some rs =>
		 rw_bind (recursive_rewrite e efs rs)
			 (fun e' =>
                            if transitive r
                            then rw_orelse (rw e' r) (rw_ret e')
                            else rw_ret e')
	     end
	     (if reflexive r then rw_ret (apps e es) else rw_fail))
        e nil r.


    Lemma rw_orelse_sound : forall {T} (a b c : mrw T),
                              rw_orelse a b = c ->
                              (exists x, a = Some x /\ c = Some x) \/
                              (a = rw_fail /\ b = c).
    Proof. clear. intros. destruct a; eauto. Qed.

    Lemma bottom_up_sound_lem
    : forall e e' tus tvs t rg rD eD,
        bottom_up e rg = Some e' ->
        RD rg t = Some rD ->
        exprD' tus tvs t e = Some eD ->
        exists eD',
          exprD' tus tvs t e' = Some eD' /\
          forall us vs,
            rD (eD us vs) (eD' us vs).
    Proof.
      unfold bottom_up. intros.
      eapply setoid_rewrite_sound in H; eauto; try solve [ constructor ].
      intros.
      eapply rw_orelse_sound in H2; destruct H2; forward_reason.
      { inv_all; subst.
        consider (respectful e0 rg0); intros.
        { unfold rw_bind in H6.
          forwardy.
          generalize H4.
          eapply apps_exprD'_fold_type in H4.
          forward_reason.
          intro.
          eapply respectfulOk in H2; eauto.
          forward_reason.
          eapply recursive_rewrite_sound with (r := rg0) (rs := l) in H6;
            eauto.
          forward_reason.
          cut (   (Transitive rD0 /\ rw y rg0 = Some x)
                  \/ (x = y)).
          { clear H7. destruct 1.
            { destruct H7.
              red in rwOk.
              eapply rwOk in H13. 3: eauto.
              2: eauto.
              destruct H13 as [ ? [ ? ? ] ].
              eexists; split; eauto.
              intros. etransitivity. eapply H12.
              eapply H11. eauto. }
            { subst.
              eexists; split; eauto.
              intros. eapply H12; eauto. eapply H11. } }
          { consider (transitive rg0); intros.
            * destruct (rw y rg0).
              + left.
                eapply transitiveOk in H7; eauto.
              + right. inversion H13. reflexivity.
            * right. inversion H13. reflexivity. } }
        { eapply rwOk in H6; eauto. } }
      { clear H2.
        consider (reflexive rg0); intros.
        { eapply reflexiveOk in H2; eauto.
          inversion H6.
          eexists; split; eauto. }
        { inversion H6. } }
    Qed.

    Theorem bottom_up_sound
    : setoid_rewrite_spec bottom_up.
    Proof.
      red. intros.
      eapply bottom_up_sound_lem in H.
      2: eauto. 2: eauto.
      eauto.
    Qed.

(*
    Fixpoint top_down (f : nat) (e : expr typ func) (r : R) {struct f}
    : option (expr typ func) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
             (rw_bind (rw (apps e es) r)
                      (fun e' =>
                         if transitive r then
                           match f with
                             | 0 => rw_ret e'
                             | S f => top_down f e' r
                           end
                         else
                           rw_ret e'))
             match respectful e r with
	       | None => if reflexive r then rw_ret (apps e es) else rw_fail
	       | Some rs =>
	         rw_orelse
                   (recursive_rewrite e efs rs)
		            (fun e' => rw_ret (apps e es')))
                   (if reflexive r then rw_ret (apps e es) else rw_fail)
	     end)
        e nil r.
*)
  End top_bottom.

End setoid.

(*
Definition my_respectfulness (f : expr typ func)
           (es : list (expr typ func * (RG -> mrw (expr typ func))))
           (rg : RG)
: mrw (expr typ func) :=
  rw_ret (apps f (List.map (fun x => fst x) es)).


Definition my_respectfulness' (f : expr nat nat)
               (es : list (expr nat nat * (RG (typ:=nat) nat -> mrw (typ:=nat) nat (expr nat nat))))
               (rg : RG (typ:=nat) nat)
    : mrw (typ:=nat) nat (expr nat nat) :=
      rw_ret (apps f (List.map (fun x => snd x rg) es)).

  Fixpoint build_big (n : nat) : expr nat nat :=
    match n with
      | 0 => Inj 0
      | S n => App (build_big n) (build_big n)
    end.

  Time Eval vm_compute in
      match setoid_rewrite (Rbase:=nat) (@my_respectfulness nat nat nat) (build_big 24) nil (RGinj 0) (rsubst_empty _) with
        | Some e => true
        | None => false
      end.
*)