(** This file contains generic functions for manipulating,
 ** (i.e. substituting and finding) unification variables
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

Require Import FunctionalExtensionality.

Section substU.
  Variable func : Type.
  Variable u : uvar.
  Variable e' : expr func.

  (** This replaces [UVar under] with [e] doing the appropriate
   ** lifing.
   **)
  Fixpoint substU (under : nat) (e : expr func) : expr func :=
    match e with
      | Var _ => e
      | Inj _ => e
      | App l r => App (substU under l) (substU under r)
      | Abs t e => Abs t (substU (S under) e)
      | UVar u' =>
        if u ?[ eq ] u' then
          lift 0 under e'
        else UVar u'
    end.
End substU.

Section instantiate.
  Variable ts : types.
  Variable func : Type.
  Let RType_typ := RType_typ ts.
  Local Existing Instance RType_typ.
  Variable RSym_func : RSym func.
  Variable lookup : uvar -> option (expr func).

  Let Expr_expr : Expr _ (expr func) := Expr_expr _.
  Local Existing Instance Expr_expr.

  Local Hint Immediate RSym_func : typeclass_instances.

  Fixpoint instantiate (under : nat) (e : expr func) : expr func :=
    match e with
      | Var _
      | Inj _ => e
      | App l r => App (instantiate under l) (instantiate under r)
      | Abs t e => Abs t (instantiate (S under) e)
      | UVar u =>
        match lookup u with
          | None => UVar u
          | Some e => lift 0 under e
        end
    end.

  Theorem typeof_expr_instantiate : forall tu tg,
    (forall u e',
       lookup u = Some e' ->
       exists t',
         nth_error tu u = Some t' /\
         typeof_expr tu tg e' = Some t') ->
    forall e tg',
      typeof_expr tu (tg' ++ tg) (instantiate (length tg') e) =
      typeof_expr tu (tg' ++ tg) e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ =>
               rewrite H
           end; auto.
    { specialize (IHe (t :: tg')). simpl in *.
      rewrite IHe. reflexivity. }
    { consider (lookup u); intros; simpl; auto.
      specialize (H _ _ H0). destruct H.
      intuition.
      generalize (typeof_expr_lift _ tu nil tg' tg e); simpl.
      congruence. }
  Qed.

  Theorem exprD'_instantiate : forall us gs',
    (forall u e',
       lookup u = Some e' ->
       exists tval,
         nth_error us u = Some tval /\
         exprD us gs' e' (projT1 tval) = Some (projT2 tval)) ->
    forall e t v,
      let (tv',vs') := EnvI.split_env gs' in
      let (tu',us') := EnvI.split_env us in
      match ExprD.exprD' tu' (v ++ tv') e t,
            ExprD.exprD' tu' (v ++ tv') (instantiate (length v) e) t
      with
        | Some l , Some r => forall vs,
                               l us' (hlist_app vs vs') = r us' (hlist_app vs vs')
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    unfold exprD. intros us gs'.
    consider (split_env us). intros x h Hsplit_env.
    destruct (split_env gs'). intros Hlookup.
    Opaque exprD'.
    induction e; simpl; intros; autorewrite with exprD_rw; auto.
    { forward. }
    { forward. }
    { rewrite typeof_expr_instantiate.
      { consider (typeof_expr x (v ++ x0) e1); auto.
        destruct t0; auto.
        specialize (IHe1 (tyArr t0_1 t0_2) v).
        specialize (IHe2 t0_1 v).
        repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; auto.
        simpl in *.
        inv_all; subst. simpl in *.
        rewrite IHe2. rewrite IHe1. reflexivity. }
      { clear - Hlookup Hsplit_env.
        intros. specialize (Hlookup _ _ H).
        destruct Hlookup. intuition.
        unfold ExprI.exprD' in H2. simpl in H2.
        forward; inv_all; subst.
        exists (projT1 x1).
        apply split_env_nth_error in H1.
        rewrite Hsplit_env in *. simpl in *.
        generalize dependent (hlist_nth h u).
        forward. subst; simpl.
        split; eauto. simpl in *.
        consider (ExprD.exprD' x x0 e' t0); try congruence; intros.
        eapply ExprD.typeof_expr_exprD'. eauto. } }
    { destruct t0; auto.
      specialize (IHe t0_2 (t :: v)). simpl in *.
      repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto.
      eapply functional_extensionality. intros.
      specialize (IHe (Hcons x1 vs)). simpl in *; auto. }
    { specialize (Hlookup u).
      destruct (lookup u).
      { specialize (Hlookup _ eq_refl).
        forward_reason.
        forward. inv_all; subst.
        rewrite exprD'_type_cast.
        generalize (exprD'_lift _ x nil v x0 e (projT1 x1)).
        simpl. simpl in H0. rewrite H0.
        forward.
        erewrite ExprD3.EXPR_DENOTE_core.exprD'_typeof by eauto.
        rewrite H2.
        match goal with
          | |- match match ?X with _ => _ end with _ => _ end =>
            consider X; intros; forward
        end.
        { eapply EnvI.nth_error_get_hlist_nth_Some in H5.
          forward_reason. simpl in *. subst.
          apply split_env_nth_error in H.
          rewrite Hsplit_env in *. simpl in *.
          specialize (H5 h).
          match goal with
            | H : _ = match _ with eq_refl => ?X end , H' : _ ?Y |- _ =>
              change X with Y in H ; generalize dependent Y
          end.
          rewrite x3. intros; subst; simpl in *.
          match goal with
            | |- match match ?x with _ => _ end with Some _ => match match ?y with _ => _ end with _ => _ end | _ => _ end =>
              change y with x ; consider x
          end; auto.
          intros.
          f_equal. specialize (H3 h Hnil). simpl in *.
          rewrite H3. auto. }
        { inv_all; subst.
          eapply EnvI.nth_error_get_hlist_nth_None in H4.
          clear - H H4 Hsplit_env.
          apply split_env_nth_error in H.
          rewrite Hsplit_env in *. simpl in *.
          generalize dependent (hlist_nth h u).
          rewrite H4. auto. } }
      { clear Hlookup.
        autorewrite with exprD_rw.
        forward. } }
  Qed.

  Lemma typeof_expr_instantiate_Some
  : forall (*lookup : uvar -> option (expr func)*) (tu : list typ)
           (tg : tenv typ),
      (forall (u : uvar) (e' : expr func) t',
         lookup u = Some e' ->
         nth_error tu u = Some t' ->
         typeof_expr tu tg e' = Some t') ->
      forall (e : expr func) (tg' : list typ) t,
        typeof_expr tu (tg' ++ tg) e = Some t ->
        typeof_expr tu (tg' ++ tg) (instantiate (length tg') e) = Some t.
  Proof.
    clear. induction e; simpl; intros; auto; forward.
    { eapply IHe1 in H0. eapply IHe2 in H1.
      Cases.rewrite_all_goal. reflexivity. }
    { inv_all; subst.
      eapply (IHe (t :: tg')) in H0.
      simpl in H0. rewrite H0. reflexivity. }
    { eapply H in H1; eauto.
      generalize (@typeof_expr_lift _ _ RSym_func tu nil tg' tg e).
      simpl. congruence. }
  Qed.

  Lemma exprD'_instantiate_Some
  : forall tus tvs P,
      (forall u t' e get,
         nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t' get) ->
         lookup u = Some e ->
         exists eD,
           exprD' tus tvs e t' = Some eD /\
           forall us vs,
             P us vs ->
             eD us vs = get us) ->
      forall e tvs' t eD,
        exprD' tus (tvs' ++ tvs) e t = Some eD ->
        exists eD',
          exprD' tus (tvs' ++ tvs) (instantiate (length tvs') e) t = Some eD' /\
          forall us vs' vs,
            P us vs ->
            eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).
  Proof.
    clear.
    induction e; simpl; intros; eauto.
    { red_exprD.
      forward; inv_all; subst.
      specialize (IHe1 _ _ _ H2); clear H2.
      specialize (IHe2 _ _ _ H3); clear H3.
      eapply typeof_expr_instantiate_Some in H1; eauto.
      { forward_reason.
        Cases.rewrite_all_goal.
        rewrite typ_cast_typ_refl. eexists; split; eauto.
        simpl. intros.
        rewrite H4; eauto.
        rewrite H3; eauto. }
      { clear - H.
        intros.
        specialize (H u t' e').
        consider (nth_error_get_hlist_nth (typD ts nil) tus u); intros.
        { destruct s.
          generalize H.
          eapply nth_error_get_hlist_nth_Some in H. simpl in *.
          forward_reason.
          rewrite x0 in H1. inv_all; subst.
          intros.
          specialize (H2 _ H1 H0). destruct H2 as [ ? [ ? ? ] ].
          clear H H1.
          rewrite exprD'_type_cast in H2.
          forward. inv_all; subst. reflexivity. }
        { exfalso. eapply nth_error_get_hlist_nth_None in H.
          congruence. } } }
    { red_exprD.
      forward; inv_all; subst.
      specialize (IHe (t :: tvs') t2 _ H2).
      simpl in IHe.
      forward_reason.
      rewrite H0.
      eexists; split; eauto.
      simpl. intros.
      eapply functional_extensionality. intros.
      exact (H1 us (Hcons x0 vs') vs X). }
    { consider (lookup u); intros.
      { red_exprD.
        forward; inv_all; subst.
        specialize (H _ _ _ _ H2 H1).
        forward_reason.
        generalize (@exprD'_lift _ _ RSym_func tus nil tvs' tvs e t).
        simpl. rewrite H.
        intros. forward.
        eexists; split; eauto.
        intros.
        erewrite <- H0. symmetry. eapply (H4 us Hnil vs' vs). apply X. }
      { eauto. } }
  Qed.

End instantiate.

Section mentionsU.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Section param.
    Variable u : uvar.

    Fixpoint mentionsU (e : expr func) : bool :=
      match e with
        | Var _
        | Inj _ => false
        | UVar u' => EqNat.beq_nat u u'
        | App f e => if mentionsU f then true else mentionsU e
        | Abs _ e => mentionsU e
      end.
  End param.

  Lemma mentionsU_lift : forall u e a b,
    mentionsU u (lift a b e) = mentionsU u e.
  Proof.
    induction e; simpl; intros; rewrite lift_lift'; simpl; intuition;
    repeat rewrite <- lift_lift' in *; intuition.
    { destruct (NPeano.ltb v a); auto. }
    { rewrite IHe1. rewrite IHe2. auto. }
  Qed.

  Theorem mentionsU_substU : forall u u' e' e under,
    mentionsU u (substU u' e under e') =
    if u ?[ eq ] u' then
      if mentionsU u e' then mentionsU u e else false
    else
      if mentionsU u e' then true else if mentionsU u' e' then mentionsU u e else false.
  Proof.
    induction e'; simpl; try congruence; intros;
    repeat match goal with
             | H : _ |- _ =>
               match type of H with
                 | not (eq _ _) => fail 1
                 | _ -> False => fail 1
                 | ?T => rewrite H by eauto
               end
             | |- context [ if @rel_dec ?A ?B ?C ?X ?Y then _ else _ ] =>
               consider (@rel_dec A B C X Y); try congruence; intros; auto; subst
             | |- context [ if EqNat.beq_nat ?X ?Y then _ else _ ] =>
               consider (EqNat.beq_nat X Y); try congruence; intros; subst; auto; subst
             | |- _ =>
               progress ( rewrite mentionsU_lift in * )
             | |- context [ if mentionsU ?X ?Y then _ else _ ] =>
               consider (mentionsU X Y); try congruence; intros; subst; auto
           end; simpl in *; eauto.
    consider (EqNat.beq_nat u' u0); congruence.
    consider (EqNat.beq_nat u0 u0); congruence.
    consider (EqNat.beq_nat u u0); congruence.
  Qed.

  Lemma mentionsU_WellTyped : forall tu e tv t,
    WellTyped_expr tu tv e t ->
    forall n : uvar, length tu <= n -> mentionsU n e = false.
  Proof.
    induction e; simpl; intros; auto.
    { rewrite WellTyped_expr_App in H.
      do 2 destruct H. intuition.
      erewrite IHe1; eauto. }
    { rewrite WellTyped_expr_Abs in H.
      destruct H; intuition; subst.
      eapply IHe; eauto. }
    { rewrite WellTyped_expr_UVar in *.
      consider (EqNat.beq_nat n u); intros; auto.
      subst. exfalso.
      rewrite <- (app_nil_r tu) in H.
      rewrite nth_error_app_R in *; auto.
      destruct (u - length tu); inversion H. }
  Qed.

  Theorem typeof_expr_mentionsU_strengthen : forall tu e tg t',
    mentionsU (length tu) e = false ->
    typeof_expr (tu ++ t' :: nil) tg e =
    typeof_expr tu tg e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | _ : context [ match ?X with _ => _ end ] |- _ =>
               consider X; intros; try congruence
             | H : _ |- _ =>
               erewrite H by eauto
           end; auto.
    destruct (Compare_dec.lt_eq_lt_dec (length tu) u) as [ [ | ] | ].
    { rewrite nth_error_past_end.
      rewrite nth_error_past_end; auto.
      omega. rewrite app_length. simpl. omega. }
    { consider (EqNat.beq_nat (length tu) u); try congruence. }
    { rewrite nth_error_app_L by auto. auto. }
  Qed.

  Lemma typeof_expr_mentionsU_strengthen_multi_lem : forall tu tu' e tg,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    typeof_expr (tu ++ rev tu') tg e =
    typeof_expr tu tg e.
  Proof.
    intros. induction tu'; simpl.
    { rewrite app_nil_r. reflexivity. }
    { rewrite <- app_ass.
      rewrite typeof_expr_mentionsU_strengthen.
      eapply IHtu'.
      rewrite app_length. rewrite H; auto.
      omega. }
  Qed.

  Theorem typeof_expr_mentionsU_strengthen_multi : forall tu tu' e tg,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    typeof_expr (tu ++ tu') tg e =
    typeof_expr tu tg e.
  Proof.
    intros.
    rewrite <- (rev_involutive tu').
    eapply typeof_expr_mentionsU_strengthen_multi_lem. auto.
  Qed.

  Lemma exprD'_mentionsU_strengthen : forall tu u e,
    mentionsU (length tu) e = false ->
    forall tg t,
    match ExprD.exprD' (tu ++ u :: nil) tg e t
        , ExprD.exprD' tu tg e t
    with
      | None , None => True
      | Some l , Some r => forall us uv vs,
                             l (hlist_app us (Hcons uv Hnil)) vs = r us vs
      | _ , _ => False
    end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw;
    repeat match goal with
             | _ : context [ match ?X with _ => _ end ] |- _ =>
               consider X; try congruence; intros
           end.
    { forward. }
    { forward. }
    { forward_reason.
      repeat rewrite typeof_expr_mentionsU_strengthen by eauto.
      forward. subst.
      specialize (H0 tg (tyArr t1 t2)).
      specialize (IHe2 tg t1).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
             end; inv_all; subst; auto.
      rewrite H4. rewrite IHe2. reflexivity. }
    { destruct t0; auto.
      specialize (IHe H (t :: tg) t0_2).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
             end; inv_all; subst; auto.
      eapply functional_extensionality; eauto. }
    { destruct (Compare_dec.lt_eq_lt_dec (length tu) u0) as [ [ | ] | ].
      { match goal with
          | |- match match ?X with _ => _ end with _ => _ end =>
            consider X; intros
        end.
        { eapply nth_error_get_hlist_nth_appR in H0; eauto with typeclass_instances.
          2: omega.
          simpl in *. forward_reason.
          exfalso.
          consider (u0 - length tu).
          { intros. exfalso. omega. }
          { congruence. } }
        { forward. subst. inv_all; subst.
          apply EnvI.nth_error_get_hlist_nth_Some in H2.
          forward_reason. simpl in *.
          clear - x l.
          apply nth_error_length_lt in x. omega. } }
      { exfalso.
        consider (EqNat.beq_nat (length tu) u0); congruence. }
      { generalize l.
        eapply nth_error_get_hlist_nth_appL with (F := typD ts nil) (tvs' := u :: nil) in l; eauto with typeclass_instances.
        forward_reason. simpl in *.
        repeat match goal with
          | H : ?X = _ |- context [ ?Y ] =>
            change Y with X ; rewrite H
        end.
        forward. simpl in *. forward.
        subst. f_equal. auto. } }
  Qed.

  Lemma exprD'_mentionsU_strengthen_multi_lem : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      match ExprD.exprD' (tu ++ rev tu') tg e t
          , ExprD.exprD' tu tg e t
      with
        | None , None => True
        | Some l , Some r => forall us us' vs,
                               l (hlist_app us us') vs = r us vs
        | _ , _ => False
      end.
  Proof.
    induction tu'; intros; simpl.
    { consider (exprD' tu tg e t); intros.
      { consider (exprD' (tu ++ nil) tg e t); intros.
        { rewrite (hlist_eta us').
          assert (tu ++ nil = tu) by (rewrite app_nil_r; auto).
          clear - H0 H1 H2.
          assert (hlist_app us Hnil = match eq_sym H2 in _ = t return hlist _ t with
                                        | eq_refl => us
                                      end).
          { clear.
            induction us. uip_all. reflexivity.
            simpl in *.
            uip_all.
            inversion e. specialize (IHus (eq_sym H0)).
            rewrite IHus. uip_all. clear.
            revert us.
            revert e. rewrite <- e0.
            intros. uip_all. reflexivity. }
          { rewrite H.
            revert H0. revert H1. clear.
            revert t1. revert t0. rewrite H2.
            intros. rewrite H1 in *.
            inv_all. subst t0.
            simpl. reflexivity. } }
        { assert (exprD' tu tg e t <> None) by congruence.
          clear - H1 H2.
          rewrite app_nil_r in H1. congruence. } }
      { forward.
        assert (exprD' (tu ++ nil) tg e t <> None) by congruence.
        clear - H0 H2.
        rewrite app_nil_r in H2. congruence. } }
    { assert (mentionsU (length (tu ++ rev tu')) e = false).
      { rewrite H; auto. rewrite app_length; omega. }
      generalize (exprD'_mentionsU_strengthen (tu ++ rev tu') a e H0 tg t).
      consider (exprD' (tu ++ rev tu') tg e t);
        consider (exprD' tu tg e t); intros; auto; forward.
      { consider (exprD' (tu ++ rev tu' ++ a :: nil) tg e t); intros.
        { generalize (hlist_app_hlist_split _ _ us').
          destruct (hlist_split (rev tu') (a :: nil) us').
          simpl in *.
          specialize (IHtu' us h vs).
          specialize (H4 (hlist_app us h) (hlist_hd h0) vs).
          intros. rewrite <- IHtu'. rewrite <- H4.
          subst. rewrite hlist_app_assoc; eauto with typeclass_instances.
          rewrite (hlist_eta h0). rewrite (hlist_eta (hlist_tl h0)).
          simpl in *.
          uip_all.
          generalize (hlist_app us (hlist_app h (Hcons (hlist_hd h0) Hnil))).
          generalize dependent t2; generalize dependent t3.
          clear. revert e0.
          rewrite <- (@app_ass typ). uip_all.
          rewrite H3 in H5. inv_all; subst; auto. }
        { clear - H3 H5.
          generalize dependent t2.
          rewrite app_ass. rewrite H5. congruence. } }
      { rewrite app_ass in H4. congruence. } }
  Qed.

  Theorem exprD'_mentionsU_strengthen_multi : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      match ExprD.exprD' (tu ++ tu') tg e t
          , ExprD.exprD' tu tg e t
      with
        | None , None => True
        | Some l , Some r => forall us us' vs,
                               l (hlist_app us us') vs = r us vs
        | _ , _ => False
      end.
  Proof.
    intros.
    rewrite <- (rev_involutive tu').
    eapply exprD'_mentionsU_strengthen_multi_lem. auto.
  Qed.

  Theorem exprD_mentionsU_strength_multi : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      exprD (Expr := @Expr_expr ts _ _) (tu ++ tu') tg e t =
      exprD (Expr := @Expr_expr ts _ _) tu tg e t.
  Proof.
    intros; unfold exprD.
    rewrite split_env_app.
    destruct (split_env tg); destruct (split_env tu').
    consider (split_env tu); intros.
    simpl.
    cutrewrite (length tu = length x1) in H.
    { generalize (exprD'_mentionsU_strengthen_multi _ e H x t x0).
      intros;
        repeat match goal with
                 | _ : match ?X with _ => _ end |- _ =>
                   destruct X; intuition
               end.
      f_equal. eapply H1. }
    { rewrite split_env_length. rewrite H0. reflexivity. }
  Qed.

End mentionsU.


(** TODO:
 ** This is a lot like [pull]
 **)
Section getInstantiation.
  Require Import MirrorCore.ExprI.
  Require Import MirrorCore.Ext.ExprD.

  Variable T : Type.
  Variable func : Type.
  Variable Subst_T : Subst T (expr func).

  Definition getInstantiation (s : T) : uvar -> nat -> option (list (expr func)) :=
    (fix recurse f l : option (list (expr func)) :=
       match l with
         | 0 => Some nil
         | S n =>
           match lookup f s with
             | None => None
             | Some z =>
               match recurse (S f) n with
                 | None => None
                 | Some zs' => Some (z :: zs')
               end
           end
       end).

  Variable ts : types.
  Variable RSym_func : RSym (typD ts) func.
  Variable SubstOk : SubstOk (Expr_expr _) Subst_T.
  Variable NormalizedSubstOk : NormalizedSubstOk Subst_T (@mentionsU func).

  Lemma getInstantiation_S : forall s b a,
    getInstantiation s a (S b) =
    match lookup a s with
      | None => None
      | Some e => match getInstantiation s (S a) b with
                    | None => None
                    | Some es => Some (e :: es)
                  end
    end.
  Proof. reflexivity. Qed.

  Lemma getInstantiation_0 : forall s a,
    getInstantiation s a 0 = Some nil.
  Proof. reflexivity. Qed.

  Lemma getInstantiation_contains_each : forall s b a i,
    getInstantiation s a b = Some i ->
    forall n,
      n < b ->
      exists e,
        lookup (a + n) s = Some e /\
        nth_error i n = Some e.
  Proof.
    induction b; intros.
    { exfalso. omega. }
    { rewrite getInstantiation_S in *.
      consider (lookup a s); try congruence; intros.
      consider (getInstantiation s (S a) b); try congruence; intros.
      inv_all; subst.
      specialize (IHb _ _ H1).
      destruct n.
      { rewrite Plus.plus_0_r. rewrite H. simpl; eauto. }
      { rewrite <- plus_n_Sm. eapply IHb. omega. } }
  Qed.

  Lemma nth_error_Some_len : forall T (ls : list T) n v,
    nth_error ls n = Some v ->
    n < length ls.
  Proof.
    induction ls; destruct n; simpl; unfold error, value; intros; try congruence.
    omega. eapply IHls in H. omega.
  Qed.

  Lemma WellTyped_getInstantiation : forall s us vs us' i,
    WellTyped_subst (SubstOk := SubstOk) (us ++ us') vs s ->
    getInstantiation s (length us) (length us') = Some i ->
    forall n,
      match nth_error us' n with
        | None => True
        | Some t =>
          exists e,
               nth_error i n = Some e
            /\ Safe_expr (Expr := Expr_expr _) us vs e t
      end.
  Proof.
    intros.
    specialize (getInstantiation_contains_each _ _ H0); intro.
    consider (nth_error us' n); auto; intros.
    generalize (nth_error_Some_len _ _ H2); intro.
    destruct (H1 _ H3).
    exists x.
    intuition.
    destruct (WellTyped_lookup _ _ _ _ H H5).
    rewrite nth_error_app_R in H4. 2: omega.
    cutrewrite (length us + n - length us = n) in H4; try omega.
    rewrite H2 in *. intuition; inv_all; subst.
    unfold Safe_expr in *; simpl in *.
    admit. (*
    rewrite typeof_expr_mentionsU_strengthen_multi in H8.
    eapply H8.
    intros.
    consider (length (us ++ us') ?[ le ] n0).
    { intros; eapply mentionsU_WellTyped with (n := n0); eauto. }
    { intros.
      destruct NormalizedSubstOk.
      destruct (H1 (n0 - length us)).
      { rewrite app_length in H7; omega. }
      { eapply lookup_normalized; try eassumption.
        replace (length us + (n0 - length us)) with n0 in H9 by omega.
        intuition eauto. } } *)
  Qed.
End getInstantiation.

(** TODO: This should respect better abstraction
Section funced.
  Variable func : Type.

(*
  Definition instantiate : (uvar -> option (expr func)) -> expr func -> expr func :=
    fun z => ExprSubst.instantiate z 0.
*)

  Fixpoint get_mentions (e : expr func) (acc : pset) : pset :=
    match e with
      | Var _
      | Inj _ => acc
      | App l r => get_mentions l (get_mentions r acc)
      | Abs _ e => get_mentions e acc
      | UVar u => PositiveMap.add (to_key u) tt acc
    end.

  Definition get_mentions_instantiate (i : uvar -> option (expr func)) (e : expr func)
  : pset * expr func :=
    let e' := instantiate i e in
    (get_mentions e' (PositiveMap.empty _), e').

(*
  Definition l := @fast_subst_lookup (expr func).
  Definition e := @fast_subst_empty (expr func).
  Definition s := @fast_subst_set (expr func) get_mentions_instantiate instantiate.
  Definition d := @fast_subst_pull (expr func).

  Require Import ExtLib.Structures.Monad.
  Require Import ExtLib.Data.Monads.OptionMonad.

  Eval compute in s 0 (UVar 1) e.
  Eval compute in bind (s 1 (Inj 2) e) (fun x => bind (s 0 (UVar 1) x) (d 1 1)).
  Eval compute in bind (s 0 (UVar 1) e) (fun x => bind (s 1 (Inj 2) x) (d 0 2)).
*)

End funced.
*)