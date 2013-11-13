Require Import Relations.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Variable ts : types.
  Variable sym : Type. (** Symbols **)
  Variable RSym_sym : RSym (typD ts) sym.
  Variable Rbase : Type. (** Relations **)
  Variable T : Type. (** Result type **)

  Inductive PR : Type :=
  | PRinj (r : Rbase)
  | PRguess
  | PRfunctorial (l r : PR)
  | PRpointwise (t : typ) (r : PR).

  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rfunctorial (l r : R)
  | Rpointwise (t : typ) (r : R).

  Fixpoint to_R (r : PR) : option R :=
    match r with
      | PRinj i => Some (Rinj i)
      | PRpointwise t r =>
        match to_R r with
          | None => None
          | Some r => Some (Rpointwise t r)
        end
      | PRfunctorial l r =>
        match to_R l , to_R r with
          | Some l , Some r => Some (Rfunctorial l r)
          | _ , _ => None
        end
      | _ => None
    end.

  Fixpoint R_to_PR (r : R) : PR :=
    match r with
      | Rinj i => PRinj i
      | Rfunctorial l r => PRfunctorial (R_to_PR l) (R_to_PR r)
      | Rpointwise t r => PRpointwise t (R_to_PR r)
    end.

  (** The input relation must not have variables in it? **)
  Variable atomic : tenv typ -> forall e : expr sym,
    (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R))
    -> tenv typ -> PR -> option (T * R).

  (** ?? **)
  Variable app : tenv typ -> tenv typ -> T -> T -> R -> R -> T.
  Variable abs : tenv typ -> tenv typ -> typ -> T -> R -> T.

  Definition setoid_fold' (tus : tenv typ)
  : expr sym -> tenv typ -> PR -> option (T * R) :=
    @Fix (expr sym) _ (wf_rightTrans (@wf_expr_acc sym))
         (fun _ => tenv typ -> PR -> option (T * R))
         (fun e =>
            match e as e
               return (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R)) -> tenv typ -> PR -> option (T * R)
            with
              | App l r => fun recur tvs rel =>
                match recur l (TransitiveClosure.RTFin _ _ _ (acc_App_l _ _))
                            tvs (PRfunctorial PRguess rel) with
                  | None =>
                    @atomic tus (App l r) recur tvs rel
                  | Some (l', relx) =>
                    match relx with
                      | Rfunctorial rel' out =>
                        match recur r (TransitiveClosure.RTFin _ _ _ (acc_App_r _ _)) tvs
                                    (R_to_PR rel')
                        with
                          | None =>
                            @atomic tus (App l r) recur tvs rel
                          | Some (r', out_r) => (** maybe this is strange **)
                            (** out_r = rel' **)
                            Some (app tus tvs l' r' rel' out, out)
                        end
                      | _ => None (** Never happens **)
                    end
                end
              | Abs t e' => fun recur tvs prel =>
                match prel with
                  | PRpointwise t' r' =>
                    match recur e'
                                (TransitiveClosure.RTFin _ _ _ (acc_Abs _ _))
                                (t :: tvs) r'
                    with
                      | Some (result, r'') =>
                        Some (abs tus tvs t result r'', Rpointwise t' r'')
                      | _ =>
                        @atomic tus (Abs t e') recur tvs prel
                    end
                  | _ =>
                    @atomic tus (Abs t e') recur tvs prel
                end
              | e' => fun recur tvs rel =>
                @atomic tus e' recur tvs rel
            end).

  Variable typeForRbase : Rbase -> typ.

  Fixpoint typeForR (r : R) : typ :=
    match r with
      | Rinj r => typeForRbase r
      | Rfunctorial l r => tyArr (typeForR l) (typeForR r)
      | Rpointwise t r => tyArr t (typeForR r)
    end.

  Inductive pr_type : PR -> typ -> Prop :=
  | PT_guess : forall t, pr_type PRguess t
  | PT_inj : forall i, pr_type (PRinj i) (typeForRbase i)
  | PT_func : forall a b c d,
                pr_type a b ->
                pr_type c d ->
                pr_type (PRfunctorial a c) (tyArr b d)
  | PT_point : forall a c d,
                pr_type c d ->
                pr_type (PRpointwise a c) (tyArr a d).

  Inductive instantiates : R -> PR -> Prop :=
  | Ins_guess : forall x, instantiates x PRguess
  | Ins_inj : forall i, instantiates (Rinj i) (PRinj i)
  | Ins_func : forall a b c d,
                 instantiates a b ->
                 instantiates c d ->
                 instantiates (Rfunctorial a c) (PRfunctorial b d)
  | Ins_point : forall a b t,
                 instantiates a b ->
                 instantiates (Rpointwise t a) (PRpointwise t b).

  Variable TR : env (typD ts) -> env (typD ts) ->
                forall r : R, T -> typD ts nil (typeForR r) -> Prop.

  Hypothesis Hatomic_ext
  : forall a b c x f g,
      (forall e pf p q,
         f e pf p q = g e pf p q) ->
      @atomic a x f b c = @atomic a x g b c.

  Lemma setoid_fold'_eta : forall tus e tvs rel,
    setoid_fold' tus e tvs rel =
    match e with
      | App l r =>
        match setoid_fold' tus l tvs (PRfunctorial PRguess rel) with
          | None =>
            @atomic tus (App l r) (fun e _ => setoid_fold' tus e) tvs rel
          | Some (l', relx) =>
            match relx with
              | Rfunctorial rel' out =>
                match setoid_fold' tus r tvs (R_to_PR rel') with
                  | None =>
                    @atomic tus (App l r) (fun e _ => setoid_fold' tus e) tvs rel
                  | Some (r', out_r) =>
                    Some (app tus tvs l' r' rel' out, out)
                end
              | _ => None (** Never happens **)
            end
        end
      | Abs t e' =>
        match rel with
          | PRpointwise t' r' =>
            match setoid_fold' tus e' (t :: tvs) r' with
              | Some (result, r'') =>
                Some (abs tus tvs t result r'', Rpointwise t' r'')
              | _ =>
                @atomic tus (Abs t e') (fun e _ => setoid_fold' tus e) tvs rel
            end
          | _ =>
            @atomic tus (Abs t e') (fun e _ => setoid_fold' tus e) tvs rel
        end
      | e' =>
        @atomic tus e' (fun e _ => setoid_fold' tus e) tvs rel
    end.
  Proof.
    unfold setoid_fold'.
    intros.
    match goal with
      | |- context [ @Fix _ _ _ _ ?F _ ] =>
        remember F ;
        generalize (@Fix_equiv _ (TransitiveClosure.rightTrans (expr_acc (func:=sym))) (wf_rightTrans (wf_expr_acc (func:=sym)))
                               _ o
                   (fun x f g => forall a b, f a b = g a b))
    end.
    intro X. rewrite X; clear X.
    { subst. destruct e; try reflexivity. }
    { destruct x; subst; simpl; intros; eauto using Hatomic_ext.
      { forward. rewrite H.
        destruct (g x1
                    (TransitiveClosure.RTFin (expr_acc (func:=sym)) x1
                                             (App x1 x2) (acc_App_l x1 x2)) a (PRfunctorial PRguess b)).
        { destruct p. forward. rewrite H.
          forward. eauto using Hatomic_ext. }
        eauto using Hatomic_ext. }
      destruct b; eauto using Hatomic_ext.
      rewrite H. forward; eauto using Hatomic_ext. }
  Qed.

(**
  Hypothesis Hatomic
  : forall tus tvs e r r' result
           (recur : forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e
                               -> tenv typ -> PR -> option (T * R)),
      @atomic tus e recur tvs r = Some (result, r') ->
      (forall tvs e' r r' result pf,
         recur e' pf tvs r = Some (result, r') ->
         instantiates r' r) ->
      instantiates r' r /\
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        (forall e' x pf,
           recur e' pf tvs r = Some (result, r') ->
           WellTyped_env tus us ->
           WellTyped_env tvs vs ->
           exprD us vs e' (typeForR r') = Some x ->
           TR us vs r' result x) ->
        exprD us vs e (typeForR r') = Some x ->
        TR us vs r' result x.

  Hypothesis Hatomic_typed
  : forall tus tvs e r r' t result,
      pr_type r t ->
      typeof_expr tus tvs e = Some t ->
      atomic tus
             (fun (e0 : expr sym)
                  (_ : TransitiveClosure.rightTrans (expr_acc (func:=sym)) e0 e) =>
                setoid_fold' tus e0) tvs r = Some (result, r') ->
      (forall y : expr sym,
         TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e ->
         forall (tus0 tvs0 : tenv typ) (r0 : PR) (r'0 : R)
                (result0 : T) (t0 : typ),
           pr_type r0 t0 ->
           typeof_expr tus0 tvs0 y = Some t0 ->
           setoid_fold' tus0 y tvs0 r0 = Some (result0, r'0) ->
           typeForR r'0 = t0) ->
      typeForR r' = t.
**)

  

  Definition setoid_fold_syntactic
             (tus tvs : tenv typ) (e : expr sym) (r : PR) (result : T) (r' : R)
  :=
    pr_type r (typeForR r') ->
    typeof_expr tus tvs e = Some (typeForR r') ->
    instantiates r' r.

(*
  Hypothesis Hatomic_types
  : forall tus tvs e r r' result recur,
      (forall e' pf tvs r result r',
         @recur e' pf tvs r = Some (result, r') ->
         setoid_fold_syntactic tus tvs e r result r') ->
      @atomic tus e recur tvs r = Some (result, r') ->
      setoid_fold_syntactic tus tvs e r result r'.
*)

  Definition setoid_fold_spec
             (tus tvs : tenv typ) (e : expr sym) (r : PR) (result : T) (r' : R)
  :=
    forall t,
      pr_type r t ->
      typeof_expr tus tvs e = Some t ->
      instantiates r' r /\
      typeForR r' = t /\
      forall us,
        WellTyped_env tus us ->
        match exprD' us tvs e (typeForR r') with
          | Some x =>
            forall vs,
              TR us (join_env vs) r' result (x vs)
          | None => True
        end.

  Hypothesis Hatomic
  : forall tus tvs e r r' result recur,
      (forall e' pf tvs r result r',
         @recur e' pf tvs r = Some (result, r') ->
         setoid_fold_spec tus tvs e' r result r') ->
      @atomic tus e recur tvs r = Some (result, r') ->
      setoid_fold_spec tus tvs e r result r'.

  Hypothesis Happ
  : forall us vs t1 t2 v1 f,
      exprD us vs f (typeForR (Rfunctorial t1 t2)) = Some v1 ->
      forall r1 r2 v2,
      @TR us vs (Rfunctorial t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app (typeof_env us) (typeof_env vs) r1 r2 t1 t2) (v1 v2).

  Hypothesis Habs
  : forall us vs t1 t2 r1 v1 f,
      exprD us vs f (typeForR (Rpointwise t1 t2)) = Some v1 ->
      (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
      @TR us vs (Rpointwise t1 t2) (abs (typeof_env us) (typeof_env vs) t1 r1 t2) v1.

  Lemma inv_instantiates_functorial : forall a b c d,
    instantiates (Rfunctorial a b) (PRfunctorial c d) ->
    instantiates a c /\ instantiates b d.
  Proof.
    clear. inversion 1; subst; eauto.
  Qed.

  Theorem instantiates_R_to_PR : forall a b, instantiates a (R_to_PR b) -> a = b.
  Proof.
    clear.
    induction a; destruct b; simpl; intros; try solve [ inversion H ].
    { inversion H; subst; auto. }
    { inversion H; subst; auto. Cases.rewrite_all. auto. }
    { inversion H; subst; auto. f_equal; auto. }
  Qed.

(*
  Lemma atomic_instantiates
  : forall (tus tvs : tenv typ) r r' result (e : expr sym),
      (forall y : expr sym,
         SolveTypeClass (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e) ->
         forall (tus0 tvs0 : tenv typ) (r0 : PR) (r'0 : R) (result0 : T),
           setoid_fold' tus0 y tvs0 r0 = Some (result0, r'0) ->
           instantiates r'0 r0) ->
      atomic tus
             (fun (e0 : expr sym)
                  (_ : TransitiveClosure.rightTrans (expr_acc (func:=sym)) e0 e) =>
                setoid_fold' tus e0) tvs r = Some (result, r') ->
      instantiates r' r.
  Proof.
    clear - Hatomic; intros.
    eapply Hatomic; eauto. simpl.
    intros. eapply H; eauto.
  Qed.
*)

  Lemma pr_type_R_to_PR : forall x,
                            pr_type (R_to_PR x) (typeForR x).
  Proof.
    clear. induction x; simpl.
    constructor.
    constructor; auto.
    constructor; auto.
  Qed.

  Ltac try_atomic :=
    try match goal with
          | H : atomic _ _ _ _ = _ |- _ =>
            solve [ eapply Hatomic in H; eauto ]
        end.

  Lemma setoid_fold'_sound
  : forall tus e tvs r r' result,
      setoid_fold' tus e tvs r = Some (result, r') ->
      setoid_fold_spec tus tvs e r result r'.
  Proof.
    intro.
    refine (@expr_strong_ind _ _ _).
    destruct e; simpl; intros; rewrite setoid_fold'_eta in H0;
      try_atomic.
    { forward_unsafe; inv_all; subst; try_atomic.
      generalize (H _ _ _ _ _ _ H4); clear H4.
      generalize (H _ _ _ _ _ _ H2); clear H2 H.
      unfold setoid_fold_spec; intros.
      simpl in H2. unfold type_of_apply in H2.
      forward; inv_all; subst.
      edestruct H4; clear H4; eauto.
      { constructor; auto. constructor. }
      { destruct H5.
        apply inv_instantiates_functorial in H.
        simpl in *. inv_all; subst. intuition.
        edestruct H3; clear H3; eauto using pr_type_R_to_PR.
        destruct H8.
        forward. red_exprD. forward; inv_all; subst.
        eapply instantiates_R_to_PR in H7. subst.
        assert (t3 = typeForR l).
        { eapply typeof_expr_exprD_same_type with (us := us) (vs := join_env vs) (e := e2).
          unfold exprD. rewrite split_env_join_env. rewrite H12. reflexivity.
          rewrite typeof_env_join_env.
          apply WellTyped_env_typeof_env in H; subst; auto. }
        subst.
        specialize (H8 _ H).
        specialize (H5 _ H).
        rewrite H12 in *. rewrite H11 in *.
        assert (TR us (join_env vs) r' (app tus (typeof_env (join_env vs)) t t0 l r') (t5 vs (t6 vs))).
        { apply WellTyped_env_typeof_env in H; subst.
          eapply Happ; eauto.
          unfold exprD. rewrite split_env_join_env.
          instantiate (1 := e1).
          rewrite H11. reflexivity. }
        { rewrite typeof_env_join_env in H7. assumption. } } }
    { destruct r; try_atomic.
      consider (setoid_fold' tus e (t :: tvs) r); intros; try_atomic; intros.
      destruct p. inv_all; subst.
      red. intros.
      simpl in *; forward; inv_all; subst.
      inversion H1; clear H1; subst.
      specialize (@H _ _ _ _ _ _ H0 _ H4 H2).
      destruct H. destruct H1.
      split.
      { constructor. auto. }
      split.
      { f_equal. auto. }
      { intros.
        red_exprD.
        rewrite typ_cast_typ_refl.
        specialize (H3 _ H5).
        forward.
        assert (TR us (join_env vs) (Rpointwise t r0)
                   (abs (typeof_env us) (typeof_env (join_env vs)) t t1 r0)
                   (fun x : typD ts nil t => t0 (HList.Hcons x vs))).
        { eapply Habs; eauto.
          instantiate (1 := (Abs t e)).
          unfold exprD. rewrite split_env_join_env.
          red_exprD.
          rewrite typ_cast_typ_refl. rewrite H3. reflexivity.
          intro. specialize (H6 (HList.Hcons x vs)).
          auto. }
        { rewrite typeof_env_join_env in *.
          apply WellTyped_env_typeof_env in H5. subst. auto. } } }
  Qed.

(*
  Lemma setoid_fold'_types_lem
  : forall e tus tvs r r' result t,
      pr_type r t ->
      typeof_expr tus tvs e = Some t ->
      setoid_fold' tus e tvs r = Some (result, r') ->
      typeForR r' = t.
  Proof.
    refine (@expr_strong_ind _ _ _).
    destruct e; simpl; intros; rewrite setoid_fold'_eta in H2.
    { eapply Hatomic_typed; simpl in *; eauto; eassumption. }
    { eapply Hatomic_typed; simpl in *; eauto; eassumption. }
    { forward.
      consider (setoid_fold' tus e1 tvs (PRfunctorial PRguess r));
        try congruence; intros.
      { destruct p. destruct r0; try congruence.
        consider (setoid_fold' tus e2 tvs (R_to_PR r0_1)); intros.
        { destruct p; inv_all; subst.
          destruct t0; simpl in *; try congruence.
          forward. inv_all; subst.
          eapply H in H2; eauto with typeclass_instances.
          simpl in *. inv_all; subst. reflexivity.
          constructor. constructor. auto. }
        { eapply Hatomic_typed in H6; eauto.
          simpl. Cases.rewrite_all. auto. } }
      { eapply Hatomic_typed in H5; eauto.
        simpl. Cases.rewrite_all. auto. } }
    { forward.
      inv_all; subst.
      destruct r; try congruence.
      { eapply Hatomic_typed in H2; eauto.
        simpl. Cases.rewrite_all. auto. }
      { eapply Hatomic_typed in H2; eauto.
        simpl. Cases.rewrite_all. auto. }
      { eapply Hatomic_typed in H2; eauto.
        simpl. Cases.rewrite_all. auto. }
      inversion H0; clear H0; subst.
      consider (setoid_fold' tus e (t :: tvs) r); intros.
      { destruct p; try congruence. inv_all; subst.
        simpl. f_equal.
        eapply H in H0; eauto with typeclass_instances. }
      { eapply Hatomic_typed in H2.
        2: econstructor; eassumption.
        2: simpl; Cases.rewrite_all; auto.
        auto.
        eauto. } }
    { eapply Hatomic_typed in H2; eauto. }
  Qed.


  Lemma instantiates_pr_type : forall r r',
                                 instantiates r' r ->
                                 pr_type r (typeForR r').
  Proof.
    clear. induction 1; constructor; eauto.
  Qed.

  Lemma atomic_sound_lem
  : forall us e tvs r r' t result,
      pr_type r t ->
      (forall y : expr sym,
         SolveTypeClass (TransitiveClosure.rightTrans (expr_acc (func:=sym)) y e) ->
         forall (us0 : env (typD ts)) (tvs0 : tenv typ)
                (r0 : PR) (r'0 : R) (result0 : T) (t0 : typ),
           pr_type r0 t0 ->
           typeof_expr (typeof_env us0) tvs0 y = Some t0 ->
           setoid_fold' (typeof_env us0) y tvs0 r0 = Some (result0, r'0) ->
           match exprD' us0 tvs0 y (typeForR r'0) with
             | Some x =>
               forall vs : HList.hlist (typD ts nil) tvs0,
                 TR us0 (join_env vs) r'0 result0 (x vs)
             | None => True
           end) ->
      typeof_expr (typeof_env us) tvs e = Some t ->
      atomic (typeof_env us)
             (fun (e0 : expr sym)
                  (_ : TransitiveClosure.rightTrans (expr_acc (func:=sym)) e0 e) =>
                setoid_fold' (typeof_env us) e0) tvs r = Some (result, r') ->
      match exprD' us tvs e (typeForR r') with
        | Some x =>
          forall vs : HList.hlist (typD ts nil) tvs,
            TR us (join_env vs) r' result (x vs)
        | None => True
      end.
  Proof.
    clear Happ Habs atomic_ext.
    intuition.
    forward.
    specialize (Hatomic H2).
    specialize (Hatomic_typed H H1 H2).
    clear H2. intuition.
    destruct Hatomic; eauto.
    { intros. eapply setoid_fold'_instantiates; eauto. }
    { apply (H4 us (join_env vs) (t0 vs)).
      { eapply WellTyped_env_typeof_env; auto. }
      { eapply WellTyped_env_typeof_env. rewrite typeof_env_join_env. auto. }
      { intuition.
        assert (typeof_expr (typeof_env us) tvs e' = Some (typeForR r')).
        { change (WellTyped_expr (typeof_env us) tvs e' (typeForR r')).
          cutrewrite (tvs = typeof_env (join_env vs)).
          rewrite typeof_expr_exprD. eauto.
          rewrite typeof_env_join_env. auto. }
        specialize (fun x => @H0 _ pf us tvs _ _ _ _ x H9 H5).
        unfold exprD in H8. rewrite split_env_join_env in H8.
        forward. inv_all; subst. eapply H8.
        eapply instantiates_pr_type; auto. }
      { unfold exprD. rewrite split_env_join_env.
        rewrite H3. auto. } }
  Qed.

  Lemma setoid_fold'_sound_lem
  : forall e us tvs r r' result t,
      pr_type r t ->
      typeof_expr (typeof_env us) tvs e = Some t ->
      setoid_fold' (typeof_env us) e tvs r = Some (result, r') ->
      match exprD' us tvs e (typeForR r') with
        | None => True
        | Some x =>
          forall vs,
            TR us (@join_env _ _ tvs vs) r' result (x vs)
      end.
  Proof.
    clear atomic_ext.
    refine (@expr_strong_ind _ _ _).
    destruct e; simpl; intros; rewrite setoid_fold'_eta in H2;
      eauto using atomic_sound_lem with typeclass_instances.
    { eapply atomic_sound_lem; eauto. }
    { eapply atomic_sound_lem; eauto. }
    { forward; inv_all; subst.
      { consider (setoid_fold' (typeof_env us) e1 tvs (PRfunctorial PRguess r));
        intros.
        { destruct p.
          destruct r0; try congruence.
          consider (setoid_fold' (typeof_env us) e2 tvs (R_to_PR r0_1)); intros.
          { destruct p. inv_all; subst.
            autorewrite with exprD_rw in H5.
            rewrite H1 in *.
            destruct t0; simpl in *; try congruence.
            forward; inv_all; try subst.
            subst t1. subst t.
            subst.
            assert (pr_type (PRfunctorial PRguess r) (tyArr t0_1 (typeForR r'))).
            { constructor. constructor. auto. }
            generalize (H e1 _ us tvs _ _ t3 _ H4 H1 H2).
            generalize (setoid_fold'_instantiates _ _ _ _ H2).
            generalize (setoid_fold'_instantiates _ _ _ _ H6).
            generalize (@setoid_fold'_types_lem _ _ _ _ _ _ _ H4 H1 H2).
            simpl. intros.
            eapply instantiates_R_to_PR in H9.
            inv_all. subst.
            assert (pr_type (R_to_PR r0_1) (typeForR r0_1)).
            { eapply pr_type_R_to_PR. }
            generalize (H e2 _ us tvs _ _ _ _ H8 H3 H6).
            rewrite H7.
            intro. specialize (H9 vs).
            rewrite H5 in *. specialize (H11 vs).
            cut (TR us (join_env vs) r'
                    (app (typeof_env us) (typeof_env (join_env vs)) t3 t4 r0_1 r')
                    (t0 vs (t5 vs))).
            { rewrite typeof_env_join_env. auto. }
            eapply Happ; eauto. instantiate (1 := e1).
            unfold exprD. rewrite split_env_join_env.
            rewrite H5. reflexivity. }
          { eapply atomic_sound_lem in H7; eauto.
            rewrite H5 in *. eauto.
            simpl. Cases.rewrite_all. auto. } }
        { eapply atomic_sound_lem in H6; eauto.
          rewrite H5 in *. eauto.
          simpl. Cases.rewrite_all. auto.  } } }
    { forward; inv_all; subst.
      destruct r.
      { eapply atomic_sound_lem in H2; eauto.
        rewrite H4 in *. eauto.
        simpl. Cases.rewrite_all. auto. }
      { eapply atomic_sound_lem in H2; eauto.
        rewrite H4 in *. eauto.
        simpl. Cases.rewrite_all. auto. }
      { eapply atomic_sound_lem in H2; eauto.
        rewrite H4 in *. eauto.
        simpl. Cases.rewrite_all. auto. }
      consider (setoid_fold' (typeof_env us) e (t :: tvs) r); intros.
      { destruct p. inv_all; subst.
        inversion H0; clear H0; subst.
        specialize (@Habs us (join_env vs) t r0 t3 (t2 vs) (Abs t e)).
        unfold exprD in Habs. rewrite split_env_join_env in Habs.
        rewrite H4 in Habs.
        specialize (@Habs eq_refl).
        autorewrite with exprD_rw in H4.
        simpl in *.
        forward; inv_all; subst.
        revert Habs.
        uip_all'.
        rewrite typeof_env_join_env in *.
        eapply Habs. intros.
        eapply H in H2; eauto with typeclass_instances.
        rewrite H3 in *.
        specialize (H2 (HList.Hcons x0 vs)).
        simpl in H2. eauto. }
      { eapply atomic_sound_lem in H3; eauto.
        rewrite H4 in *. eauto.
        simpl; Cases.rewrite_all; auto. } }
    { eapply atomic_sound_lem in H2; eauto. }
  Qed.
**)

  Definition setoid_fold (tus tvs : tenv typ) (e : expr sym) (r : R) : option T :=
    match setoid_fold' tus e tvs (R_to_PR r) with
      | None => None
      | Some (t, _) => Some t
    end.

  Theorem setoid_fold_sound
  : forall tus tvs e r result,
      setoid_fold tus tvs e r = Some result ->
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR r) = Some x ->
        TR us vs r result x.
  Proof.
    unfold setoid_fold. intros.
    consider (setoid_fold' tus e tvs (R_to_PR r)); intros; try congruence.
    destruct p; intuition. inv_all; subst.
    eapply setoid_fold'_sound in H. red in H.
    edestruct H; eauto using pr_type_R_to_PR.
    { assert (exists v, exprD us vs e (typeForR r) = Some v); eauto.
      eapply typeof_expr_exprD in H3.
      eapply WellTyped_env_typeof_env in H0.
      eapply WellTyped_env_typeof_env in H1. subst.
      auto. }
    { destruct H4.
      specialize (H5 _ H0).
      unfold exprD in *.
      consider (split_env vs); intros.
      forward. inv_all; subst.
      eapply instantiates_R_to_PR in H3; subst.
      cutrewrite (tvs = x0) in H5.
      rewrite H6 in *. specialize (H5 h).
      cutrewrite (vs = join_env h). auto.
      eapply split_env_projT2_join_env; eauto.
      change x0 with (projT1 (existT (HList.hlist (typD ts nil)) x0 h)).
      match goal with
        | H : _ = ?X |- _ = projT1 ?Y =>
          change Y with X ; rewrite <- H2
      end.
      rewrite split_env_projT1.
      eapply WellTyped_env_typeof_env in H1.
      subst. reflexivity. }
  Qed.

End setoid.

(**
Section interface.
  Variable ts : types.
  Variable sym : Type. (** Symbols **)
  Variable RSym_sym : RSym (typD ts) sym.

  Let tc_acc : relation (expr sym) :=
    TransitiveClosure.rightTrans (@expr_acc sym).

  Record SRW_Algo (T : Type) : Type :=
  { Rbase : Type (** Relations **)
    (** The input relation must not have variables in it? **)
  ; atomic : tenv typ -> forall e : expr sym,
    (forall e', tc_acc e' e -> tenv typ -> PR Rbase -> option (T * R Rbase))
    -> tenv typ -> PR Rbase -> option (T * R Rbase)
    (** ?? **)
  ; app : tenv typ -> tenv typ -> T -> T -> R Rbase -> R Rbase -> T
  ; abs : tenv typ -> tenv typ -> typ -> T -> R Rbase -> T
  }.

  Record SRW_AlgoOk (T : Type) (Algo : SRW_Algo T) : Type :=
  { typeForRbase : Algo.(Rbase) -> typ
  ; TR : env (typD ts) -> env (typD ts) -> forall r : R Algo.(Rbase), T -> typD ts nil (typeForR typeForRbase r) -> Prop

  ;  Hatomic
     : forall tus tvs e r r' result
              (recur : forall e', tc_acc e' e
                                  -> tenv typ -> PR Algo.(Rbase) ->
                                  option (T * R Algo.(Rbase))),
         Algo.(atomic) tus (e := e) recur tvs r = Some (result, r') ->
         (forall tvs e' r r' result pf,
            recur e' pf tvs r = Some (result, r') ->
            instantiates typeForRbase r' r /\
            forall us vs x,
              WellTyped_env tus us ->
              WellTyped_env tvs vs ->
              exprD us vs e' (typeForR typeForRbase r') = Some x ->
              TR us vs r' result x) ->
         instantiates typeForRbase r' r /\
         forall us vs x,
           WellTyped_env tus us ->
           WellTyped_env tvs vs ->
           exprD us vs e (typeForR typeForRbase r') = Some x ->
           TR us vs r' result x
  ; atomic_ext
    : forall a b c x f g,
        (forall e pf p q,
           f e pf p q = g e pf p q) ->
        Algo.(atomic) a (e:=x) f b c = Algo.(atomic) a (e:=x) g b c
  ; Happ
    : forall us vs t1 t2 r1 r2 v1 v2 f,
        exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
        @TR us vs (Rfunctorial t1 t2) r1 v1 ->
        @TR us vs t1 r2 v2 ->
        @TR us vs t2 (Algo.(app) (typeof_env us) (typeof_env vs) r1 r2 t1 t2) (v1 v2)
  ; Habs
    : forall us vs t1 t2 r1 v1 f,
        exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
        (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
        @TR us vs (Rpointwise t1 t2)
            (Algo.(abs) (typeof_env us) (typeof_env vs) t1 r1 t2) v1
  }.

  Section from_proper.

    Variable (T : Type).
    Variable (_Rbase : Type).
    Hypothesis (_properAt : expr sym -> PR _Rbase -> option (R _Rbase)).
    Hypothesis (_atomic : tenv typ -> forall e : expr sym,
                                       (forall e', tc_acc e' e -> tenv typ ->
                                                   (PR _Rbase) -> option (T * (R _Rbase)))
                                       -> tenv typ -> R _Rbase -> T).
    Hypothesis (_app : tenv typ -> tenv typ -> T -> T -> R _Rbase -> R _Rbase -> T).
    Hypothesis (_abs : tenv typ -> tenv typ -> typ -> T -> R _Rbase -> T).

    Definition SRW_Algo_properAt : SRW_Algo T :=
      {| Rbase := _Rbase
       ; atomic := fun tus e recur tvs rel =>
                     match _properAt e rel with
                       | None => None
                       | Some rel' =>
                         Some (_atomic tus (e:=e) recur tvs rel', rel')
                     end
       ; app := _app
       ; abs := _abs
       |}.

    Hypothesis typeForRbase : _Rbase -> typ.
    Hypothesis TR : env (typD ts) -> env (typD ts) -> forall r : R _Rbase, T -> typD ts nil (typeForR typeForRbase r) -> Prop.
    Hypothesis Hatomic
    : forall e r r',
        _properAt e r = Some r' ->
        instantiates typeForRbase r' r /\
        forall us vs x result (recur : forall e', tc_acc e' e -> tenv typ -> PR _Rbase-> option (T * R _Rbase)),
        (forall e' tvs r r' result pf,
           recur e' pf tvs r = Some (result, r') ->
           instantiates typeForRbase r' r /\
           forall vs x,
             WellTyped_env tvs vs ->
             exprD us vs e' (typeForR typeForRbase r') = Some x ->
             TR us vs r' result x) ->
        _atomic (typeof_env us) recur (typeof_env vs) r' = result ->
        exprD us vs e (typeForR typeForRbase r') = Some x ->
        TR us vs r' result x.
    Hypothesis Hatomic_ext
    : forall a b c x f g,
        (forall e pf p q,
           f e pf p q = g e pf p q) ->
        _atomic a (e:=x) f b c = _atomic a (e:=x) g b c.
    Hypothesis Happ
    : forall us vs t1 t2 r1 r2 v1 v2 f,
        exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
        @TR us vs (Rfunctorial t1 t2) r1 v1 ->
        @TR us vs t1 r2 v2 ->
        @TR us vs t2 (_app (typeof_env us) (typeof_env vs) r1 r2 t1 t2) (v1 v2).
    Hypothesis Habs
    : forall us vs t1 t2 r1 v1 f,
        exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
        (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
        @TR us vs (Rpointwise t1 t2) (_abs (typeof_env us) (typeof_env vs) t1 r1 t2) v1.

    Theorem SRW_AlgoOk_properAt : SRW_AlgoOk SRW_Algo_properAt.
    Proof.
      refine (@Build_SRW_AlgoOk _ SRW_Algo_properAt typeForRbase _ _ _ _ _);
      simpl; eauto using Happ, Habs.
      { intros.
        forward; inv_all; subst.
        destruct (@Hatomic _ _ _ H); intuition.
        eapply H2; clear H2; eauto.
        { instantiate (1 := recur).
          intros.
          specialize (@H0 _ _ _ _ _ _ H2).
          intuition. }
        { eapply WellTyped_env_typeof_env in H3.
          eapply WellTyped_env_typeof_env in H4.
          subst. reflexivity. } }
      { intros.
        destruct (_properAt x c); auto.
        f_equal. f_equal. eapply Hatomic_ext. auto. }
    Qed.
  End from_proper.

  Definition setoid_foldI {T} (a : SRW_Algo T)
  : tenv typ -> tenv typ -> expr sym -> R a.(Rbase) -> option T :=
    @setoid_fold ts sym RSym_sym _ T a.(atomic) a.(app) a.(abs).

  Theorem setoid_foldI_sound {T} (a : SRW_Algo T) (aC : SRW_AlgoOk a)
  : forall tus tvs e r result,
      setoid_foldI a tus tvs e r = Some result ->
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR aC.(typeForRbase) r) = Some x ->
        aC.(TR) us vs r result x.
  Proof.
    unfold setoid_foldI. intros.
    destruct aC.
    eapply setoid_fold_sound in H; eauto.
  Qed.

End interface.
**)