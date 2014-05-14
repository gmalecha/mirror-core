Require Import Coq.Relations.Relations.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
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

  Let Expr_expr : Expr (typD ts) (expr sym) := Expr_expr _.
  Local Existing Instance Expr_expr.

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
  Variable app : tenv typ -> tenv typ -> T -> T -> R -> R -> option T.
  Variable abs : tenv typ -> tenv typ -> typ -> T -> R -> option T.

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
                          | Some (r', out_r) =>
                            (** out_r = rel' **)
                            Monad.bind (app tus tvs l' r' rel' out)
                                       (fun x => Monad.ret (x, out))
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
                        Monad.bind (abs tus tvs t result r'')
                                   (fun x => Monad.ret (x, Rpointwise t' r''))
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
                    Monad.bind (app tus tvs l' r' rel' out)
                               (fun x => Monad.ret (x,out))
                end
              | _ => None (** Never happens **)
            end
        end
      | Abs t e' =>
        match rel with
          | PRpointwise t' r' =>
            match setoid_fold' tus e' (t :: tvs) r' with
              | Some (result, r'') =>
                Monad.bind (abs tus tvs t result r'')
                           (fun x => Monad.ret (x, Rpointwise t' r''))
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

  Definition setoid_fold_syntactic
             (tus tvs : tenv typ) (e : expr sym) (r : PR) (result : T) (r' : R)
  :=
    pr_type r (typeForR r') ->
    typeof_expr tus tvs e = Some (typeForR r') ->
    instantiates r' r.

  Definition setoid_fold_spec
             (tus tvs : tenv typ) (e : expr sym) (r : PR) (result : T) (r' : R)
  :=
    forall t,
      pr_type r t ->
      typeof_expr tus tvs e = Some t ->
      instantiates r' r /\
      typeForR r' = t /\
        match exprD' tus tvs e (typeForR r') with
          | Some x =>
            forall us vs,
              TR (join_env us) (join_env vs) r' result (x us vs)
          | None => True
        end.

  Hypothesis Hatomic
  : forall tus tvs e r r' result recur,
      @atomic tus e recur tvs r = Some (result, r') ->
      (forall e' pf tvs r result r',
         @recur e' pf tvs r = Some (result, r') ->
         setoid_fold_spec tus tvs e' r result r') ->
      setoid_fold_spec tus tvs e r result r'.

  Hypothesis Happ
  : forall us vs t1 t2 result r1 r2,
      app (typeof_env us) (typeof_env vs) r1 r2 t1 t2 = Some result ->
      forall f v1 v2,
        exprD us vs f (typeForR (Rfunctorial t1 t2)) = Some v1 ->
        @TR us vs (Rfunctorial t1 t2) r1 v1 ->
        @TR us vs t1 r2 v2 ->
        @TR us vs t2 result (v1 v2).

  Hypothesis Habs
  : forall us vs t1 t2 r1 result,
      abs (typeof_env us) (typeof_env vs) t1 r1 t2 = Some result ->
      forall v1 f,
        exprD us vs f (typeForR (Rpointwise t1 t2)) = Some v1 ->
        (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
        @TR us vs (Rpointwise t1 t2) result v1.

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
    { inversion H; subst; auto. Cases.rewrite_all_goal. auto. }
    { inversion H; subst; auto. f_equal; auto. }
  Qed.

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
      { unfold Monad.bind in *.
        simpl in H5.
        apply inv_instantiates_functorial in H. destruct H.
        forward; inv_all; subst.
        destruct H6. inv_all; subst.
        edestruct H3; clear H3; eauto using pr_type_R_to_PR.
        destruct H8.
        eapply instantiates_R_to_PR in H6; subst.
        intuition.
        forward. red_exprD. forward; inv_all; subst.
        change ((fix typeForR (r : R) : typ :=
             match r with
             | Rinj r0 => typeForRbase r0
             | Rfunctorial l r0 => tyArr (typeForR l) (typeForR r0)
             | Rpointwise t r0 => tyArr t (typeForR r0)
             end)) with typeForR in *.
        rewrite H11 in H8.
        rewrite H10 in H7.
        uip_all.
        replace tvs with (typeof_env (join_env vs)) in H5 by apply typeof_env_join_env.
        replace tus with (typeof_env (join_env us)) in H5 by apply typeof_env_join_env.
        specialize (@Happ _ _ _ _ _ _ _ H5).
        eapply Happ; eauto.
        instantiate (1 := e1).
        unfold exprD. rewrite split_env_join_env.
        change ExprD3.EXPR_DENOTE_core.exprD' with exprD'.
        rewrite split_env_join_env. simpl. rewrite H10. reflexivity. } }
    { destruct r; try_atomic.
      consider (setoid_fold' tus e (t :: tvs) r); intros; try_atomic; intros.
      destruct p. inv_all; subst.
      red. intros.
      simpl in *; forward; inv_all; subst.
      inversion H2; clear H2; subst.
      specialize (@H _ _ _ _ _ _ H0 _ H5 H3).
      destruct H. destruct H2. subst.
      split.
      { constructor. auto. }
      split.
      { f_equal. auto. }
      { intros.
        simpl.
        red_exprD.
        forward.
        eapply Habs; eauto.
        { repeat rewrite typeof_env_join_env. eapply H1. }
        { instantiate (1 := (Abs t e)).
          unfold exprD. repeat rewrite split_env_join_env.
          change (@ExprI.exprD' _ _ _ _) with exprD'.
          red_exprD.
          rewrite H2. reflexivity. }
        { intro. specialize (H4 us (HList.Hcons x vs)). auto. } } }
  Qed.

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
      unfold exprD in *.
      consider (split_env vs); intros.
      consider (split_env us); intros.
      change ExprD3.EXPR_DENOTE_core.exprD' with exprD' in *.
      forward. inv_all; subst.
      eapply instantiates_R_to_PR in H3; subst.
      cutrewrite (tvs = x0) in H5.
      cutrewrite (tus = x1) in H5.
      unfold Expr_expr in *; simpl in *.
      rewrite H7 in *. specialize (H5 h0 h).
      cutrewrite (vs = join_env h).
      cutrewrite (us = join_env h0); auto.
      eapply split_env_projT2_join_env; eauto.
      eapply split_env_projT2_join_env; eauto.
      change x1 with (projT1 (existT (HList.hlist (typD ts nil)) x1 h0)).
      match goal with
        | H : _ = ?X |- _ = projT1 ?Y =>
          change Y with X ; rewrite <- H
      end.
      rewrite split_env_projT1.
      eapply WellTyped_env_typeof_env in H0. apply H0.
      change x0 with (projT1 (existT (HList.hlist (typD ts nil)) x0 h)).
      match goal with
        | H : _ = ?X |- _ = projT1 ?Y =>
          change Y with X ; rewrite <- H
      end.
      rewrite split_env_projT1.
      eapply WellTyped_env_typeof_env in H1. apply H1. }
  Qed.

End setoid.

Section interface.
  Variable ts : types.
  Variable sym : Type. (** Symbols **)
  Variable RSym_sym : RSym (typD ts) sym.

  Let Expr_expr : Expr (typD ts) (expr sym) := Expr_expr _.
  Local Existing Instance Expr_expr.

  Let tc_acc : relation (expr sym) :=
    TransitiveClosure.rightTrans (@expr_acc sym).

  Record SRW_Algo (T : Type) : Type :=
  { Rbase : Type (** Relations **)
    (** The input relation must not have variables in it? **)
  ; atomic : tenv typ -> forall e : expr sym,
    (forall e', tc_acc e' e -> tenv typ -> PR Rbase -> option (T * R Rbase))
    -> tenv typ -> PR Rbase -> option (T * R Rbase)
    (** ?? **)
  ; app : tenv typ -> tenv typ -> T -> T -> R Rbase -> R Rbase -> option T
  ; abs : tenv typ -> tenv typ -> typ -> T -> R Rbase -> option T
  }.

  Record SRW_AlgoOk (T : Type) (Algo : SRW_Algo T) : Type :=
  { typeForRbase : Algo.(Rbase) -> typ
  ; TR : env (typD ts) -> env (typD ts) -> forall r : R Algo.(Rbase), T -> typD ts nil (typeForR typeForRbase r) -> Prop
  ; Hatomic_ext
    : forall a b c x f g,
        (forall e pf p q,
           f e pf p q = g e pf p q) ->
        Algo.(atomic) a (e:=x) f b c = Algo.(atomic) a (e:=x) g b c
  ; Hatomic
  : forall tus tvs e r r' result recur,
      Algo.(atomic) tus (e:=e) recur tvs r = Some (result, r') ->
      (forall e' pf tvs r result r',
         @recur e' pf tvs r = Some (result, r') ->
         @setoid_fold_spec _ _ RSym_sym _ _ _ TR tus tvs e' r result r') ->
      @setoid_fold_spec _ _ RSym_sym _ _ _ TR tus tvs e r result r'
  ; Happ
  : forall us vs t1 t2 result r1 r2,
      Algo.(app) (typeof_env us) (typeof_env vs) r1 r2 t1 t2 = Some result ->
      forall f v1 v2,
        exprD us vs f (typeForR _ (Rfunctorial t1 t2)) = Some v1 ->
        @TR us vs (Rfunctorial t1 t2) r1 v1 ->
        @TR us vs t1 r2 v2 ->
        @TR us vs t2 result (v1 v2)
  ; Habs
  : forall us vs t1 t2 r1 result,
      Algo.(abs) (typeof_env us) (typeof_env vs) t1 r1 t2 = Some result ->
      forall v1 f,
        exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
        (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
        @TR us vs (Rpointwise t1 t2) result v1
  }.

  Section from_proper.

    Variable (T : Type).
    Variable (_Rbase : Type).
    Hypothesis (_properAt : expr sym -> PR _Rbase -> option (R _Rbase)).
    Hypothesis (_atomic : tenv typ -> tenv typ -> expr sym -> R _Rbase -> option T).
    Hypothesis (_app : tenv typ -> tenv typ -> T -> T -> R _Rbase -> R _Rbase -> option T).
    Hypothesis (_abs : tenv typ -> tenv typ -> typ -> T -> R _Rbase -> option T).

    Definition SRW_Algo_properAt : SRW_Algo T :=
    {| Rbase := _Rbase
     ; atomic := fun tus e recur tvs rel =>
                   match _properAt e rel with
                     | None => None
                     | Some rel' =>
                       match _atomic tus tvs e rel' with
                         | None => None
                         | Some x => Some (x, rel')
                       end
                   end
     ; app := _app
     ; abs := _abs
     |}.

    Hypothesis typeForRbase : _Rbase -> typ.
    Hypothesis TR : env (typD ts) -> env (typD ts) -> forall r : R _Rbase, T -> typD ts nil (typeForR typeForRbase r) -> Prop.
    Hypothesis Hatomic
    : forall tus tvs e r r' result,
        _properAt e r = Some r' ->
        _atomic tus tvs e r' = Some result ->
        @setoid_fold_spec _ _ RSym_sym _ _ _ TR tus tvs e r result r'.
    Hypothesis Happ
    : forall us vs t1 t2 r1 r2 v1 v2 f result,
        _app (typeof_env us) (typeof_env vs) r1 r2 t1 t2 = Some result ->
        exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
        @TR us vs (Rfunctorial t1 t2) r1 v1 ->
        @TR us vs t1 r2 v2 ->
        @TR us vs t2 result (v1 v2).
    Hypothesis Habs
    : forall us vs t1 t2 r1 v1 f result,
        _abs (typeof_env us) (typeof_env vs) t1 r1 t2 = Some result ->
        exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
        (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
        @TR us vs (Rpointwise t1 t2) result v1.

    Theorem SRW_AlgoOk_properAt : SRW_AlgoOk SRW_Algo_properAt.
    Proof.
      refine (@Build_SRW_AlgoOk _ SRW_Algo_properAt typeForRbase _ _ _ _ _);
         simpl; eauto using Hatomic, Happ, Habs.
      { intros.
        forward; inv_all; subst. clear H0.
        eapply Hatomic; eauto. }
      { intros. eapply Happ; eauto. }
      { intros. eapply Habs; eauto. }
    Qed.
  End from_proper.

  Definition setoid_foldI {T} (a : SRW_Algo T)
  : tenv typ -> tenv typ -> expr sym -> R a.(Rbase) -> option T :=
    @setoid_fold sym _ T a.(atomic) a.(app) a.(abs).

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