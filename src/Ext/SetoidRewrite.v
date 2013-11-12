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
  | PRguess (t : typ)
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

  Definition setoid_rewrite' (tus : tenv typ)
  : expr sym -> tenv typ -> PR -> option (T * R) :=
    @Fix (expr sym) _ (wf_rightTrans (@wf_expr_acc sym))
         (fun _ => tenv typ -> PR -> option (T * R))
         (fun e =>
            match e as e
               return (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R)) -> tenv typ -> PR -> option (T * R)
            with
              | App l r => fun recur tvs rel =>
                             (** TODO: It shouldn't be necessary to type check here **)
                match typeof_expr tus tvs r with
                  | None => None
                  | Some ty =>
                    match recur l (TransitiveClosure.RTFin _ _ _ (acc_App_l _ _)) tvs (PRfunctorial (PRguess ty) rel) with
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

  Fixpoint typeForPR (r : PR) : typ :=
    match r with
      | PRinj r => typeForRbase r
      | PRfunctorial l r => tyArr (typeForPR l) (typeForPR r)
      | PRpointwise t r => tyArr t (typeForPR r)
      | PRguess t => t
    end.

  Inductive instantiates : R -> PR -> Prop :=
  | Ins_guess : forall x, instantiates x (PRguess (typeForR x))
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

  Hypothesis Hatomic
  : forall tus tvs e r r' result
           (recur : forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e
                               -> tenv typ -> PR -> option (T * R)),
      @atomic tus e recur tvs r = Some (result, r') ->
      (forall tvs e' r r' result pf,
         recur e' pf tvs r = Some (result, r') ->
         instantiates r' r /\
         forall us vs x,
           WellTyped_env tus us ->
           WellTyped_env tvs vs ->
           exprD us vs e' (typeForR r') = Some x ->
           TR us vs r' result x) ->
      instantiates r' r /\
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR r') = Some x ->
        TR us vs r' result x.

  Hypothesis atomic_ext
  : forall a b c x f g,
      (forall e pf p q,
         f e pf p q = g e pf p q) ->
      @atomic a x f b c = @atomic a x g b c.

  Hypothesis Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      exprD us vs f (typeForR (Rfunctorial t1 t2)) = Some v1 ->
      @TR us vs (Rfunctorial t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app (typeof_env us) (typeof_env vs) r1 r2 t1 t2) (v1 v2).

  Hypothesis Habs
  : forall us vs t1 t2 r1 v1 f,
      exprD us vs f (typeForR (Rpointwise t1 t2)) = Some v1 ->
      (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
      @TR us vs (Rpointwise t1 t2) (abs (typeof_env us) (typeof_env vs) t1 r1 t2) v1.

  Lemma setoid_rewrite'_eta : forall tus e tvs rel,
    setoid_rewrite' tus e tvs rel =
    match e with
      | App l r =>
        match typeof_expr tus tvs r with
          | None => None (** Never happens **)
          | Some ty =>
            match setoid_rewrite' tus l tvs (PRfunctorial (PRguess ty) rel) with
              | None =>
                @atomic tus (App l r) (fun e _ => setoid_rewrite' tus e) tvs rel
              | Some (l', relx) =>
                match relx with
                  | Rfunctorial rel' out =>
                    match setoid_rewrite' tus r tvs (R_to_PR rel') with
                      | None =>
                        @atomic tus (App l r) (fun e _ => setoid_rewrite' tus e) tvs rel
                      | Some (r', out_r) => (** maybe this is strange **)
                        (** out_r = rel' **)
                        Some (app tus tvs l' r' rel' out, out)
                    end
                  | _ => None (** Never happens **)
                end
            end
        end
      | Abs t e' =>
        match rel with
          | PRpointwise t' r' =>
            match setoid_rewrite' tus e' (t :: tvs) r' with
              | Some (result, r'') =>
                Some (abs tus tvs t result r'', Rpointwise t' r'')
              | _ =>
                @atomic tus (Abs t e') (fun e _ => setoid_rewrite' tus e) tvs rel
            end
          | _ =>
            @atomic tus (Abs t e') (fun e _ => setoid_rewrite' tus e) tvs rel
        end
      | e' =>
        @atomic tus e' (fun e _ => setoid_rewrite' tus e) tvs rel
    end.
  Proof.
    unfold setoid_rewrite'.
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
    { destruct x; subst; simpl; intros; eauto using atomic_ext.
      { forward. rewrite H.
        destruct (g x1
                    (TransitiveClosure.RTFin (expr_acc (func:=sym)) x1
                                             (App x1 x2) (acc_App_l x1 x2)) a (PRfunctorial (PRguess t) b)).
        { destruct p. forward. rewrite H.
          forward. eauto using atomic_ext. }
        eauto using atomic_ext. }
      destruct b; eauto using atomic_ext.
      rewrite H. forward; eauto using atomic_ext. }
  Qed.

  Lemma instantiates_typeof : forall r1 r2,
                                instantiates r1 r2 ->
                                typeForR r1 = typeForPR r2.
  Proof.
    clear. induction 1; simpl; intros; Cases.rewrite_all; auto.
  Qed.

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

  Lemma instantiates_guess : forall l t,
                               instantiates l (PRguess t) ->
                               typeForR l = t.
  Proof.
    clear. intros. remember (PRguess t).
    inversion H; subst; try congruence.
  Qed.

  Lemma setoid_rewrite'_sound_lem
  : forall e tus tvs r r' result,
      setoid_rewrite' tus e tvs r = Some (result, r') ->
      instantiates r' r /\
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR r') = Some x ->
        TR us vs r' result x.
  Proof.
    refine (@expr_strong_ind _ _ _).
    destruct e; simpl; intros; rewrite setoid_rewrite'_eta in H0;
    eauto using Hatomic with typeclass_instances.
    { forward.
      consider (setoid_rewrite' tus e1 tvs (PRfunctorial (PRguess t) r)); intros;
      eauto using Hatomic with typeclass_instances.
      { destruct p. forward. subst.
        consider (setoid_rewrite' tus e2 tvs (R_to_PR l));
          eauto using Hatomic with typeclass_instances; intros.
        destruct p. inv_all; subst.
        generalize (H _ _ _ _ _ _ _ H2); clear H2.
        generalize (H _ _ _ _ _ _ _ H1); clear H H1.
        intros. destruct H; destruct H1.
        eapply instantiates_R_to_PR in H. subst.
        eapply inv_instantiates_functorial in H1.
        destruct H1. split; auto.
        intros.
        red_exprD.
        forward; inv_all; subst.
        clear Habs Hatomic.
        inversion H; clear H; subst.
        assert (t3 = typeForR l).
        { eapply WellTyped_env_typeof_env in H4.
          eapply WellTyped_env_typeof_env in H5.
          subst.
          apply (typeof_expr_exprD_same_type _ _ _ _ _ H9 H0). }
        subst.
        specialize (H3 us vs _ H4 H5 H8).
        specialize (H2 us vs _ H4 H5 H9).
        eapply WellTyped_env_typeof_env in H4.
        eapply WellTyped_env_typeof_env in H5. subst.
        specialize (@Happ us vs l r' t0 t1); eauto. } }
    { destruct r; eauto using Hatomic.
      { consider (setoid_rewrite' tus e (t :: tvs) r); eauto using Hatomic.
        destruct p; intros. inv_all; subst.
        specialize (H _ _ _ _ _ _ _ H0).
        destruct H. split.
        { constructor. auto. }
        { clear Happ Hatomic. intros.
          red_exprD. inversion x1; subst.
          revert H4. uip_all'. intros; subst.
          apply WellTyped_env_typeof_env in H2.
          apply WellTyped_env_typeof_env in H3. subst.
          eapply (@Habs us vs t r0 t1 _ (Abs t e)).
          { admit. }
          { intros.
            eapply H1; eauto.
            { eapply WellTyped_env_typeof_env; auto. }
            { eapply WellTyped_env_typeof_env; auto. }
            { generalize dependent (x2 x); intros.
              match goal with
                | |- ?X = Some (match ?Y with _ => _ end _) =>
                  change Y with X ; destruct X
              end; auto. exfalso; auto. } } } } }
  Qed.

(*
  (** TODO: I really need to work this out with [exprD'] **)
  Lemma setoid_rewrite'_sound_lem2
  : forall vs e tus tvs r r' result,
      setoid_rewrite' tus e (tvs ++ typeof_env vs) r = Some (result, r') ->
      instantiates r' r /\
      forall us vs' x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD' us (vs' ++ typeof_env vs) e (typeForR r') = Some x ->
        TR us vs r' result x.
  Proof.
    refine (@expr_strong_ind _ _ _).
    destruct e; simpl; intros; rewrite setoid_rewrite'_eta in H0;
    eauto using Hatomic with typeclass_instances.
    { forward.
      consider (setoid_rewrite' tus e1 tvs (PRfunctorial (PRguess t) r)); intros;
      eauto using Hatomic with typeclass_instances.
      { destruct p. forward. subst.
        consider (setoid_rewrite' tus e2 tvs (R_to_PR l));
          eauto using Hatomic with typeclass_instances; intros.
        destruct p. inv_all. inversion H3; clear H3; subst.
        generalize (H _ _ _ _ _ _ _ H2); clear H2.
        generalize (H _ _ _ _ _ _ _ H1); clear H H1.
        intros. destruct H; destruct H1.
        eapply instantiates_R_to_PR in H. subst.
        eapply inv_instantiates_functorial in H1.
        destruct H1. split; auto.
        intros.
        red_exprD.
        forward; inv_all; subst.
        clear Habs Hatomic.
        inversion H; clear H; subst.
        assert (t3 = typeForR l).
        { eapply WellTyped_env_typeof_env in H4.
          eapply WellTyped_env_typeof_env in H5.
          subst.
          apply (typeof_expr_exprD_same_type _ _ _ _ H9 H0). }
        subst.
        specialize (H3 us vs _ H4 H5 H8).
        specialize (H2 us vs _ H4 H5 H9).
        eapply WellTyped_env_typeof_env in H4.
        eapply WellTyped_env_typeof_env in H5. subst.
        specialize (@Happ us vs l r' t0 t1); eauto. } }
    { destruct r; eauto using Hatomic.
      { consider (setoid_rewrite' tus e (t :: tvs) r); eauto using Hatomic.
        destruct p; intros. inv_all; subst.
        inversion H1; clear H1; subst.
        specialize (H _ _ _ _ _ _ _ H0).
        destruct H. split.
        { constructor. auto. }
        { clear Happ Hatomic. intros.
          red_exprD. inversion x1; subst.
          revert H4. uip_all'. intros; subst.
          apply WellTyped_env_typeof_env in H2.
          apply WellTyped_env_typeof_env in H3. subst.
          eapply (@Habs us vs t r0 t1 _ (Abs t e)).
          { admit. }
          { intros.
            eapply H1; eauto.
            { eapply WellTyped_env_typeof_env; auto. }
            { eapply WellTyped_env_typeof_env; auto. }
            { generalize dependent (x2 x); intros.
              match goal with
                | |- ?X = Some (match ?Y with _ => _ end _) =>
                  change Y with X ; destruct X
              end; auto. exfalso; auto. } } } } }
  Qed.
*)

  Definition setoid_rewrite (tus tvs : tenv typ) (e : expr sym) (r : R) : option T :=
    match setoid_rewrite' tus e tvs (R_to_PR r) with
      | None => None
      | Some (t, _) => Some t
    end.

  Theorem setoid_rewrite_sound
  : forall tus tvs e r result,
      setoid_rewrite tus tvs e r = Some result ->
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR r) = Some x ->
        TR us vs r result x.
  Proof.
    unfold setoid_rewrite. intros.
    consider (setoid_rewrite' tus e tvs (R_to_PR r)); intros; try congruence.
    destruct p; intuition. inv_all; subst.
    eapply setoid_rewrite'_sound_lem in H. intuition.
    eapply instantiates_R_to_PR in H3. subst.
    eauto.
  Qed.

End setoid.

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

  Definition setoid_rewriteI {T} (a : SRW_Algo T)
  : tenv typ -> tenv typ -> expr sym -> R a.(Rbase) -> option T :=
    @setoid_rewrite ts sym RSym_sym _ T a.(atomic) a.(app) a.(abs).

  Theorem setoid_rewriteI_sound {T} (a : SRW_Algo T) (aC : SRW_AlgoOk a)
  : forall tus tvs e r result,
      setoid_rewriteI a tus tvs e r = Some result ->
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR aC.(typeForRbase) r) = Some x ->
        aC.(TR) us vs r result x.
  Proof.
    unfold setoid_rewriteI. intros.
    destruct aC.
    eapply setoid_rewrite_sound in H; eauto.
  Qed.

End interface.
