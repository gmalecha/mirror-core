Require Import Relations.
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

  (** The output relation will be an instantiation of R **)
  Variable properAt : expr sym -> PR -> option R.

  (** The input relation must not have variables in it? **)
  Variable atomic : tenv typ -> forall e : expr sym,
                      (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R))
                      -> tenv typ -> R -> T.

  (** ?? **)
  Variable app : tenv typ -> tenv typ -> T -> T -> R -> R -> T.
  Variable abs : tenv typ -> tenv typ -> typ -> T -> R -> T.

  Definition setoid_rewrite' (tus : tenv typ) : expr sym -> tenv typ -> PR -> option (T * R) :=
    @Fix (expr sym) _ (wf_rightTrans (@wf_expr_acc sym))
         (fun _ => tenv typ -> PR -> option (T * R))
         (fun e =>
            match e as e
               return (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R)) -> tenv typ -> PR -> option (T * R)
            with
              | App l r => fun recur tvs rel =>
                match typeof_expr tus tvs r with
                  | None => None
                  | Some ty =>
                    match recur l (TransitiveClosure.RTFin _ _ _ (acc_App_l _ _)) tvs (PRfunctorial (PRguess ty) rel) with
                      | None =>
                        match properAt (App l r) rel with
                          | None => None
                          | Some rel' =>
                            Some (@atomic tus (App l r) recur tvs rel', rel')
                        end
                      | Some (l', relx) =>
                        match relx with
                          | Rfunctorial rel' out =>
                            match recur r (TransitiveClosure.RTFin _ _ _ (acc_App_r _ _)) tvs
                                        (R_to_PR rel')
                            with
                              | None => None
                              | Some (r', out_r) => (** maybe this is strange **)
                                (** out_r = rel' **)
                                Some (app tus tvs l' r' out_r out, out)
                            end
                          | _ => None (** Never happens **)
                        end
                    end
                end
              | Abs t e' => fun recur tvs prel =>
                              match prel with
                                | PRpointwise t' r' =>
                                  match recur e' (TransitiveClosure.RTFin _ _ _ (acc_Abs _ _))
                                              (t :: tvs) r'
                                  with
                                    | Some (result, r'') =>
                                      Some (abs tus tvs t result r'', Rpointwise t' r'')
                                    | _ =>
                                      match properAt (Abs t e') prel with
                                        | None => None
                                        | Some rel' =>
                                          Some (@atomic tus (Abs t e') recur tvs rel', rel')
                                      end
                                  end
                                | _ =>
                                  match properAt (Abs t e') prel with
                                    | None => None
                                    | Some rel' =>
                                      Some (@atomic tus (Abs t e') recur tvs rel', rel')
                                  end
                              end
              | e' => fun recur tvs rel =>
                        match properAt e' rel with
                          | None => None
                          | Some rel' =>
                            Some (@atomic tus e' recur tvs rel', rel')
                        end
            end).

  Variable typeForRbase : Rbase -> typ.

  Fixpoint typeForPR (r : PR) : typ :=
    match r with
      | PRinj r => typeForRbase r
      | PRguess t => t
      | PRfunctorial l r => tyArr (typeForPR l) (typeForPR r)
      | PRpointwise t r => tyArr t (typeForPR r)
    end.

  Fixpoint typeForR (r : R) : typ :=
    match r with
      | Rinj r => typeForRbase r
      | Rfunctorial l r => tyArr (typeForR l) (typeForR r)
      | Rpointwise t r => tyArr t (typeForR r)
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

  Variable TR : env (typD ts) -> env (typD ts) -> forall r : R, T -> typD ts nil (typeForR r) -> Prop.

  Hypothesis Hatomic
  : forall e r r',
      properAt e r = Some r' ->
      instantiates r' r /\
      forall us vs x result (recur : forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR -> option (T * R)),
        (forall tus e' tvs r r' result pf,
           recur e' pf tvs r = Some (result, r') ->
           instantiates r' r /\
           forall us vs x,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             exprD us vs e' (typeForR r') = Some x ->
             TR us vs r' result x) ->
        @atomic (typeof_env us) e recur (typeof_env vs) r' = result ->
        exprD us vs e (typeForR r') = Some x ->
        TR us vs r' result x.

  Hypothesis Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      exprD us vs f (typeForR (Rfunctorial t1 t2)) = Some v1 ->
      @TR us vs (Rfunctorial t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app (typeof_env us) (typeof_env vs) r1 r2 t1 t2) (v1 v2).

  Hypothesis Habs
  : forall us vs (t1 : typ) (t2 : R) (r1 : T) (v1 : typD ts nil t1 -> typD ts nil (typeForR t2)) f,
      exprD us vs f (typeForR (Rpointwise t1 t2)) = Some v1 ->
      (forall x : typD ts nil t1, @TR us (existT _ _ x :: vs) t2 r1 (v1 x)) ->
      @TR us vs (Rpointwise t1 t2) (abs (typeof_env us) (typeof_env vs) t1 r1 t2) v1.

  Lemma setoid_rewrite'_eta : forall tus e tvs rel,
    setoid_rewrite' tus e tvs rel =
    match e with
      | App l r =>
        match typeof_expr tus tvs r with
          | None => None
          | Some ty =>
            match setoid_rewrite' tus l tvs (PRfunctorial (PRguess ty) rel) with
              | None =>
                match properAt (App l r) rel with
                  | None => None
                  | Some rel' =>
                    Some (@atomic tus (App l r) (fun e _ => setoid_rewrite' tus e) tvs rel', rel')
                end
              | Some (l', relx) =>
                match relx with
                  | Rfunctorial rel' out =>
                    match setoid_rewrite' tus r tvs (R_to_PR rel') with
                      | None => None
                      | Some (r', out_r) => (** maybe this is strange **)
                        (** out_r = rel' **)
                        Some (app tus tvs l' r' out_r out, out)
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
                match properAt (Abs t e') rel with
                  | None => None
                  | Some rel' =>
                    Some (@atomic tus (Abs t e') (fun e _ => setoid_rewrite' tus e) tvs rel', rel')
                end
            end
          | _ =>
            match properAt (Abs t e') rel with
              | None => None
              | Some rel' =>
                Some (@atomic tus (Abs t e') (fun e _ => setoid_rewrite' tus e) tvs rel', rel')
            end
        end
      | e' =>
        match properAt e' rel with
          | None => None
          | Some rel' =>
            Some (@atomic tus e' (fun e _ => setoid_rewrite' tus e) tvs rel', rel')
        end
    end.
  Proof.
    unfold setoid_rewrite'.
    intros. erewrite Fix_eq.
    { destruct e; reflexivity. }
    { intros. destruct x; simpl; try reflexivity.
      admit.
      admit.
      admit.
      admit.
      admit. }
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

  Lemma setoid_rewrite_sound_lem
  : forall tus e tvs r r' result,
      setoid_rewrite' tus e tvs r = Some (result, r') ->
      instantiates r' r /\
      forall us vs x,
        WellTyped_env tus us ->
        WellTyped_env tvs vs ->
        exprD us vs e (typeForR r') = Some x ->
        TR us vs r' result x.
  Proof.
    induction e; simpl; intros.
    admit.
    admit.
    admit.
(*
    { rewrite setoid_rewrite_eta in *.
      generalize dependent (@Var sym v); intros.
      forward. inv_all; subst.
      inversion H0; clear H0; subst.
      destruct (@Hatomic e r r' H).
      auto. }
    { admit. }
    { rewrite setoid_rewrite_eta in H.
      red_exprD. forward.
      consider (setoid_rewrite (typeof_env us) e1 (typeof_env vs) (PRfunctorial (PRguess t) r)); intros.
      { destruct p. forward; inv_all; subst. inversion H4; clear H4; subst.
        specialize (@IHe1 _ _ _ _ H1); destruct IHe1.
        eapply inv_instantiates_functorial in H0. intuition.
        specialize (@IHe2 _ _ _ _ H3); destruct IHe2.
        forward; subst. inv_all; subst.
        generalize (@typ_cast_typ_eq _ _ _ _ _ _ H11); intros; subst.
        rewrite typ_cast_typ_refl in H11. inv_all; subst.
        eapply instantiates_R_to_PR in H6. subst.
        simpl in H2.
        cut (typeForR l = t); intros; subst.
        { cut (t3 = typeForR l); intros; subst.
          { specialize (H2 _ H9).
            specialize (H7 _ H10).
            eapply Happ; eauto. }
          { revert H. revert H10. clear. admit. } }
        { 
          eauto using instantiates_guess. } }
      { admit. } }
*)
    { rewrite setoid_rewrite'_eta in H.
      destruct r. admit. admit. admit.
      consider (setoid_rewrite' tus e (t :: tvs) r).
      { destruct p; intros. inv_all; subst.
        inversion H0; clear H0; subst.
        specialize (IHe _ _ _ _ H). intuition.
        { constructor. auto. }
        { clear Happ Hatomic.
          red_exprD. inversion x1; subst.
          revert H4. uip_all'. intros; subst.
          apply WellTyped_env_typeof_env in H2.
          apply WellTyped_env_typeof_env in H3. subst.
          eapply (@Habs us vs t r0 t1 _ (Abs t e)).
          { admit. }
          { intros.
            eapply H1; eauto. admit. admit.
            admit. } } }
      { admit. } }

    admit.
  Qed.

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
    eapply setoid_rewrite_sound_lem in H. intuition.
    eapply instantiates_R_to_PR in H3. subst.
    eauto.
  Qed.

End setoid.

Section interface.
  Variable ts : types.
  Variable sym : Type. (** Symbols **)
  Variable RSym_sym : RSym (typD ts) sym.

  Record SRW_Algo (T : Type) : Type :=
  { Rbase : Type (** Relations **)
     (** The output relation will be an instantiation of R **)
   ; properAt : expr sym -> PR Rbase -> option (R Rbase)
     (** The input relation must not have variables in it? **)
   ; atomic : tenv typ -> forall e : expr sym,
                            (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> (PR Rbase) -> option (T * (R Rbase)))
                            -> tenv typ -> R Rbase -> T
     (** ?? **)
   ; app : tenv typ -> tenv typ -> T -> T -> R Rbase -> R Rbase -> T
   ; abs : tenv typ -> tenv typ -> typ -> T -> R Rbase -> T
  }.

  Record SRW_AlgoOk (T : Type) (Algo : SRW_Algo T) : Type :=
  { typeForRbase : Algo.(Rbase) -> typ
  ; TR : env (typD ts) -> env (typD ts) -> forall r : R Algo.(Rbase), T -> typD ts nil (typeForR typeForRbase r) -> Prop
  ; Hatomic
    : forall e r r',
      Algo.(properAt) e r = Some r' ->
      instantiates typeForRbase r' r /\
      forall us vs x result (recur : forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR Algo.(Rbase)-> option (T * R Algo.(Rbase))),
        (forall tus e' tvs r r' result pf,
           recur e' pf tvs r = Some (result, r') ->
           instantiates typeForRbase r' r /\
           forall us vs x,
             WellTyped_env tus us ->
             WellTyped_env tvs vs ->
             exprD us vs e' (typeForR typeForRbase r') = Some x ->
             TR us vs r' result x) ->
        @Algo.(atomic) (typeof_env us) recur (typeof_env vs) r' = result ->
        exprD us vs e (typeForR typeForRbase r') = Some x ->
        TR us vs r' result x
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
        @TR us vs (Rpointwise t1 t2) (Algo.(abs) (typeof_env us) (typeof_env vs) t1 r1 t2) v1
  }.

  Definition setoid_rewriteI {T} (a : SRW_Algo T) : tenv typ -> tenv typ -> expr sym -> R a.(Rbase) -> option T :=
    @setoid_rewrite ts sym RSym_sym _ T a.(properAt) a.(atomic) a.(app) a.(abs).


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

(**
Section demo.
  Variable ts : types.

  Inductive sym : Type := And | Other.
  Instance RSym_sym : RSym (typD ts) sym :=
  { typeof_sym := fun s =>
                    match s with
                      | And => Some (tyArr tyProp (tyArr tyProp tyProp))
                      | Other => Some (tyArr tyProp tyProp)
                    end
  ; symD := fun s =>
              match s as s return match match s with
                                          | And => Some (tyArr tyProp (tyArr tyProp tyProp))
                                          | Other => Some (tyArr tyProp tyProp)
                                        end
                                  with
                                    | None => unit
                                    | Some t => typD ts nil t
                                  end
              with
                | And => and
                | Other => not
              end
  ; sym_eqb := fun _ _ => None
  }.
  Inductive Rbase := Impl | Eq.
  Definition typeForRbase (_ : Rbase) : typ := tyProp.
  Definition T := expr sym.

  Fixpoint RD (r : R Rbase) : relation (typD ts nil (typeForR typeForRbase r)) :=
    match r with
      | Rfunctorial l r =>
        (fun f g => forall x y, RD l x y -> RD r (f x) (g y))
      | Rinj Impl => Basics.impl
      | Rinj Eq => @eq Prop
    end.
 Import ExtLib.Core.RelDec.
  
  Local Instance RelDec_Rbase : RelDec (@eq Rbase) :=
  { rel_dec := fun a b =>
                 match a , b with
                   | Eq , Eq => true
                   | Impl , Impl => true
                   | _ , _ => false
                 end
  }.

  Fixpoint unify (r : R Rbase) (p : PR Rbase) : bool :=
    match p with
      | PRguess _ => true
      | PRinj i => match r with
                     | Rinj i' => i ?[ eq ] i'
                     | _ => false
                   end
      | PRfunctorial a b =>
        match r with
          | Rfunctorial a' b' => andb (unify a' a) (unify b' b)
          | _ => false
        end
    end.

  Fixpoint is_refl (r : PR Rbase) : bool :=
    match r with
      | PRinj _ => true
      | _ => false
    end.

  Definition properAt (f : expr sym) (r : PR Rbase) : option (R Rbase) :=
    if is_refl r then
      to_R r
    else
      let results :=
          match f with
            | Inj And => (Rfunctorial (Rinj Eq) (Rfunctorial (Rinj Eq) (Rinj Eq)) ::
                                      Rfunctorial (Rinj Impl) (Rfunctorial (Rinj Impl) (Rinj Impl)) :: nil)
            | _ => nil
          end
      in
      match filter (fun x => unify x r) results with
        | nil => None
        | r :: _ => Some r
      end.

  Definition atomic (tus : tenv typ) (e : expr sym) :
    (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> tenv typ -> PR Rbase -> option (T * R Rbase))
    -> tenv typ -> R Rbase -> T :=
    fun _ _ _ => e.

  Definition app : T -> T -> R Rbase -> R Rbase -> T :=
    fun a b _ _ => App a b.

  Definition TR (us vs : env (typD ts)) (r : R Rbase) (t : T) (v : typD ts nil (typeForR typeForRbase r)) : Prop :=
    exists v',
      exprD us vs t (typeForR typeForRbase r) = Some v' /\
      RD r v v'.

  Theorem Hatomic
  : forall e r r',
      properAt e r = Some r' ->
      instantiates typeForRbase r' r /\
      forall us vs x result,
        @atomic (typeof_env us) e (fun e _ => setoid_rewrite _ properAt atomic app (typeof_env us) e) (typeof_env vs) r' = result ->
        exprD us vs e (typeForR typeForRbase r') = Some x ->
        TR us vs r' result x.
  Proof.
    unfold TR, atomic, properAt; intros; subst.
    split.
    { admit. }
    { intros; subst.
      rewrite H1. eexists; split; eauto.
      destruct result; simpl in *; try congruence.
      admit. admit.  admit. admit. admit. }
(*
      destruct s; simpl in *; try congruence.
      destruct r; try congruence.
      { inv_all; subst. simpl.
        intros; subst; auto. }
      { red_exprD. simpl in *.
        destruct r1; simpl in *; subst.
        { destruct r; simpl in *; try congruence.
          destruct r2; try congruence. inv_all. subst; simpl; intuition.
          simpl in *. inv_all.
          admit.
          admit. admit. } admit. admit. } }
*)
  Qed.

  Theorem Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      exprD us vs f (typeForR typeForRbase (Rfunctorial t1 t2)) = Some v1 ->
      @TR us vs (Rfunctorial t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app r1 r2 t1 t2) (v1 v2).
  Proof.
    unfold TR; simpl; intuition.
    destruct H0. destruct H1. intuition.
    unfold app. red_exprD.
    cutrewrite (typeof_expr (typeof_env us) (typeof_env vs) r1 =
                Some (tyArr (typeForR typeForRbase t1) (typeForR typeForRbase t2))).
    { Cases.rewrite_all.
      rewrite typ_cast_typ_refl. eexists; split; eauto. }
    { admit. }
  Qed.

  Eval compute in
      @setoid_rewrite _ _ _ _ _ properAt atomic app nil (Inj And) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRfunctorial (PRguess _ tyProp) (PRinj Impl))).

  Eval compute in typeof_expr nil (tyProp :: nil) (App (Inj And) (Var 0)).

  Eval compute in
      @setoid_rewrite _ _ _ _ _ properAt atomic app nil (Var 0) (tyProp :: nil)
                      (PRinj Impl).

  Eval compute in
      @setoid_rewrite _ _ _ _ _ properAt atomic app nil (App (Inj And) (Var 0)) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRinj Impl)).

  Eval compute in
      @setoid_rewrite _ _ _ _ _ properAt atomic app nil (App (App (Inj And) (Var 0)) (Var 0)) (tyProp :: nil)
                      (PRinj Eq).
End demo.
**)