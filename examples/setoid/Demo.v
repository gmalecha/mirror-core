Require Import Relations Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.SetoidFold.

Set Implicit Arguments.
Set Strict Implicit.

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
  Inductive Rbase := Impl | Eq (t : typ).
  Definition typeForRbase (r : Rbase) : typ :=
    match r with
      | Impl => tyProp
      | Eq t => t
    end.
  Definition T := expr sym.


  Fixpoint RD (r : R Rbase) : relation (typD ts nil (typeForR typeForRbase r)) :=
    match r with
      | Rfunctorial l r =>
        (fun f g => forall x y, RD l x y -> RD r (f x) (g y))
      | Rpointwise l r =>
        (fun f g => forall x, RD r (f x) (g x))
      | Rinj Impl => Basics.impl
      | Rinj (Eq t) => @eq (typD ts nil t)
    end.

  Local Instance RelDec_Rbase : RelDec (@eq Rbase) :=
  { rel_dec := fun a b =>
                 match a , b with
                   | Eq t , Eq t' => t ?[ eq ] t'
                   | Impl , Impl => true
                   | _ , _ => false
                 end
  }.

  Fixpoint unify (r : R Rbase) (p : PR Rbase) : bool :=
    match p with
      | PRguess => true
      | PRinj i => match r with
                     | Rinj i' => i ?[ eq ] i'
                     | _ => false
                   end
      | PRfunctorial a b =>
        match r with
          | Rfunctorial a' b' => andb (unify a' a) (unify b' b)
          | _ => false
        end
      | PRpointwise a b =>
        match r with
          | Rpointwise a' b' => andb (a ?[ eq ] a') (unify b' b)
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
            | Inj And =>
              (Rfunctorial (Rinj (Eq tyProp)) (Rfunctorial (Rinj (Eq tyProp)) (Rinj (Eq tyProp))) ::
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
    -> tenv typ -> PR Rbase -> option (T * R Rbase) :=
    fun _ _ r => None.

  Definition app (a b : tenv typ) : T -> T -> R Rbase -> R Rbase -> option T :=
    fun a b _ _ => Some (App a b).

  Definition TR (us vs : env (typD ts)) (r : R Rbase) (t : T) (v : typD ts nil (typeForR typeForRbase r)) : Prop :=
    exists v',
      exprD us vs t (typeForR typeForRbase r) = Some v' /\
      RD r v v'.

(*
  Definition algo : SRW_Algo sym (expr sym) :=
    @Build_SRW_Algo sym T Rbase atomic app.

  Theorem Hatomic
  : forall e r r',
      properAt e r = Some r' ->
      instantiates r' r /\
      forall us vs x result,
        @atomic (typeof_env us) e (fun e _ => setoid_fold _ properAt atomic app (typeof_env us) e) (typeof_env vs) r' = result ->
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
      @setoid_fold _ _ _ _ _ properAt atomic app nil (Inj And) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRfunctorial (PRguess _ tyProp) (PRinj Impl))).

  Eval compute in typeof_expr nil (tyProp :: nil) (App (Inj And) (Var 0)).

  Eval compute in
      @setoid_fold _ _ _ _ _ properAt atomic app nil (Var 0) (tyProp :: nil)
                      (PRinj Impl).

  Eval compute in
      @setoid_fold _ _ _ _ _ properAt atomic app nil (App (Inj And) (Var 0)) (tyProp :: nil)
                      (PRfunctorial (PRguess _ tyProp) (PRinj Impl)).

  Eval compute in
      @setoid_fold _ _ _ _ _ properAt atomic app nil (App (App (Inj And) (Var 0)) (Var 0)) (tyProp :: nil)
                      (PRinj Eq).
*)
End demo.
