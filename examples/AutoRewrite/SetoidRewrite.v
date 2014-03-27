Require Import Relations.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
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

  Inductive R : Type :=
  | RInj (r : Rbase)
  | Rpointwise (l r : R).

  Variable respects : expr sym -> R -> option R.
  Variable atomic : forall e : expr sym,
                      (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> R -> T)
                      -> R -> T.
  Variable app : T -> T -> T.
  Variable abs : typ -> T -> T.

  Definition setoid_rewrite : expr sym -> R -> T :=
    @Fix (expr sym) _ (wf_rightTrans (@wf_expr_acc sym))
         (fun _ => R -> T)
         (fun e =>
            match e as e
               return (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> R -> T) -> R -> T
            with
              | App l r => fun recur rel =>
                match respects l rel with
                  | None =>
                    @atomic (App l r) recur rel
                  | Some r' =>
                    app (recur l (TransitiveClosure.RTFin _ _ _ (acc_App_l _ _))
                               (Rpointwise r' rel))
                        (recur r (TransitiveClosure.RTFin _ _ _ (acc_App_r _ _))
                               r')
                end
(*
              | Abs t e' => fun recur rel =>
                match rel with
                  | Rpointwise l r =>
                    abs t (@recur e' (TransitiveClosure.RTFin _ _ _ (acc_Abs _ _)) r)
                  | _ => @atomic  (Abs t e') recur rel
                end
*)
              | e' => @atomic e'
            end).

  Variable typeForRbase : Rbase -> typ.

  Fixpoint typeForR (r : R) : typ :=
    match r with
      | RInj r => typeForRbase r
      | Rpointwise l r => tyArr (typeForR l) (typeForR r)
    end.

  Variable TR : env (typD ts) -> env (typD ts) -> forall r : R, T -> typD ts nil (typeForR r) -> Prop.

  Hypothesis Hatomic_rel
  : forall e f g x,
      (forall e pf x, f e pf x = g e pf x) ->
      @atomic e f x = @atomic e g x.

  Hypothesis Hatomic
  : forall us vs e r x result,
      exprD us vs e (typeForR r) = Some x ->
      @atomic e (fun e _ => setoid_rewrite e) r = result ->
      TR us vs r result x.

  Hypothesis Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      respects f t2 = Some t1 ->
      exprD us vs f (typeForR (Rpointwise t1 t2)) = Some v1 ->
      @TR us vs (Rpointwise t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app r1 r2) (v1 v2).

  Hypothesis Hrespects_typ
  : forall r r' e,
      respects e r = Some r' ->
      forall us vs t,
        typeof_expr us vs e = Some t ->
        t = (tyArr (typeForR r') (typeForR r)).

  Lemma side_condition
  : forall (x0 : expr sym)
           (f g : forall y : expr sym,
                    TransitiveClosure.rightTrans (expr_acc (func:=sym)) y x0 -> R -> T),
      (forall (y : expr sym)
              (p : TransitiveClosure.rightTrans (expr_acc (func:=sym)) y x0)
              (a : R), f y p a = g y p a) ->
      forall a : R,
        match
          x0 as e
          return
          ((forall e' : expr sym,
              TransitiveClosure.rightTrans (expr_acc (func:=sym)) e' e -> R -> T) ->
           R -> T)
        with
          | Var v0 => atomic (e:=Var v0)
          | Inj s => atomic (e:=Inj s)
          | App l r0 =>
            fun
              (recur : forall e' : expr sym,
                         TransitiveClosure.rightTrans (expr_acc (func:=sym)) e'
                                                      (App l r0) -> R -> T) (rel : R) =>
              match respects l rel with
                | Some r' =>
                  app
                    (recur l
                           (TransitiveClosure.RTFin (expr_acc (func:=sym)) l
                                                    (App l r0) (acc_App_l l r0)) (Rpointwise r' rel))
                    (recur r0
                           (TransitiveClosure.RTFin (expr_acc (func:=sym)) r0
                                                    (App l r0) (acc_App_r l r0)) r')
                | None => atomic recur rel
              end
          | Abs t e => atomic (e:=Abs t e)
          | UVar u => atomic (e:=UVar u)
        end f a =
        match
          x0 as e
          return
          ((forall e' : expr sym,
              TransitiveClosure.rightTrans (expr_acc (func:=sym)) e' e -> R -> T) ->
           R -> T)
        with
          | Var v0 => atomic (e:=Var v0)
          | Inj s => atomic (e:=Inj s)
          | App l r0 =>
            fun
              (recur : forall e' : expr sym,
                         TransitiveClosure.rightTrans (expr_acc (func:=sym)) e'
                                                      (App l r0) -> R -> T) (rel : R) =>
              match respects l rel with
                | Some r' =>
                  app
                    (recur l
                           (TransitiveClosure.RTFin (expr_acc (func:=sym)) l 
                                                    (App l r0) (acc_App_l l r0)) (Rpointwise r' rel))
                    (recur r0
                           (TransitiveClosure.RTFin (expr_acc (func:=sym)) r0 
                                                    (App l r0) (acc_App_r l r0)) r')
                | None => atomic recur rel
              end
          | Abs t e => atomic (e:=Abs t e)
          | UVar u => atomic (e:=UVar u)
        end g a.
  Proof.
    destruct x0; simpl; intros; auto.
    destruct (respects x0_1 a); auto.
    do 2 rewrite H. reflexivity.
  Qed.

  Ltac expand H :=
    rewrite (fun F => @Fix_equiv _ _ (wf_rightTrans (wf_expr_acc (func:=sym)))
                                 (fun _ : expr sym => R -> T) F
                                 (fun x y z => forall a, y a = z a)) in H by apply side_condition.

  Theorem setoid_rewrite_sound
  : forall us vs e r x result,
      exprD us vs e (typeForR r) = Some x ->
      setoid_rewrite e r = result ->
      TR us vs r result x.
  Proof.
    induction e; simpl; intros.
    { unfold setoid_rewrite in *.
      expand H0.
      simpl in *. eapply Hatomic in H0; eauto. }
    { unfold setoid_rewrite in *.
      expand H0. simpl in *.
      eapply Hatomic in H0; eauto. }
    { unfold setoid_rewrite in *.
      expand H0; simpl in *.
      consider (respects e1 r); intros.
      { progress red_exprD.
        forward; subst. inv_all; subst.
        generalize (@Hrespects_typ _ _ _ H0 _ _ _ H2).
        inversion 1; intros; subst.
        specialize (IHe1 (Rpointwise r0 r)).
        specialize (IHe2 r0).
        match goal with
          | |- context [ app ?X ?Y ] =>
            generalize dependent X ; generalize dependent Y; intros
        end.
        eapply Happ; eauto. }
      { eapply Hatomic; eauto. } }
    { unfold setoid_rewrite in *.
      expand H0. simpl in *.
      eapply Hatomic in H0; eauto. }
    { unfold setoid_rewrite in *.
      expand H0. simpl in *.
      eapply Hatomic in H0; eauto. }
  Qed.
End setoid.

Section foo.
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
      | Rpointwise l r =>
        (fun f g => forall x y, RD l x y -> RD r (f x) (g y))
      | RInj Impl => Basics.impl
      | RInj Eq => @eq Prop
    end.

  Definition respects (f : expr sym) (r : R Rbase) : option (R Rbase) :=
    match f , r with
      | App (Inj And) _ , RInj Impl => Some (RInj Impl)
      | App (Inj And) _ , RInj Eq => Some (RInj Eq)
      | Inj And , Rpointwise (RInj Impl) (RInj Impl) => Some (RInj Impl)
      | _ , _ => None
    end.

  Definition atomic (e : expr sym) :
    (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> R Rbase -> T)
    -> R Rbase -> T :=
    fun _ _ => e.

  Definition app : T -> T -> T := App.

  Definition TR (us vs : env (typD ts)) (r : R Rbase) (t : T) (v : typD ts nil (typeForR typeForRbase r)) : Prop :=
    exists v',
      exprD us vs t (typeForR typeForRbase r) = Some v' /\
      (RD r v v' \/ v = v').

  Theorem Hatomic
  : forall us vs e r x result,
      exprD us vs e (typeForR typeForRbase r) = Some x ->
      @atomic e (fun e _ => setoid_rewrite respects atomic app e) r = result ->
      TR us vs r result x.
  Proof.
    intros.
    generalize dependent ((fun (e0 : expr sym)
        (_ : TransitiveClosure.rightTrans (expr_acc (func:=sym)) e0 e) =>
      setoid_rewrite respects atomic app e0)).
    intros.
    unfold atomic in *. subst. red.
    match goal with
      | H : ?X = _ |- context [ ?Y ] =>
        change Y with X ; rewrite H
    end.
    eexists; split; eauto.
  Qed.

  Theorem Hrespects_typ
  : forall r r' e,
      respects e r = Some r' ->
      forall us vs t,
        typeof_expr us vs e = Some t ->
        t = (tyArr (typeForR typeForRbase r') (typeForR typeForRbase r)).
  Proof.
    destruct e; destruct r; simpl; intros; try congruence.
    forward.
    forward; subst. inv_all. subst. reflexivity.
    forward; subst; inv_all; subst.
    unfold type_of_apply in *.
    destruct r; inv_all; subst; inv_all; subst.
    forward. subst; inv_all; subst. reflexivity.
    forward. subst; inv_all; subst; reflexivity.
    forward.
  Qed.

  Theorem Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      respects f t2 = Some t1 ->
      exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
      @TR us vs (Rpointwise t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app r1 r2) (v1 v2).
  Proof.
    unfold app, TR; simpl; intros.
    destruct H1. destruct H2.
    destruct H1; destruct H2.
    red_exprD.
    destruct (typeof_expr_exprD _ us vs r1 (tyArr (typeForR typeForRbase t1) (typeForR typeForRbase t2))).
    unfold WellTyped_expr in H6.
(*
    rewrite H6. 2: eexists. 2: eapply H1.
    clear H5 H6. rewrite H1. rewrite H2.
    rewrite typ_cast_typ_refl.
    eexists; split; eauto.
    intuition; subst.
    { left. eapply H5.
*)
  Admitted.
End foo.