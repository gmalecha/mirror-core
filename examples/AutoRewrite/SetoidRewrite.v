Require Import Coq.Relations.Relations.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprTac.

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
  Variable Typ0_Prop : Typ0 _ Prop.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable Rbase : Type.
  Variable Req : Rbase -> Rbase -> bool.

  Inductive RG : Type :=
  | RGinj (r : Rbase)
  | RGrespects (l r : RG)
  | RGany.

  (** Dependent type for this? **)
  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R).

  (** This will be called on the head symbol to see what it
   ** respects
   **)
(*  Variable respects : expr typ func -> RG -> option RG. *)
(*  Variable is_reflexive : RG -> option R. *)

  Fixpoint RtoRG (r : R) : RG :=
    match r with
      | Rinj r => RGinj r
      | Rrespects l r => RGrespects (RtoRG l) (RtoRG r)
    end.

  Fixpoint RGtoR (rg : RG) : option R :=
    match rg with
      | RGinj x => Some (Rinj x)
      | RGrespects a b =>
        match RGtoR a , RGtoR b with
          | Some a , Some b => Some (Rrespects a b)
          | _ , _ => None
        end
      | _ => None
    end.

  Fixpoint unify (l r : RG) : option RG :=
    match l , r with
      | RGany , _ => Some r
      | _ , RGany => Some l
      | RGinj l , RGinj r => if Req l r then Some (RGinj l) else None
      | RGrespects la lb , RGrespects ra rb =>
        match unify la ra , unify lb rb with
          | None , _ => None
          | _ , None => None
          | Some l , Some r => Some (RGrespects l r)
        end
      | _ , _ => None
    end.

  Variable m : Type -> Type.
  Variable under : forall T, RG -> m T -> m T.
  Variable mzero : forall T, m T.
  Variable mret  : forall T, T -> m T.
  Variable mbind : forall T U, m T -> (T -> m U) -> m U.
  Variable mplus  : forall T, m T -> m T -> m T.
  Variable unify_with : nat -> RG -> m RG.

  Variable rw : expr typ func -> RG ->
                m (option (expr typ func * RG)).

  Definition setoid_rewrite : expr typ func -> RG -> m (expr typ func * RG) :=
    @Fix (expr typ func) _ (wf_rightTrans (@wf_expr_acc typ func))
         (fun _ => RG -> m (expr typ func * RG))
         (fun e rg =>
            mbind (rw e rg)
                  (fun val =>
                     match val with
                       | Some val => mret val
                       | None =>
                         match e as e
                               return (forall e', TransitiveClosure.rightTrans (@expr_acc typ func) e' e -> R -> m (expr typ func))
                                      -> R -> m (expr typ func)
                         with
                           | Inj _ => fun rvars rg =>
                                        match rw e rg with
                                          | None => mzero
                                          | Some r => mret (e, r)
                                        end
                           | Var v =>
                             mbind (unify_with v rg)
                                   (fun r => mret (Var v, r))
                           | App l r => fun recur rel =>
                                          match rw l rel with
                                            | None =>
                                              @atomic (App l r) recur rel
                                            | Some r' =>
                                              app (recur l (TransitiveClosure.RTFin _ _ _ (acc_App_l _ _))
                                                         (Rpointwise r' rel))
                                                  (recur r (TransitiveClosure.RTFin _ _ _ (acc_App_r _ _))
                                                         r')
                                          end
                           | e' => @atomic e'
                         end
                     end)).


  Definition setoid_rewrite : expr typ func -> list RG -> RG -> option (expr typ func * T :=
    @Fix (expr typ func) _ (wf_rightTrans (@wf_expr_acc typ func))
         (fun _ => R -> T)
         (fun e =>
            match e as e
               return (forall e', TransitiveClosure.rightTrans (@expr_acc typ func) e' e -> R -> T) -> R -> T
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
              | e' => @atomic e'
            end).

  Variable typeForRbase : Rbase -> typ.

  Fixpoint typeForR (r : R) : typ :=
    match r with
      | RInj r => typeForRbase r
      | Rpointwise l r => tyArr (typeForR l) (typeForR r)
    end.

  Variable TR : forall ts,
                  tenv typ -> tenv typ ->
                  forall r : R, T -> typD ts (typeForR r) -> Prop.

  Hypothesis Hatomic_rel
  : forall e f g x,
      (forall e pf x, f e pf x = g e pf x) ->
      @atomic e f x = @atomic e g x.

  Check exprD'.

  Hypothesis Hatomic
  : forall tus tvs e r x result,
      exprD' tus tvs (typeForR r) e = Some x ->
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
*)
