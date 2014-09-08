Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import MirrorCore.Util.Forwardy.
Require Import ExtLib.Data.Pair.
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
(*
  Variable respects : expr typ func -> RG -> option RG.
  Variable is_reflexive : RG -> option R.
*)

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

(*
  Definition try_reflexive (e : expr typ func)
             (rvars : list RG) (rg : RG)
  : option (expr typ func * list RG * RG) :=
    match is_reflexive rg with
      | None => None
      | Some r => Some (e, rvars, RtoRG r)
    end.
*)

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

  Variable rw : expr typ func -> list RG -> RG ->
                option (expr typ func * list RG * RG).

  Fixpoint setoid_rewrite
           (e : expr typ func) (rvars : list RG) (rg : RG)
  : option (expr typ func * list RG * RG).
  refine (
      match e with
        | Inj _ =>
          match rw e rvars rg with
            | None => None
            | Some x => Some x
          end
        | App f x =>
          match rw e rvars rg with
            | None =>
              match setoid_rewrite f rvars (RGrespects RGany rg) with
                | None => None
                | Some (f',rvars', RGrespects rD rR) =>
                  match setoid_rewrite x rvars' rD with
                    | None => None
                    | Some (x',rvars'',z) =>
                      match z with
                        | RGany => None
                        | _ => Some (App f' x', rvars'',rR)
                      end
                  end
                | _ => None (* Dead code *)
              end
            | Some x => Some x
          end
        | Abs t b =>
          match rg with
            | RGrespects l r =>
              match setoid_rewrite b (l :: rvars) r with
                | None => None
                | Some (b',lr'::rvars',r') =>
                  Some (Abs t b', rvars', RGrespects lr' r')
                | _ => None (** Dead code **)
              end
            | _ => rw e rvars rg
          end
        | Var v =>
          match nth_error rvars v with
            | None => None (** Dead code **)
            | Some r =>
              match unify r rg with
                | None => None
                | Some r' =>
                  Some (Var v,
                        firstn v rvars ++ r' :: skipn (S v) rvars,
                        r')
              end
          end
        | UVar u =>
          match rw e rvars rg with
            | None => None
            | Some r => Some r
          end
      end).
  Defined.

  Variable typeForRbase : Rbase -> typ.

  Fixpoint typeForR (r : R) : typ :=
    match r with
      | Rinj r => typeForRbase r
      | Rrespects l r => tyArr (typeForR l) (typeForR r)
    end.

  Inductive Rrefines : R -> RG -> Prop :=
  | RRGany : forall i, Rrefines i RGany
  | RRGinj : forall i, Rrefines (Rinj i) (RGinj i)
  | RRGrespects : forall l l' r r',
                    Rrefines l l' -> Rrefines r r' ->
                    Rrefines (Rrespects l r) (RGrespects l' r').

  Inductive RGtypes : RG -> typ -> Prop :=
  | RGTany : forall t, RGtypes RGany t
  | RGTinj : forall i, RGtypes (RGinj i) (typeForRbase i)
  | RGTrespects : forall r1 r2 t1 t2,
                    RGtypes r1 t1 -> RGtypes r2 t2 ->
                    RGtypes (RGrespects r1 r2) (tyArr t1 t2).

  Inductive RGlt : RG -> RG -> Prop :=
  | RGlt_inj : forall x, RGlt (RGinj x) (RGinj x)
  | RGlt_any : forall x, RGlt RGany x
  | RGlt_respectful : forall a b c d,
                        RGlt a b -> RGlt c d ->
                        RGlt (RGrespects a c) (RGrespects b d).

  Instance Transitive_RGlt : Transitive RGlt.
  Proof.
    clear. red. intros x y z H; revert z; induction H; auto.
    + intro; constructor.
    + inversion 1; subst.
      econstructor; eauto.
  Qed.

  Variable RbaseD : forall r, relation (typD nil (typeForRbase r)).

  Fixpoint RD (r : R) : relation (typD nil (typeForR r)) :=
    match r as r return relation (typD nil (typeForR r)) with
      | Rinj i => RbaseD i
      | Rrespects a b =>
        match eq_sym (typ2_cast nil (typeForR a) (typeForR b)) in _ = T return relation T with
          | eq_refl => respectful (RD a) (RD b)
        end
    end.

  (* - the term has type [t]
   * - there is a relation [r]  <----
   *)

  Inductive hlist_Forall2 T (F G : T -> Type) (R : forall t, F t -> G t -> Prop)
  : forall ts : list T, HList.hlist F ts -> HList.hlist G ts -> Prop :=
  | hlist_Forall2_nil  : @hlist_Forall2 T F G R nil HList.Hnil HList.Hnil
  | hlist_Forall2_cons : forall t ts h1 h2 x y,
     @R t x y ->
     @hlist_Forall2 T F G R ts h1 h2 ->
     @hlist_Forall2 T F G R (t :: ts) (HList.Hcons x h1) (HList.Hcons y h2).

  (** This doesn't appear to work well... **)
  (** Think about:
   ** - the denotation of a relation at a type?
   ** - it appears that i need to manifest the relation
   **   - this enables me to explicity quantify over it in the conclusion
   **     forall rels,
   **)

  Definition Hrewriter (srw : _) : Prop :=
    forall tus e rgvars rgvars' rg rg' e',
      srw e rgvars rg = Some (e', rgvars', rg') ->
      Forall2 RGlt rgvars rgvars' /\
      RGlt rg rg' /\
      (forall tvs t eD,
         RGtypes rg t ->
         Forall2 RGtypes rgvars tvs ->
         exprD' nil tus tvs t e = Some eD ->
         exists eD',
           RGtypes rg' t /\
           Forall2 RGtypes rgvars' tvs /\
           exprD' nil tus tvs t e' = Some eD' /\
           forall us vs vs',
             @hlist_Forall2 typ _ _ _ tvs vs vs' ->
             rD (eD us vs) (eD' us vs')).

  Lemma Rrefines_RGlt : forall r rg',
                          Rrefines r rg' ->
                          forall rg,
                          RGlt rg rg' ->
                          Rrefines r rg.
  Proof.
    clear. induction 1; simpl; intros.
    { inversion H. constructor. }
    { inversion H.
      + constructor.
      + constructor. }
    { inversion H1; subst.
      + constructor.
      + constructor; eauto. }
  Qed.

  Lemma Forall2_diag : forall xs ys,
                         Forall2 Rrefines xs ys ->
                         forall zs,
                           Forall2 RGlt zs ys ->
                           Forall2 Rrefines xs zs.
  Proof.
    clear. induction 1.
    { inversion 1. constructor. }
    { inversion 1; subst.
      constructor; eauto using Rrefines_RGlt. }
  Qed.

  Hypothesis Hrw : Hrewriter rw.

  Local Instance Injective_Rrefines a b c d : Injective (Rrefines (Rrespects a b) (RGrespects c d)) :=
    { result := Rrefines a c /\ Rrefines b d }.
  clear. inversion 1. subst. split; auto.
  Defined.

  Local Instance Injective_RGlt a b c d : Injective (RGlt (RGrespects a b) (RGrespects c d)) :=
    { result := RGlt a c /\ RGlt b d }.
  clear. inversion 1. subst. split; auto.
  Defined.

  Local Instance Transitive_Forall2 (A : Type) (R : A -> A -> Prop) (_ : Transitive R) : Transitive (Forall2 R).
  Proof.
    clear - H.
    red. intros x y z H'; revert z; induction H'; auto.
    inversion 1; subst.
    constructor. etransitivity; eauto.
    eapply IHH'; eauto.
  Qed.

  Theorem setoid_rewrite_sound
  : Hrewriter setoid_rewrite.
  Proof.
    induction e; simpl; intros.
    { forwardy. inv_all; subst.
      admit. }
    { admit. (* consider (rw (Inj f) rgvars rg).
      { intros. inv_all; subst.
        eapply Hrw in H2; eauto. }
      { intro X; clear X. inversion 1. } *) }
    { consider (rw (App e1 e2) rgvars rg).
      { intros. inv_all; subst.
        eapply Hrw in H. eapply H; eauto. }
      { intro X; clear X. intros; forwardy.
        destruct r; try congruence. forwardy.
        assert (exists rD, RtoRG rD = r /\
                           e' = App e e0 /\ l0 = rgvars' /\ rg' = r2).
        { (* TODO: Not true. *) admit. }
        clear H1.
        forward_reason. subst.
        eapply IHe1 in H; clear IHe1; eauto.
        forward_reason.
        eapply IHe2 in H0; clear IHe2; eauto.
        forward_reason.
        split; [ etransitivity; eauto | ].
        inv_all.
        split; [ eauto | ].
        intros. specialize (H4 rvars x).
        specialize (H2 rvars (Rrespects x r)).
        assert (Forall2 Rrefines rvars l).
        { admit. }
        forward_reason.
        autorewrite with exprD_rw in *; simpl in *; forwardy.
        inv_all; subst.
        Lemma Rrefines_RtoRG : forall r, Rrefines r (RtoRG r).
        Proof.
          induction r; simpl; try constructor; eauto.
        Qed.
        assert (y = typeForR x).
        { 


        split; [ eauto using Rrefines_RGlt | ].
        split; [ eauto using Forall2_diag | ].
        assert (Rrefines x (RtoRG x)) by eauto using Rrefines_RtoRG.
        assert (Rrefines (Rrespects x r) (RGrespects r1 r2)).
        { constructor; auto. admit. }
        forward_reason.
        inv_all.
        

        { inv_all; subst.
          unfold type_of_apply in H5.
          arrow_case_any; try congruence.
          clear H6. unfold Relim in H5.
          rewrite Data.Eq.eq_Const_eq in H5.
          red in x1. subst.
          rewrite Data.Eq.eq_Const_eq in H5.
          forwardy. inv_all; subst.
          red in y. subst.

          eapply IHe2 in H3; clear IHe2; eauto.
          Focus 2.
          forward_reason. split; eauto.
          split; auto.
          split; [ etransitivity; eauto | ].
          split; eauto.
          intros. specialize (H6 tus).
          specialize (H12 tus).
          autorewrite with exprD_rw in *.
          simpl in *. forwardy.
          inv_all; subst.
          generalize dependent e1.
          generalize dependent e2.
          



End setoid.


(*



  Definition setoid_rewrite : expr typ func -> R -> T :=
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
