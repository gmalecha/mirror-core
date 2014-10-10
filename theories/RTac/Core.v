Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Move to Data.Hlist **)
Theorem rev_app_distr_trans
: forall (A : Type) (x y : list A), rev (x ++ y) = rev y ++ rev x.
Proof. clear.
       induction x; simpl; intros.
       - symmetry. apply app_nil_r_trans.
       - rewrite IHx. apply app_ass_trans.
Defined.

(** TODO: This is cubic! **)
Theorem rev_involutive_trans (A : Type)
: forall (l : list A), rev (rev l) = l.
Proof. clear.
       induction l; simpl; auto.
       rewrite rev_app_distr_trans. rewrite IHl. reflexivity.
Defined.

Definition hlist_unrev {T} {F : T -> Type} {ls} (h : hlist F (rev ls))
: hlist F ls :=
  match rev_involutive_trans ls in _ = t return hlist F t with
    | eq_refl => hlist_rev h
  end.


(** TODO: Move to Data.Prop **)
Lemma impl_iff
: forall P Q R S : Prop,
    (P <-> R) ->
    (P -> (Q <-> S)) ->
    ((P -> Q) <-> (R -> S)).
Proof. clear. intuition. Qed.

Lemma and_iff
: forall P Q R S : Prop,
    (P <-> R) ->
    (P -> (Q <-> S)) ->
    ((P /\ Q) <-> (R /\ S)).
Proof. clear; intuition. Qed.

(** TODO: Move to Data.Pair *)
Section Eqpair.
  Context {T U} (rT : relation T) (rU : relation U).

  Inductive Eqpair : relation (T * U) :=
  | Eqpair_both : forall a b c d, rT a b -> rU c d -> Eqpair (a,c) (b,d).

  Global Instance Reflexive_Eqpair {RrT : Reflexive rT} {RrU : Reflexive rU}
  : Reflexive Eqpair.
  Proof. red. destruct x. constructor; reflexivity. Qed.

  Global Instance Symmetric_Eqpair {RrT : Symmetric rT} {RrU : Symmetric rU}
  : Symmetric Eqpair.
  Proof. red. inversion 1; constructor; symmetry; assumption. Qed.

  Global Instance Transitive_Eqpair {RrT : Transitive rT} {RrU : Transitive rU}
  : Transitive Eqpair.
  Proof. red. inversion 1; inversion 1; constructor; etransitivity; eauto. Qed.

  Global Instance Injective_Eqpair a b c d : Injective (Eqpair (a,b) (c,d)) :=
  { result := rT a c /\ rU b d }.
  abstract (inversion 1; auto).
  Defined.
End Eqpair.

Instance Injective_Roption_None T (R : T -> T -> Prop) : Injective (Roption R None None) :=
  { result := True }.
auto.
Defined.
Instance Injective_Roption_None_Some T (R : T -> T -> Prop) a : Injective (Roption R None (Some a)) :=
  { result := False }.
inversion 1.
Defined.
Instance Injective_Roption_Some_None T (R : T -> T -> Prop) a : Injective (Roption R (Some a) None) :=
  { result := False }.
inversion 1.
Defined.
Instance Injective_Roption_Some_Some T (R : T -> T -> Prop) a b : Injective (Roption R (Some a) (Some b)) :=
  { result := R a b }.
inversion 1. auto.
Defined.


Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Inductive Goal :=
  | GAll    : typ -> Goal -> Goal
  (** The first element in the list has the lowest index
   ** in the final goal.
   **)
  | GExs    : list (typ * option expr) -> Goal -> Goal
  | GHyp    : expr -> Goal -> Goal
  | GConj_  : Goal -> Goal -> Goal
  | GGoal   : expr -> Goal
  | GSolved : Goal.

  Definition GAlls (ts : list typ) (g : Goal) : Goal :=
    fold_right (fun x y => GAll x y) g ts.

  Definition GEx (t : typ) (e : option expr) (g : Goal) : Goal :=
    match g with
      | GExs tes g' => GExs ((t,e) :: tes) g'
      | _ => GExs ((t, e) :: nil) g
    end.

  Definition GConj l r : Goal :=
    match l with
      | GSolved => r
      | _ => match r with
               | GSolved => l
               | _ => GConj_ l r
             end
    end.

  Fixpoint GConj_list (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | g :: nil => g
      | g :: gs => GConj_ g (GConj_list gs)
    end.

  Fixpoint GConj_list_filter (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | GSolved :: gs => GConj_list gs
      | g :: gs => GConj g (GConj_list gs)
    end.

  Inductive Ctx :=
  | CTop
  | CAll : Ctx -> typ -> Ctx
  | CExs : Ctx -> list typ -> Ctx
  | CHyp : Ctx -> expr -> Ctx.

  Fixpoint CEx (c : Ctx) (t : typ) : Ctx :=
    CExs c (t :: nil).

  Fixpoint CAlls (c : Ctx) (ls : list typ) : Ctx :=
    match ls with
      | nil => c
      | l :: ls => CAlls (CAll c l) ls
    end.

  (** StateT subst Option Goal **)
  Inductive Result :=
  | Fail
  | More_  : subst -> Goal -> Result
  | Solved : subst -> Result.

  Definition More (s : subst) (g : Goal) : Result :=
    match g with
      | GSolved => Solved s
      | _ => More_ s g
    end.

  Definition fromResult (r : Result) : option (subst * Goal) :=
    match r with
      | Fail => None
      | More_ s g => Some (s, g)
      | Solved s => Some (s, GSolved)
    end.

  Definition DEAD : Result.
    exact Fail.
  Qed.

  (** Treat this as opaque! **)
  Definition rtac : Type :=
    Ctx -> subst -> Goal -> Result.

  (** Auxiliary Functions **)
  Fixpoint countVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CAll ctx' t => S (countVars ctx')
      | CExs ctx' _
      | CHyp ctx' _ => countVars ctx'
    end.

  Fixpoint countUVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CExs ctx' ts => length ts + countUVars ctx'
      | CAll ctx' _
      | CHyp ctx' _ => countUVars ctx'
    end.

  Fixpoint getUVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' _ => getUVars ctx'
      | CExs ctx' ts => getUVars ctx' ++ ts
      | CHyp ctx' _ => getUVars ctx'
    end.

  Fixpoint getVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' t => getVars ctx' ++ t :: nil
      | CExs ctx' _ => getVars ctx'
      | CHyp ctx' _ => getVars ctx'
    end.

  Lemma countVars_getVars : forall ctx, countVars ctx = length (getVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Lemma countUVars_getUVars : forall ctx, countUVars ctx = length (getUVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Fixpoint getEnvs' (ctx : Ctx) (tus tvs : tenv typ)
  : tenv typ * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CExs ctx' ts => getEnvs' ctx' (ts ++ tus) tvs (** TODO: Check **)
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv typ * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Fixpoint Ctx_append (c1 c2 : Ctx) : Ctx :=
    match c2 with
      | CTop => c1
      | CAll ctx' t => CAll (Ctx_append c1 ctx') t
      | CExs ctx' ts => CExs (Ctx_append c1 ctx') ts
      | CHyp ctx' h => CHyp (Ctx_append c1 ctx') h
    end.

  Theorem getUVars_append
  : forall c1 c2,
      getUVars (Ctx_append c1 c2) = getUVars c1 ++ getUVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.

  Theorem getVars_append
  : forall c1 c2,
      getVars (Ctx_append c1 c2) = getVars c1 ++ getVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.
  (** End: Auxiliary Functions **)


  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Fixpoint hlist_mapT {T : Type} {F : T -> Type}
           {ls : list T} (h : HList.hlist (fun x => option (F x)) ls)
  : option (hlist F ls) :=
    match h in hlist _ ls return option (hlist F ls) with
      | Hnil => Some (Hnil)
      | Hcons _ _ x y =>
        match x , hlist_mapT y with
          | Some x , Some y => Some (Hcons x y)
          | _ , _ => None
        end
    end.

  Section with_T.
    Context {T : Type}.
    Variables (b : T) (c : list T).

    Fixpoint nth_after' a  : nth_error (a ++ b :: c) (length a) = Some b :=
      match a as a return nth_error (a ++ b :: c) (length a) = Some b with
        | nil => eq_refl
        | x :: xs => nth_after' xs
      end.
  End with_T.
  Definition nth_after T a b c := @nth_after' T b c a.

  Definition hlist_get_cons_after_app {T : Type} {F : T -> Type} {t} {a b : list T}
             (h : hlist F (a ++ t :: b)) : F t :=
    (match nth_after a t b in _ = T return match T with
                                             | None => unit
                                             | Some x => F x
                                           end
     with
       | eq_refl => hlist_nth h (length a)
     end).

  Fixpoint goal_substD (tus tvs : list typ) (tes : list (typ * option expr))
  : option (exprT (tus ++ map fst tes) tvs Prop) :=
    match tes as tes return option (exprT (tus ++ map fst tes) tvs Prop) with
      | nil => Some (fun _ _ => True)
      | (t,None) :: tes =>
        match app_ass_trans tus (t :: nil) (map fst tes) in _ = t
              return option (exprT _ tvs Prop) ->
                     option (exprT t tvs Prop)
        with
          | eq_refl => fun x => x
        end (goal_substD (tus ++ t :: nil) tvs tes)
      | (t,Some e) :: tes =>
        match exprD' (tus ++ t :: map fst tes) tvs e t
            , goal_substD (tus ++ t :: nil) tvs tes
        with
          | Some eD , Some sD =>
            Some (match eq_sym (app_ass_trans tus (t :: nil) (map fst tes)) in _ = t
                        return exprT t tvs Prop -> exprT _ tvs Prop
                  with
                    | eq_refl => fun sD =>
                      fun us vs => sD us vs /\
                                   hlist_get_cons_after_app us = eD us vs
                  end sD)
          | _ , _ => None
        end
    end.

  (** NOTE:
   ** Appending the newly introduced terms makes tactics non-local.
   ** Requiring globalness seems bad.
   ** - The alternative, however, is to expose a lot more operations
   **   on substitute
   **)
  Fixpoint goalD (tus tvs : list typ) (goal : Goal) {struct goal}
  : option (exprT tus tvs Prop) :=
    match goal with
      | GAll tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => _foralls typD (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tes goal' =>
        let tus_ext := map fst tes in
        match goalD (tus ++ tus_ext) tvs goal'
            , goal_substD tus tvs tes with
          | None , _ => None
          | Some _ , None => None
          | Some D , Some sD =>
            Some (fun us vs => _exists typD tus_ext
                                        (fun us' => sD (HList.hlist_app us us') vs
                                                    /\ D (HList.hlist_app us us') vs))
        end
      | GHyp hyp' goal' =>
        match mapT (T:=list) (F:=option) (propD tus tvs) (hyp' :: nil) with
          | None => None
          | Some hs =>
            match goalD tus tvs goal' with
              | None => None
              | Some D =>
                Some (fun us vs => _impls (map (fun x => x us vs) hs) (D us vs))
            end
        end
      | GConj_ l r =>
        match goalD tus tvs l
            , goalD tus tvs r
        with
          | Some lD , Some rD => Some (fun us vs => lD us vs /\ rD us vs)
          | _ , _ => None
        end
      | GSolved => Some (fun _ _ => True)
      | GGoal goal' => propD tus tvs goal'
    end.

  Lemma goalD_conv
  : forall tus tvs tus' tvs' (pfu : tus' = tus) (pfv : tvs' = tvs),
      goalD tus tvs =
      match pfu in _ = t
            return Goal -> option (HList.hlist _ t -> _) with
        | eq_refl =>
          match pfv in _ = t
                return Goal -> option (_ -> HList.hlist _ t -> _) with
            | eq_refl => goalD tus' tvs'
          end
      end.
  Proof.
    clear. destruct pfu; destruct pfv. reflexivity.
  Qed.

  Fixpoint forgets (from : nat) (ts : list typ) (s : subst)
  : subst * list (typ * option expr) :=
    match ts with
      | nil => (s,nil)
      | t :: ts =>
        let '(s',rr) := forgets (S from) ts s in
        let '(s'',ne) := forget from s' in
        (s'',(t,ne) :: rr)
    end.

  Theorem forgets_map_fst : forall ts from s,
                              map fst (snd (forgets from ts s)) = ts.
  Proof.
    clear.
    induction ts; simpl; auto.
    intros. specialize (IHts (S from) s).
    destruct (forgets (S from) ts s).
    destruct (forget from s0).
    simpl. f_equal. assumption.
  Defined.

  Fixpoint remembers (from : nat) (tes : list (typ * option expr)) (s : subst)
  : option subst :=
    match tes with
      | nil => Some s
      | (_,None) :: tes' => remembers (S from) tes' s
      | (_,Some e) :: tes' =>
        match set from e s with
          | None => None
          | Some s' => remembers from tes' s'
        end
    end.

  Fixpoint pctxD (tus tvs : tenv typ) (ctx : Ctx) (s : subst)
           {struct ctx}
  : option (subst *
            (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
             -> exprT tus tvs Prop)) :=
    match ctx as ctx
          return option (subst *
                         (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                          -> exprT tus tvs Prop))
    with
      | CTop =>
        Some (s, fun k us vs => k (hlist_app us Hnil) (hlist_app vs Hnil))
(*        match substD tus tvs s with
          | None => None
          | Some sD =>
            Some (fun k us vs => sD us vs /\ k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
*)
      | CAll ctx' t =>
(*        if strengthenV (length (tvs ++ getVars ctx')) 1 s then *)
          match pctxD tus tvs ctx' s with
            | Some (s,cD) =>
              Some (s,
                    fun k : exprT _ _ Prop =>
                      cD (fun us vs =>
                            forall x : typD t,
                              k us
                                match
                                  app_ass_trans tvs (getVars ctx') (t :: nil) in (_ = t0)
                                  return (hlist typD t0)
                                with
                                  | eq_refl => hlist_app vs (Hcons x Hnil)
                                end))
            | None => None
          end
(*        else
          None *)
      | CExs ctx' ts =>
        match forgets (length (tus ++ getUVars ctx')) ts s as Z
              return map fst (snd Z) = ts -> _
        with
          | (s',tes) => fun pf =>
            match goal_substD (tus ++ getUVars ctx') (tvs ++ getVars ctx') tes
                , pctxD tus tvs ctx' s'
            with
              | Some sD , Some (s'',cD) =>
                Some (s'',
                      fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                        cD (fun us vs =>
                              _foralls typD ts (fun us' =>
                                                 sD (hlist_app us match eq_sym pf in _ = t return hlist _ t with
                                                                    | eq_refl => us'
                                                                  end) vs ->
                                                 k match
                                                     app_ass_trans tus _ ts in (_ = t0)
                                                     return (hlist typD t0)
                                                   with
                                                     | eq_refl => hlist_app us us'
                                                   end
                                                   vs)))
              | _ , _ => None
            end
        end (forgets_map_fst _ _ _)
      | CHyp ctx' h =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match pctxD tus tvs ctx' s with
                         | None => None
                         | Some (s',cD) =>
                           Some (s',fun k : exprT _ _ Prop =>
                                      cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

  Definition subst_ctxD {T} {tus tvs} (v : option (subst * (T -> exprT tus tvs Prop)))
  : option (T -> exprT tus tvs Prop) :=
    match v with
      | None => None
      | Some (s,D) =>
        match substD tus tvs s with
          | None => None
          | Some sD => Some (fun k us vs => sD us vs /\ D k us vs)
        end
    end.

  Definition subst_pctxD {T} {tus tvs} (v : option (subst * (T -> exprT tus tvs Prop)))
  : option (T -> exprT tus tvs Prop) :=
    match v with
      | None => None
      | Some (s,D) =>
        match substD tus tvs s with
          | None => None
          | Some sD => Some (fun k us vs => sD us vs -> D k us vs)
        end
    end.

  Definition RCtx {tus tvs tus' tvs'} :=
    (RexprT tus tvs Basics.impl ==> RexprT tus' tvs' Basics.impl)%signature.

  Definition rtac_spec tus tvs ctx s g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match subst_ctxD (pctxD tus tvs ctx s)
            , goalD _ _ g
            , subst_ctxD (pctxD tus tvs ctx s')
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            forall us vs,
              cD' (fun _ _ => True) us vs -> cD gD us vs
        end
      | More_ s' g' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match subst_ctxD (pctxD tus tvs ctx s)
            , goalD _ _ g
            , subst_ctxD (pctxD tus tvs ctx s')
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            forall us vs, cD' gD' us vs -> cD gD us vs
        end
    end.

  Local Existing Instance Transitive_Roption.
  Local Existing Instance Symmetric_Roption.
  Local Existing Instance Reflexive_Roption.
  Local Existing Instance Transitive_RexprT.
  Local Existing Instance Symmetric_RexprT.
  Local Existing Instance Reflexive_RexprT.

  Definition EqGoal tus tvs : relation Goal :=
    fun g1 g2 =>
        Roption (RexprT tus tvs iff)
                (goalD tus tvs g1)
                (goalD tus tvs g2).

  Instance Reflexive_EqGoal tus tvs : Reflexive (EqGoal tus tvs).
  Proof. red. red. reflexivity. Qed.
  Instance Transitive_EqGoal tus tvs : Transitive (EqGoal tus tvs).
  Proof.
    red. unfold EqGoal. intros.
    etransitivity; eauto.
  Qed.
  Instance Symmetric_EqGoal tus tvs : Symmetric (EqGoal tus tvs).
  Proof.
    red; unfold EqGoal. intros.
    symmetry. eauto.
  Qed.

  Definition EqResult tus tvs : relation Result :=
    fun r1 r2 =>
      Roption (Eqpair (@eq _) (EqGoal tus tvs))
              (fromResult r1) (fromResult r2).

  Instance Reflexive_EqResult tus tvs : Reflexive (EqResult tus tvs).
  Proof.
    red. red. intros. destruct (fromResult x); try constructor; reflexivity.
  Qed.
  Instance Symmetric_EqResult tus tvs : Symmetric (EqResult tus tvs).
  Admitted.
  Instance Transitive_EqResult tus tvs : Transitive (EqResult tus tvs).
  Admitted.

  Theorem Proper_pctxD
  : forall tus tvs c1 s,
      Proper (Roption (Eqpair (@eq _)
                              (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) iff ==>
                                      (RexprT tus tvs iff))))%signature
             (pctxD tus tvs c1 s).
  Proof.
    induction c1; simpl; intros.
    { constructor.
      constructor. reflexivity.
      red. unfold RexprT, OpenTeq, OpenTrel.
      intros. eapply H.
      apply equiv_eq_eq in H0; subst; reflexivity.
      apply equiv_eq_eq in H1; subst; reflexivity. }
    { admit. }
    { admit. }
    { admit. }
  Qed.

  Theorem Proper_pctxD_impl
  : forall tus tvs c1 s,
      Proper (Roption (Eqpair (@eq _)
                              (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) Basics.impl ==>
                                      (RexprT tus tvs Basics.impl))))%signature
             (pctxD tus tvs c1 s).
  Proof.
    induction c1; simpl; intros.
    { constructor.
      constructor. reflexivity.
      red. unfold RexprT, OpenTeq, OpenTrel.
      intros. eapply H.
      apply equiv_eq_eq in H0; subst; reflexivity.
      apply equiv_eq_eq in H1; subst; reflexivity. }
    { admit. }
    { admit. }
    { admit. }
  Qed.


  Theorem rtac_spec_respects tus tvs ctx s
  : Proper (EqGoal (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==>
            EqResult (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==> iff)
           (rtac_spec tus tvs ctx s).
  Proof.
    red. red. red.
    unfold rtac_spec.
    unfold EqGoal.
    unfold EqResult.
    intros. unfold subst_ctxD.
    inversion H0; clear H0.
    { destruct x0; simpl in *; try congruence.
      destruct y0; simpl in *; try congruence.
      reflexivity. }
    { destruct x0; simpl in *; try congruence;
      destruct y0; simpl in *; try congruence; inv_all; subst;
      inversion H3; clear H3; subst;
      repeat match goal with
               | |- (_ -> _) <-> (_ -> _) =>
                 apply impl_iff; [ reflexivity | intro ]
               | |- (_ /\ _) <-> (_ /\ _) =>
                 apply and_iff; [ reflexivity | intro ]
             end.
      { red in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        apply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H17. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H23. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H16. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H22. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H16. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H22. assumption. reflexivity. reflexivity. } }
      { red in H6.
        simpl in H6.
        generalize (Proper_pctxD tus tvs ctx s).
        generalize (Proper_pctxD tus tvs ctx s1).
        destruct (pctxD tus tvs ctx s); try reflexivity.
        destruct p.
        destruct (substD tus tvs s0); try reflexivity.
        inversion H; try reflexivity.
        destruct (pctxD tus tvs ctx s1); try reflexivity.
        destruct p.
        destruct (substD tus tvs s2); try reflexivity.
        inversion H6; clear H6; try reflexivity.
        inversion 1; inversion 1; subst.
        inversion H11; inversion H15; subst.
        do 2 (apply forall_iff; intro).
        eapply impl_iff.
        { apply and_iff. reflexivity. intro.
          eapply H14. assumption. reflexivity. reflexivity. }
        { intro. apply and_iff. reflexivity. intro.
          eapply H21. assumption. reflexivity. reflexivity. } } }
  Qed.

  Lemma More_More_ tus tvs :
    (@eq subst ==> EqGoal tus tvs ==> EqResult tus tvs)%signature
                                                       More More_.
  Proof.
    red. red. red.
    simpl. intros; subst.
    destruct x0; simpl; repeat constructor; assumption.
  Qed.

  Inductive GConj_rel : Goal -> Goal -> Goal -> Prop :=
  | GConjL : forall x, GConj_rel GSolved x x
  | GConjR : forall x, GConj_rel x GSolved x
  | GConjLR : forall x y, GConj_rel x y (GConj_ x y).

  Lemma GConj_rel_sound
  : forall tus tvs g1 g2 g,
      GConj_rel g1 g2 g ->
      (EqGoal tus tvs)%signature (GConj_ g1 g2) g.
  Proof.
    clear. inversion 1; subst; red; simpl.
    - destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite And_comm. rewrite And_True_iff.
      apply equiv_eq_eq in H0; apply equiv_eq_eq in H1; subst; reflexivity.
    - destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite And_True_iff.
      apply equiv_eq_eq in H0; apply equiv_eq_eq in H1; subst; reflexivity.
    - reflexivity.
  Qed.

  Lemma GConj_GConj_rel : forall g1 g2, GConj_rel g1 g2 (GConj g1 g2).
  Proof.
    intros; destruct g1; destruct g2; simpl; try constructor.
  Qed.

  Lemma GConj_GConj_ tus tvs :
    (EqGoal tus tvs ==> EqGoal tus tvs ==> EqGoal tus tvs)%signature GConj GConj_.
  Proof.
    unfold EqGoal, respectful; simpl.
    intros.
    etransitivity.
    - symmetry. eapply GConj_rel_sound. eapply (GConj_GConj_rel x x0).
    - simpl. inversion H; try reflexivity.
      inversion H0; try reflexivity.
      constructor.
      do 5 red.
      intros. eapply and_iff. eapply H3; eauto.
      intro; eapply H6; eauto.
  Qed.

  Definition rtac_sound (tus tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      rtac_spec tus tvs ctx s g result.

  Definition CtxMorphism {tus tvs tus' tvs'} (c1 c2 : exprT tus tvs Prop -> exprT tus' tvs' Prop) : Prop :=
    forall P Q : exprT _ _ Prop,
      (** TODO: Is this the right binding for [forall] **)
      forall us vs, c1 (fun us vs => P us vs -> Q us vs) us vs -> c1 P us vs -> c2 Q us vs.

  Theorem Applicative_pctxD
  : forall tus tvs ctx s p,
      subst_ctxD (pctxD tus tvs ctx s) = Some p ->
      forall us vs (P Q : exprT _ _ Prop),
        p (fun a b => P a b -> Q a b) us vs ->
        p P us vs ->
        p Q us vs.
  Proof.
    clear. induction ctx; simpl; intros.
    { forward; inv_all; subst.
      forward_reason; split; eauto. }
    { specialize (IHctx s).
      unfold subst_ctxD in *.
      forward; inv_all; subst.
      specialize (IHctx _ eq_refl).
      rewrite H7 in *. inv_all; subst.
      eapply IHctx.
      2: eapply H1.
      clear - H0 H5.
      forward_reason; split; auto.
      generalize (Proper_pctxD_impl tus tvs ctx s).
      rewrite H5.
      intro XXX; inversion XXX; clear XXX; subst.
      inversion H3; clear H3; subst.
      eapply H8. 4: eapply H0. 2: reflexivity. 2: reflexivity.
      clear.
      do 6 red. intros.
      eapply equiv_eq_eq in H; eapply equiv_eq_eq in H0; subst.
      eauto. }
    { generalize dependent (forgets_map_fst l (length (tus ++ getUVars ctx)) s).
      unfold subst_ctxD in *.
      forward; inv_all; subst.
      simpl in *.
      specialize (IHctx s0).
      revert IHctx. Cases.rewrite_all_goal. intros.
      specialize (IHctx _ eq_refl).
      simpl in *.
      generalize (Proper_pctxD_impl tus tvs ctx s0).
      Cases.rewrite_all_goal.
      intros. red in H2.
      inv_all.
      eapply IHctx; clear IHctx; [ | eapply H0 ].
      simpl.
      forward_reason; split; auto.
      eapply H6. 4: eapply H2. 2: reflexivity. 2: reflexivity.
      clear. do 6 red. intros.
      eapply equiv_eq_eq in H; eapply equiv_eq_eq in H0; subst.
      eapply _forall_sem.
      intros.
      eapply _forall_sem in H2.
      eapply _forall_sem in H1.
      specialize (H2 H).
      specialize (H1 H).
      eauto. }
    { specialize (IHctx s).
      unfold subst_ctxD in *.
      forward; inv_all; subst.
      specialize (IHctx _ eq_refl).
      simpl in *.
      rewrite H3 in *. inv_all. subst.
      eapply IHctx; clear IHctx; [ | eapply H1 ].
      forward_reason; split; auto.
      generalize (Proper_pctxD_impl tus tvs ctx s).
      rewrite H6.
      intro XXX; inversion XXX; clear XXX; subst.
      inv_all.
      eapply H7. 4: eapply H4. 2: reflexivity. 2: reflexivity.
      clear.
      do 6 red. intros.
      eapply equiv_eq_eq in H; eapply equiv_eq_eq in H0; subst.
      eauto. }
  Qed.

  Definition rtac_local_spec tus tvs ctx s g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match subst_pctxD (pctxD tus tvs ctx s)
            , goalD _ _ g
            , subst_pctxD (pctxD tus tvs ctx s')
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            CtxMorphism cD' cD /\
            forall us vs,
(*
              cD' (fun _ _ => True) us vs -> cD gD us vs
*)
              cD' gD us vs
        end
      | More_ s' g' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match subst_pctxD (pctxD tus tvs ctx s)
            , goalD _ _ g
            , subst_pctxD (pctxD tus tvs ctx s')
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            CtxMorphism cD' cD /\
(*             forall us vs, cD' gD' us vs -> cD gD us vs *)
            forall us vs, cD' (fun us vs => gD' us vs -> gD us vs) us vs
        end
    end.

  Section runOnGoals'.
    Variable tac : Ctx -> subst -> expr -> Result.

    Fixpoint runOnGoals' (nus nvs : nat) (ctx : Ctx) (s : subst) (g : Goal)
             {struct g}
    : Result :=
      match g with
        | GGoal e => tac ctx s e
        | GSolved => Solved s
        | GAll t g =>
          match runOnGoals' nus (S nvs) (CAll ctx t) s g with
            | Fail => Fail
            | Solved s => Solved s
            | More_ s g => More s (GAll t g)
          end
        | GExs tes g =>
          match remembers nus tes s with
            | None => Fail
            | Some s' =>
              match runOnGoals' (length tes + nus) nvs (CExs ctx (map fst tes)) s' g with
                | Fail => Fail
                | Solved s'' =>
                  Fail
                | More_ s'' g' =>
                  Fail
              end
          end
        | GHyp h g =>
          match runOnGoals' nus nvs (CHyp ctx h) s g with
            | Fail => Fail
            | Solved s => Solved s
            | More_ s g => More_ s (GHyp h g)
          end
        | GConj_ l r =>
          match runOnGoals' nus nvs ctx s l with
            | Fail => Fail
            | Solved s' => runOnGoals' nus nvs ctx s' r
            | More_ s' g' =>
              match runOnGoals' nus nvs ctx s' r with
                | Fail => Fail
                | Solved s'' => More s'' g'
                | More_ s'' g'' => More s'' (GConj_ g' g'')
              end
          end
      end.



(*
    Instance Transitive_CtxMorphism a b c d : Transitive (@CtxMorphism a b c d).
    Proof.
      clear. red. red. intuition.
      specialize (H1 us vs).
      red
      eapply H0. 2: eapply H. 3: eassumption.
      eapply H1. auto.
    Qed.
*)

    Lemma onLeft {tus tvs tus' tvs'}
          (c c' : exprT tus' tvs' Prop -> exprT tus tvs Prop)
          (P Q P' : exprT _ _ Prop)
    : forall
        (Hap : forall (P Q : exprT _ _ Prop) us vs,
                 c (fun us vs => P us vs -> Q us vs) us vs ->
                 c P us vs -> c Q us vs)
        (Hpure : forall (P : exprT _ _ Prop) us vs,
                   (forall us vs, P us vs) ->
                   c P us vs)
        (Hpure' : forall (P : exprT _ _ Prop) us vs,
                    (forall us vs, P us vs) ->
                    c' P us vs)
        (Hf : forall us vs,
                c' (fun us vs => P' us vs -> P us vs) us vs)
        (Hinj : CtxMorphism c' c),
      forall us vs,
        c (fun us vs => P' us vs /\ Q us vs -> P us vs /\ Q us vs) us vs.
    Proof.
      clear; intros.
      eapply Hap.
      instantiate (1 := fun us vs => P' us vs -> P us vs); simpl.
      eapply Hpure. intros. tauto.
      eapply Hinj. 2: eapply Hf. simpl.
      eapply Hpure'. intros; tauto.
    Qed.

    Lemma onLeft_subst {tus tvs tus' tvs'} (s s' : exprT tus tvs Prop)
          (c c' : exprT tus' tvs' Prop -> exprT tus tvs Prop)
          (P Q P' : exprT _ _ Prop)
    : forall
        (Hap : forall (P Q : exprT _ _ Prop) us vs,
                 s us vs /\ c (fun us vs => P us vs -> Q us vs) us vs ->
                 s us vs /\ c P us vs -> s us vs /\ c Q us vs)
        (Hpure : forall (P : exprT _ _ Prop) us vs,
                   (forall us vs, P us vs) ->
                   c P us vs)
        (Hpure' : forall (P : exprT _ _ Prop) us vs,
                    (forall us vs, P us vs) ->
                    c' P us vs)
        (Hss' : forall us vs, s' us vs -> s us vs)
        (Hinj : CtxMorphism (fun k us vs => s' us vs /\ c' k us vs)
                            (fun k us vs => s us vs /\ c k us vs)),
      forall us vs,
        s' us vs /\ c' (fun us vs => P' us vs -> P us vs) us vs ->
        s us vs /\ c (fun us vs => P' us vs /\ Q us vs -> P us vs /\ Q us vs) us vs.
    Proof.
      clear; intros ? ? ? ? ? us vs Hf.
      pose (proj1 Hf).
      eapply Hap.
      instantiate (1 := fun us vs => P' us vs -> P us vs); simpl.
      split. apply (Hss' _ _ s0).
      eapply Hpure. clear. intros. tauto.
      eapply Hinj. 2: eapply Hf. simpl.
      split; eauto.
    Qed.

    Definition runOnGoals (tus : tenv typ) (tvs : tenv typ)
               (ctx : Ctx) (s : subst) (g : Goal)
    : Result :=
      runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx) ctx s g.

    Theorem Proper_subst_pctxD_impl
    : forall tus tvs c1 s,
        Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) Basics.impl ==>
                                (RexprT tus tvs Basics.impl)))%signature
               (subst_pctxD (pctxD tus tvs c1 s)).
    Proof.
      intros. unfold subst_pctxD.
      generalize (Proper_pctxD_impl tus tvs c1 s).
      inversion 1. red. constructor.
      destruct x.
      destruct (substD tus tvs s0); try constructor.
      subst. inversion H2; subst; eauto.
      do 7 red. intros.
      eapply H7; eauto.
      apply equiv_eq_eq in H3; apply equiv_eq_eq in H4; subst.
      auto.
    Qed.

    Theorem Applicative_subst_pctxD
    : forall tus tvs ctx s p,
        subst_pctxD (pctxD tus tvs ctx s) = Some p ->
        (forall us vs (P Q : exprT _ _ Prop),
           p (fun a b => P a b -> Q a b) us vs ->
           p P us vs ->
           p Q us vs) /\
        (forall us vs (P : exprT _ _ Prop),
           (forall a b, P a b) -> p P us vs).
    Proof.
      clear. induction ctx; simpl; intros.
      { forward; inv_all; subst.
        forward_reason; split; eauto. }
      { specialize (IHctx s).
        unfold subst_pctxD in *.
        forward; inv_all; subst.
        specialize (IHctx _ eq_refl).
        destruct IHctx as [ Hap Hpure ].
        rewrite H5 in *; subst; inv_all; subst.
        split.
        { intros. revert H1.
          eapply Hap. 2: eapply H0.
          eapply Hap. 2: eapply H.
          eapply Hpure. intros.
          eapply H1. eauto. }
        { intros. revert H0.
          eapply Hap. 2: eapply Hpure.
          eapply Hpure. intros a b X. eapply X.
          simpl. eauto. } }
      { admit. }
      { admit. }
    Qed.

    Theorem runOnGoals'_sound
    : forall tus tvs,
        (forall ctx s ge result,
           tac ctx s ge = result ->
           rtac_local_spec tus tvs ctx s (GGoal ge) result) ->
        forall g ctx s,
          rtac_local_spec tus tvs ctx s g (runOnGoals' (length tus + countUVars ctx)
                                                       (length tvs + countVars ctx)
                                                       ctx s g).
    Proof.
(*
      red. intros tus tvs Htac.
      induction g; fold runOnGoals' in *.
      { (* All *)
        intros.
        specialize (IHg (CAll ctx t) s).
        simpl in *.
        match goal with
          | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X
        end; [ | f_equal ; omega ].
        destruct (runOnGoals' (length tus + countUVars ctx)
                              (length tvs + S (countVars ctx)) (CAll ctx t) s g);
          auto; intros; forward_reason; split; auto.
        { generalize (Proper_subst_pctxD_impl tus tvs ctx s).
          forward.
          unfold subst_pctxD in *.
          revert H7. Cases.rewrite_all_goal.
          forward. subst.
          red in H6.
          inv_all; subst.
          simpl in *.
          rewrite H12 in H16. inv_all; subst.
          Cases.rewrite_all_goal.
          destruct H10.
          split.
          { red; intros.
            revert H11. red in H1.
            specialize (H1 (fun a b => forall x, P a (hlist_app b (Hcons x Hnil)))).
            
            
 }
        { admit. } }
      { admit. }
      { admit. }
      { simpl; intros; clear Htac.
        specialize (IHg1 ctx s).
        rename g1 into A.
        rename g2 into B.
        destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                              ctx s A); auto.
        rename g into A'.
        { specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          rename g into B'.
          { intros; forward_reason; split; auto.
            generalize (Proper_pctxD_impl tus tvs ctx s).
            generalize (Proper_pctxD_impl tus tvs ctx s0).
            generalize (Proper_pctxD_impl tus tvs ctx s1).
            generalize (@Applicative_pctxD tus tvs ctx s).
            generalize (@Applicative_pctxD tus tvs ctx s0).
            generalize (@Applicative_pctxD tus tvs ctx s1).
            simpl. forward.
            admit. }
          { admit. } }
        { specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          rename g into B'.
          { intros; forward_reason; split; auto.
            admit. }
          { admit. } } }
      { (* Solved *)
        clear - Htac; simpl; intros.
        specialize (Htac ctx s e _ eq_refl).
        eapply Htac. }
      { (* Goal *)
        clear. simpl.
        intros. split; auto.
        generalize (Proper_subst_pctxD_impl tus tvs ctx s).
        generalize (@Applicative_subst_pctxD tus tvs ctx s).
        forward.
        specialize (H1 _ eq_refl).
        destruct H1 as [ Hap Hpure ].
        red in H2; inv_all.
        split.
        { red. intros.
          eapply Hap. eapply H1. assumption. }
        { intros.
          eapply Hpure. auto. } }
*)
    Admitted.
  End runOnGoals'.

(*
  Theorem ctxD'_no_hyps
  : forall ctx tus tvs (P : exprT tus tvs Prop),
      (forall us vs, P us vs) ->
      @ctxD' tus tvs ctx P.
  Proof.
    induction ctx; simpl; intros; auto; forward; subst; auto.
  Qed.

  Lemma ctxD'_impl
  : forall c a b (P Q : exprT a b Prop),
      ctxD' c P ->
      (forall x y, P x y -> Q x y) ->
      ctxD' c Q.
  Proof.
    clear.
    induction c; simpl; auto.
    { intros. destruct b; auto.
      intro. specialize (H H1).
      eapply IHc; eauto. }
    { intros; destruct a; auto.
      intro. specialize (H H1).
      eapply IHc; eauto. }
    { intros; forward.
      eapply IHc; [ eassumption | eauto ]. }
  Qed.

  Lemma ctxD'_combine
  : forall c a b (P Q : exprT a b Prop),
      ctxD' c P ->
      ctxD' c Q ->
      ctxD' c (fun a b => P a b /\ Q a b).
  Proof.
    induction c; simpl; intros; eauto.
    { destruct b; auto.
      intros; forward_reason.
      subst. specialize (IHc _ _ _ _ H H0); simpl in *.
      clear - IHc.
      eapply ctxD'_impl; eauto; simpl.
      simpl. clear. intuition. }
    { destruct a; auto.
      intros; forward_reason.
      subst. specialize (IHc _ _ _ _ H H0); simpl in *.
      clear - IHc.
      eapply ctxD'_impl; eauto; simpl.
      simpl. clear. intuition. }
    { forward.
      specialize (IHc _ _ _ _ H0 H1); clear - IHc.
      eapply ctxD'_impl; eauto.
      simpl. intuition. }
  Qed.
*)
End parameterized.

Arguments rtac_sound {typ expr subst _ _ _ _ _ _} tus tvs tac : rename.

Arguments GEx {typ expr} _ _ _ : rename.
Arguments GAll {typ expr} _ _ : rename.
Arguments GHyp {typ expr} _ _ : rename.
Arguments GConj {typ expr} _ _ : rename.
Arguments GConj_ {typ expr} _ _ : rename.
Arguments GConj_list {typ expr} _ : rename.
Arguments GGoal {typ expr} _ : rename.
Arguments GSolved {typ expr} : rename.
Arguments CTop {typ expr} : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Arguments Fail {typ expr subst} : rename.
Arguments More {typ expr subst} _ _ : rename.
Arguments More_ {typ expr subst} _ _ : rename.
Arguments Solved {typ expr subst} _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.SubstI.
Export MirrorCore.ExprDAs.


(**
  (** TODO: I hope that there is a better way to reason about this **)
  Inductive Path (f : nat -> nat -> Prop) : nat -> nat -> Prop :=
  | PDirect : forall x y, f x y -> Path f x y
  | PThrough : forall x y z, f x y -> Path f y z -> Path f x z.

  Definition Acyclic_from (tus tvs : nat) (tes : list (typ * option expr))
  : Prop :=
    (forall x, ~Path (fun f t =>
                        f > tus /\ t > tus /\
                        exists z e,
                          nth_error tes (f - tus) = Some (z, Some e) /\
                          mentionsU t e = true) x x) /\
    (forall t e, In (t,Some e) tes ->
                 forall u, mentionsU u e = true ->
                           u < tus + length tes).

  Fixpoint WellFormed_goal (tus tvs : nat) (goal : Goal) : Prop :=
    match goal with
      | GAll _ goal' => WellFormed_goal tus (S tvs) goal'
      | GExs tes goal' =>
           Acyclic_from tus tvs tes
        /\ WellFormed_goal (tus + length tes) tvs goal'
      | GHyp _ goal' => WellFormed_goal tus tvs goal'
      | GGoal _ => True
      | GSolved => True
      | GConj_ ls =>
        (fix Forall (ls : list Goal) : Prop :=
           match ls with
             | nil => True
             | l :: ls => WellFormed_goal tus tvs l /\ Forall ls
           end) ls
    end.



          (** TODO: This can probably be more efficient because it can
           ** co-operate with mapUnderEx
           **)
          (fix go (nus : nat) (tes : list (typ * option expr)) (s : subst)
               (ctx : Ctx)
           : Result :=
             match tes with
               | nil => runRTac' ctx s g nus nvs
               | (t,e) :: tes =>
                 match e with
                   | None =>
                     mapUnderEx t nus (go (S nus) tes s (CEx ctx t))
                   | Some e' =>
                     match set nus e' s with
                       | None => Fail
                       | Some s' =>
                         mapUnderEx t nus (go (S nus) tes s' (CEx ctx t))
                     end
                 end
             end) nus tes s ctx
**)

(**
        
        assert (
            forall s gs,
              
              match r gs s with
                | Fail => True
                | More_ s' g' =>
                  WellFormed_subst s ->
                  WellFormed_subst s' /\
                  match osgD tus tvs (toGoal (length tus) (length tvs) ctx s (GConj_ gs))
                      , osgD tus tvs (toGoal (length tus) (length tvs) ctx s' g')
                  with
                    | Some gD , Some gD' =>
                      forall (us : hlist typD tus) (vs : hlist typD tvs),
                        gD' us vs -> gD us vs
                    | Some _ , None => False
                    | None , _ => True
                  end
                | Solved s' =>
                  WellFormed_subst s ->
                  WellFormed_subst s' /\
                  match osgD tus tvs (toGoal (length tus) (length tvs) ctx s (GConj_ gs))
                      , osgD tus tvs (toGoal (length tus) (length tvs) ctx s' GSolved)
                  with
                    | Some gD , Some sD' =>
                      forall (us : hlist typD tus) (vs : hlist typD tvs),
                        sD' us vs -> gD us vs
                    | Some _ , None => False
                    | None , _ => True
                  end
              end).
        { subst. clear.
          intros.
          eapply rtac_spec_respects.
          reflexivity.
          eapply More_More_. reflexivity. eapply GConj_GConj_. reflexivity.
          simpl. intros; split; auto.
          forward. }
        { clear Heqr. generalize dependent r.
          revert H; induction 1.
          { simpl; intros. eapply H0. }
          { simpl; intros. clear H0.
            specialize (H ctx s).
            match goal with
              | |- match match ?X with _ => _ end with _ => _ end =>
                destruct X ; auto
            end.
            - specialize (fun Z => IHForall (fun (other : list Goal) (s1 : subst) => r (g :: other) s1) Z s0).
              match type of IHForall with
                | ?X -> _ => assert X
              end.
              { intros. specialize (H1 s1 (g :: gs)).
                destruct (r (g :: gs) s1); auto.


  (** Intensional functor
  Inductive CtxFunctor tus tvs : Ctx * subst -> Ctx * subst -> Prop :=
  | CtxF_CTop : forall s1 s2,
                  (match substD tus tvs s1
                       , substD tus tvs s2
                   with
                     | Some s1D , Some s2D =>
                       forall us vs, s2D us vs -> s1D us vs
                     | None , _ => True
                     | Some _ , None => False
                   end) ->
                  CtxFunctor tus tvs (CTop, s1) (CTop, s2)
  | CtxF_
  **)

  Definition CtxMorphism {tus tvs tus' tvs' tus'' tvs''}
             (c1D : exprT tus' tvs' Prop -> exprT tus tvs Prop)
             (c2D : exprT tus'' tvs'' Prop -> exprT tus tvs Prop)
  : Prop :=
    exists f : exprT _ _ (hlist typD _ * hlist typD _),
      forall (P : exprT _ _ Prop) (Q : exprT _ _ Prop),
        (forall x y, P x y -> Q (fst (f x y)) (snd (f x y))) ->
        forall us vs,
          c1D P us vs -> c2D Q us vs.


  Definition CtxFunctor tus tvs : Ctx * subst -> Ctx * subst -> Prop :=
    fun cs1 cs2 =>
      let '(c1,s1) := cs1 in
      let '(c2,s2) := cs2 in
      match ctxD' tus tvs c1 s1
          , ctxD' tus tvs c2 s2
      with
        | None , _ => True
        | Some _ , None => False
        | Some (s1,c1D) , Some (s2,c2D) =>
          match substD tus tvs s1
              , substD tus tvs s2
          with
            | Some s1D , Some s2D =>
              CtxMorphism (fun k us vs => s1D us vs /\ c1D k us vs)
                          (fun k us vs => s2D us vs /\ c2D k us vs)
            | None , _ => True
            | Some _ , None => False
          end
      end.

            Lemma rinduction tus tvs ctx
            : forall g s g',
                (match osgD tus tvs (toGoal (length tus) (length tvs) ctx s g) with
                 | Some gD =>
                   match
                     osgD tus tvs (toGoal (length tus) (length tvs) ctx s g')
                   with
                     | Some sD' =>
                       forall (us : hlist typD tus) (vs : hlist typD tvs),
                         (sD' us vs) -> (gD us vs)
                     | None => False
                   end
                 | None => True
               end) <->
                (match ctxD' tus tvs ctx s
                       , goalD _ _ g
                       , goalD _ _ g'
                 with
                   | Some cD , Some gD , Some gD' =>
                     forall us vs,
                       cD (fun us' vs' =>
                             gD' us' vs' -> gD us' vs') us vs
                   | None , _ , _ => True
                   | Some _ , None , _ => True
                   | Some _ , _ , None => False
                 end).
            Proof.
              induction ctx; simpl.
              { intros.
                rewrite goalD_conv with (pfu := eq_sym (app_nil_r_trans _))
                                        (pfv := eq_sym (app_nil_r_trans _)).
                autorewrite with eq_rw.
                destruct (goalD tus tvs g);
                  destruct (goalD tus tvs g');
                  destruct (substD tus tvs s); try reflexivity.
                admit. }
              { intros. rewrite IHctx.
                simpl. forward.
                (** NOT TRUE **)
              }
              { intros.
                generalize (forgets_map_fst l (length (tus ++ getUVars ctx)) s).
                rewrite app_length.
                rewrite countUVars_getUVars.
                destruct (forgets (length tus + length (getUVars ctx)) l s).
                simpl; intros; subst.
                rewrite IHctx.
                simpl.
                rewrite goalD_conv with (pfu := eq_sym (app_ass_trans _ _ _)) (pfv := eq_refl).
                autorewrite with eq_rw.
                repeat match goal with
                         | |- context [ match ?X with _ => _ end ] =>
                           match X with
                             | match _ with _ => _ end => fail 1
                             | _ => destruct X
                           end
                       end; try reflexivity.
                do 2 (eapply forall_iff; intro).
                simpl.
*)