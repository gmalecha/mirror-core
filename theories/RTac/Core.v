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

(** TODO: Move to Data.HList **)
Theorem rev_app_distr_trans
: forall (A : Type) (x y : list A), rev (x ++ y) = rev y ++ rev x.
Proof. clear.
       induction x; simpl; intros.
       - symmetry. apply app_nil_r_trans.
       - rewrite IHx. apply app_ass_trans.
Defined.

(** TODO: Move to Data.List **)
Instance Injective_cons {T} (a : T) b c d
: Injective (a :: b = c :: d) :=
  { result := a = c /\ b = d }.
abstract (inversion 1; auto).
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

Instance Injective_Proper_Roption_Some {T} (rT : relation T) x
: Injective (Proper (Roption rT) (Some x)) :=
  { result := rT x x }.
abstract (inversion 1; assumption).
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

  Fixpoint goal_substD (tus tvs : list typ)
           (ts : list typ) (es : list (option expr))
  : option (exprT (tus ++ ts) tvs Prop) :=
    match ts as ts , es return option (exprT (tus ++ ts) tvs Prop) with
      | nil , nil => Some (fun _ _ => True)
      | t :: ts , None :: es =>
        match app_ass_trans tus (t :: nil) ts in _ = t
              return option (exprT _ tvs Prop) ->
                     option (exprT t tvs Prop)
        with
          | eq_refl => fun x => x
        end (goal_substD (tus ++ t :: nil) tvs ts es)
      | t :: ts , (Some e) :: es =>
        match exprD' (tus ++ t :: ts) tvs e t
            , goal_substD (tus ++ t :: nil) tvs ts es
        with
          | Some eD , Some sD =>
            Some (match eq_sym (app_ass_trans tus (t :: nil) ts) in _ = t
                        return exprT t tvs Prop -> exprT _ tvs Prop
                  with
                    | eq_refl => fun sD =>
                      fun us vs => sD us vs /\
                                   hlist_get_cons_after_app us = eD us vs
                  end sD)
          | _ , _ => None
        end
      | nil , _ :: _ => None
      | _ :: _ , nil => None
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
            , goal_substD tus tvs tus_ext (map snd tes) with
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
  : subst * list (option expr) :=
    match ts with
      | nil => (s,nil)
      | t :: ts =>
        let '(s',rr) := forgets (S from) ts s in
        let '(s'',ne) := forget from s' in
        (s'',ne :: rr)
    end.

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

  Fixpoint ctxD (tus tvs : tenv typ) (ctx : Ctx) (s : subst)
           {struct ctx}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match ctx as ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | CTop =>
        match substD tus tvs s with
          | None => None
          | Some sD =>
            Some (fun k us vs =>
                    sD us vs /\
                    k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
      | CAll ctx' t =>
          match ctxD tus tvs ctx' s with
            | Some cD =>
              Some (fun k : exprT _ _ Prop =>
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
      | CExs ctx' ts =>
        match forgets (length (tus ++ getUVars ctx')) ts s with
          | (s',tes) =>
            match goal_substD (tus ++ getUVars ctx') (tvs ++ getVars ctx') ts tes
                , ctxD tus tvs ctx' s'
            with
              | Some sD , Some cD =>
                Some (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                        cD (fun us vs =>
                              _exists typD ts (fun us' =>
                                                 sD (hlist_app us us') vs /\
                                                 k match
                                                     app_ass_trans tus _ ts in (_ = t0)
                                                     return (hlist typD t0)
                                                   with
                                                     | eq_refl => hlist_app us us'
                                                   end
                                                   vs)))
              | _ , _ => None
            end
        end
      | CHyp ctx' h =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match ctxD tus tvs ctx' s with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

  Fixpoint pctxD (tus tvs : tenv typ) (ctx : Ctx) (s : subst)
           {struct ctx}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match ctx as ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | CTop =>
        match substD tus tvs s with
          | None => None
          | Some sD =>
            Some (fun (k : exprT _ _ Prop) us vs => sD us vs ->
                                 k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
      | CAll ctx' t =>
          match pctxD tus tvs ctx' s with
            | Some cD =>
              Some (fun k : exprT _ _ Prop =>
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
      | CExs ctx' ts =>
        match forgets (length (tus ++ getUVars ctx')) ts s with
          | (s',tes) =>
            match goal_substD (tus ++ getUVars ctx') (tvs ++ getVars ctx') ts tes
                , pctxD tus tvs ctx' s'
            with
              | Some sD , Some cD =>
                Some (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                        cD (fun us vs =>
                              _foralls typD ts (fun us' =>
                                                 sD (hlist_app us us') vs ->
                                                 k match
                                                     app_ass_trans tus _ ts in (_ = t0)
                                                     return (hlist typD t0)
                                                   with
                                                     | eq_refl => hlist_app us us'
                                                   end
                                                   vs)))
              | _ , _ => None
            end
        end
      | CHyp ctx' h =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match pctxD tus tvs ctx' s with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
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
        match ctxD tus tvs ctx s
            , goalD _ _ g
            , ctxD tus tvs ctx s'
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
        match ctxD tus tvs ctx s
            , goalD _ _ g
            , ctxD tus tvs ctx s'
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
    red. red. intros. reflexivity.
  Qed.
  Instance Symmetric_EqResult tus tvs : Symmetric (EqResult tus tvs).
  Proof.
    red. unfold EqResult; inversion 1; constructor.
    symmetry; eauto.
  Qed.
  Instance Transitive_EqResult tus tvs : Transitive (EqResult tus tvs).
  Proof.
    red; unfold EqResult; inversion 1; inversion 1; constructor.
    subst.
    etransitivity; eauto.
  Qed.

  Ltac equivs :=
    repeat match goal with
             | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
           end; subst.

  Theorem Proper_pctxD_iff
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) iff ==>
                              (RexprT tus tvs iff)))%signature
             (pctxD tus tvs c1 s).
  Proof.
    induction c1; simpl; intros.
    { destruct (substD tus tvs s); try constructor.
      do 6 red; intros.
      apply equiv_eq_eq in H0; subst.
      apply equiv_eq_eq in H1; subst.
      eapply impl_iff; try reflexivity.
      intro. eapply H; reflexivity. }
    { red; simpl.
      specialize (IHc1 s).
      destruct (pctxD tus tvs c1 s); try constructor.
      inv_all.
      do 6 red. intros.
      eapply IHc1; eauto.
      do 5 red; intros.
      eapply forall_iff. intros.
      eapply H; eauto.
      equivs. reflexivity. }
    { destruct (forgets (length (tus ++ getUVars c1)) l s); simpl.
      intros; subst.
      specialize (IHc1 s0).
      destruct (goal_substD (tus ++ getUVars c1) (tvs ++ getVars c1) l l0);
        try constructor.
      destruct (pctxD tus tvs c1 s0); try constructor.
      inv_all.
      do 6 red; intros; equivs.
      eapply IHc1; try reflexivity.
      do 5 red; intros; equivs.
      eapply _forall_iff. intros.
      eapply impl_iff; try reflexivity.
      intros. eapply H; reflexivity. }
    { specialize (IHc1 s).
      destruct (propD (tus ++ getUVars c1) (tvs ++ getVars c1) e);
        try constructor.
      destruct (pctxD tus tvs c1 s); try constructor.
      do 6 red. intros.
      inv_all.
      eapply IHc1; eauto.
      do 5 red; intros.
      equivs.
      eapply impl_iff; try reflexivity.
      intros; eapply H; reflexivity. }
  Qed.

  Theorem Proper_pctxD_impl
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) Basics.impl ==>
                              (RexprT tus tvs Basics.impl)))%signature
             (pctxD tus tvs c1 s).
  Proof.
    induction c1; simpl; intros.
    { destruct (substD tus tvs s); try constructor.
      do 7 red.
      intros; equivs; eauto.
      eapply H; eauto; reflexivity. }
    { consider (pctxD tus tvs c1 s); constructor.
      specialize (IHc1 s). rewrite H in IHc1.
      inv_all.
      do 7 red; intros; equivs.
      revert H3; eapply IHc1; try reflexivity.
      do 6 red; intros; equivs.
      eapply H0; eauto; reflexivity. }
    { destruct (forgets (length (tus ++ getUVars c1)) l s).
      destruct (goal_substD (tus ++ getUVars c1) (tvs ++ getVars c1) l l0);
        try constructor.
      specialize (IHc1 s0).
      destruct (pctxD tus tvs c1 s0); try constructor.
      inv_all.
      do 7 red. intros; equivs.
      revert H2. eapply IHc1; try reflexivity.
      do 6 red; intros; equivs.
      revert H2.
      do 2 rewrite _forall_sem.
      intros. generalize (H0 _ H1).
      eapply H; reflexivity. }
    { destruct (propD (tus ++ getUVars c1) (tvs ++ getVars c1) e);
      try constructor.
      specialize (IHc1 s).
      destruct (pctxD tus tvs c1 s); constructor.
      inv_all.
      do 7 red; intros; equivs.
      revert H2. eapply IHc1; try reflexivity.
      do 6 red. intros. equivs.
      generalize (H2 H3). eapply H; reflexivity. }
  Qed.


(*
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
*)

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
    (EqGoal tus tvs ==> EqGoal tus tvs ==> EqGoal tus tvs)%signature
                                                          GConj GConj_.
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

  Theorem Applicative_pctxD
  : forall tus tvs ctx s C,
      pctxD tus tvs ctx s = Some C ->
      (forall us vs (P Q : exprT _ _ Prop),
         C (fun a b => P a b -> Q a b) us vs ->
         C P us vs ->
         C Q us vs) /\
      (forall us vs (Q : exprT _ _ Prop), (forall a b, Q a b) -> C Q us vs).
  Proof.
    clear. induction ctx; simpl; intros.
    { forward; inv_all; subst.
      forward_reason; split; eauto. }
    { specialize (IHctx s).
      forward; inv_all; subst.
      destruct (IHctx _ eq_refl) as [ Hap Hpure ]; clear IHctx.
      generalize (Proper_pctxD_impl tus tvs ctx s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H0; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto. }
      { intros us vs Q v.
        eapply Hpure. intros; eauto. } }
    { forward; inv_all; subst.
      destruct (IHctx _ _ H1) as [ Hap Hpure ]; clear IHctx.
      generalize (Proper_pctxD_impl tus tvs ctx s0).
      Cases.rewrite_all_goal; intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H2; [ | reflexivity | reflexivity | eapply f ].
        clear.
        do 6 red; intros; equivs.
        rewrite _forall_sem.
        rewrite _forall_sem in H1.
        rewrite _forall_sem in H2.
        firstorder. }
      { intros. eapply Hpure.
        intros. eapply _forall_sem.
        eauto. } }
    { specialize (IHctx s).
      forward; inv_all; subst.
      destruct (IHctx _ eq_refl) as [ Hap Hpure ]; clear IHctx.
      generalize (Proper_pctxD_impl tus tvs ctx s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H1; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto. }
      { intros us vs Q v.
        eapply Hpure. intros; eauto. } }
  Qed.

  Definition CtxMorphism {tus tvs tus' tvs'}
             (c1 c2 : exprT tus tvs Prop -> exprT tus' tvs' Prop) : Prop :=
    forall (P : exprT _ _ Prop) us vs, c1 P us vs -> c2 P us vs.

  Inductive SubstMorphism (tus tvs : tenv typ) : Ctx -> subst -> subst -> Prop :=
  | SMall : forall c t s1 s2,
              SubstMorphism tus tvs c s1 s2 ->
              SubstMorphism tus tvs (CAll c t) s1 s2
  | SMexs : forall c ts s1 s2,
              (let '(s1',es1) := forgets (length (tus ++ getUVars c)) ts s1 in
               let '(s2',es2) := forgets (length (tus ++ getUVars c)) ts s2 in
               match pctxD tus tvs c s1'
                   , goal_substD (tus ++ getUVars c) (tvs ++ getVars c) ts es1
                   , pctxD tus tvs c s2'
                   , goal_substD (tus ++ getUVars c) (tvs ++ getVars c) ts es2
               with
                 | None , _ , _ , _
                 | Some _ , None , _ , _ => True
                 | Some _ , Some _ , None , _
                 | Some _ , Some _ , Some _ , None => False
                 | Some c1D , Some s1D , Some c2D , Some s2D =>
                   forall us vs, c2D (fun us vs =>
                                       forall us',
                                         s2D (hlist_app us us') vs ->
                                         s1D (hlist_app us us') vs) us vs
               end) ->
              SubstMorphism tus tvs c
                            (fst (forgets (length (tus ++ getUVars c)) ts s1))
                            (fst (forgets (length (tus ++ getUVars c)) ts s2)) ->
              SubstMorphism tus tvs (CExs c ts) s1 s2
  | SMhyp : forall c h s1 s2,
              SubstMorphism tus tvs c s1 s2 ->
              SubstMorphism tus tvs (CHyp c h) s1 s2
  | SMtop : forall s1 s2,
              match substD tus tvs s1
                  , substD tus tvs s2
              with
                | None , _ => True
                | Some _ , None => False
                | Some a , Some b => forall us vs, b us vs -> a us vs
              end ->
              SubstMorphism tus tvs CTop s1 s2.




  Definition rtac_local_spec tus tvs ctx s g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match pctxD tus tvs ctx s
            , goalD _ _ g
            , pctxD tus tvs ctx s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            SubstMorphism tus tvs ctx s s' /\
            forall us vs,
              cD' gD us vs
        end
      | More_ s' g' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match pctxD tus tvs ctx s
            , goalD _ _ g
            , pctxD tus tvs ctx s'
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            SubstMorphism tus tvs ctx s s' /\
            forall us vs, cD' (fun us vs => gD' us vs -> gD us vs) us vs
        end
    end.

  Lemma Fmap_pctxD_impl
  : forall tus tvs c s C,
      pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ Basics.impl ==> RexprT tus tvs Basics.impl)%signature C.
  Proof.
    clear. intros.
    generalize (Proper_pctxD_impl tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma Fmap_pctxD_iff
  : forall tus tvs c s C,
      pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ iff ==> RexprT tus tvs iff)%signature C.
  Proof.
    clear. intros.
    generalize (Proper_pctxD_iff tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  (** TODO: Move to Data.Prop **)
  Lemma True_impl_iff : forall (P : Prop), (True -> P) <-> P.
  Proof.
    clear; intros; tauto.
  Qed.

  Theorem Proper_rtac_local_spec tus tvs ctx s
  : Proper (EqGoal (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==>
            EqResult (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==> iff)
           (rtac_local_spec tus tvs ctx s).
  Proof.
    red. red. red. unfold rtac_local_spec.
    inversion 2.
    { destruct x0; destruct y0; simpl in *; try congruence.
      reflexivity. }
    { destruct x0; destruct y0; simpl in *;
      try solve [ reflexivity | congruence ]; inv_all; subst; inv_all;
      try (eapply impl_iff; try reflexivity; intros;
           eapply and_iff; try reflexivity; intros;
           try inversion H; try reflexivity;
           try inversion H5; try reflexivity;
           repeat match goal with
                    | |- context [ match ?X with _ => _ end ] =>
                      consider X; intros; try reflexivity; [ ]
                  end;
           eapply and_iff; try reflexivity; intros;
           do 2 (eapply forall_iff; intro);
           eapply Fmap_pctxD_iff; eauto; try reflexivity;
           do 5 red; intros).
      { apply impl_iff; [ eapply H10; eauto | intro ].
        apply H7; eauto. }
      { do 5 red in H10.
        rewrite H10; try reflexivity.
        rewrite True_impl_iff.
        eapply H7; eauto. }
      { do 5 red in H10.
        rewrite <- H10; try reflexivity.
        rewrite True_impl_iff.
        eapply H7; eauto. } }
  Qed.

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
    eapply Hinj. eapply Hf.
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
    eapply Hinj. eapply Hf.
  Qed.

  Instance Reflexive_SubstMorphism tus tvs ctx
  : Reflexive (SubstMorphism tus tvs ctx).
  Proof.
    red. induction ctx; simpl; intros; try constructor;
         forward; eauto.
    eapply Applicative_pctxD in H0.
    destruct H0.
    eapply H2. clear; auto.
  Qed.

  Lemma pctxD_SubstMorphism
  : forall tus tvs ctx s s',
      SubstMorphism tus tvs ctx s s' ->
      forall C C',
      pctxD tus tvs ctx s = Some C ->
      pctxD tus tvs ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C P us vs -> C' P us vs.
  Proof.
    induction 1; intros; simpl in *; forward; inv_all; subst; eauto.
    { eapply IHSubstMorphism; eauto. }
    { simpl in *.
      eapply (IHSubstMorphism _ _ H7 H4) in H3.
      destruct (Applicative_pctxD _ _ H4) as [ Hap Hpure ].
      Cases.rewrite_all_goal.
      intros; inv_all.
      revert H3. eapply Hap.
      generalize (H9 us vs).
      eapply Hap.
      eapply Hpure.
      clear. intros.
      rewrite _forall_sem.
      rewrite _forall_sem in H0.
      intros; eauto. }
    { eapply IHSubstMorphism; eauto. }
  Qed.

  Instance Transitive_SubstMorphism tus tvs ctx
  : Transitive (SubstMorphism tus tvs ctx).
  Proof.
    clear. red. intros x y z H; revert z.
    induction H.
    { inversion 1; subst.
      constructor; eauto. }
    { inversion 1; subst.
      forward. simpl in *.
      constructor.
      { forward. inv_all; subst.
        Cases.rewrite_all_goal.
        repeat match goal with
                 | H : ?X = _ , H' : ?X = _ |- _ =>
                   rewrite H in H'
               end; inv_all; subst.
        specialize (H16 us vs).
        specialize (H14 us vs).
        revert H16.
        eapply (Applicative_pctxD _ _ H13).
        eapply (pctxD_SubstMorphism H7 H4 H13 us vs).
        revert H14.
        eapply (Applicative_pctxD _ _ H4).
        eapply (Applicative_pctxD _ _ H4).
        clear. firstorder. }
      { Cases.rewrite_all_goal; simpl.
        eauto. } }
    { inversion 1; subst; constructor; eauto. }
    { inversion 1; subst; constructor.
      forward. eauto. }
  Qed.


  Lemma pctxD_ctxD
  : forall tus tvs ctx s pC C,
      pctxD tus tvs ctx s = Some pC ->
      ctxD tus tvs ctx s = Some C ->
      forall us vs (P Q : exprT _ _ Prop),
        pC (fun a b => P a b -> Q a b) us vs ->
        C P us vs -> C Q us vs.
  Proof.
    induction ctx; simpl; intros; inv_all; subst; forward; inv_all; subst.
    { firstorder. }
    { revert H2. eapply IHctx; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red. intros; equivs. firstorder. }
    { revert H2.
      eapply IHctx; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red; intros; equivs.
      rewrite _exists_sem.
      rewrite _exists_sem in H2.
      destruct H2 as [ v ? ]; exists v.
      rewrite _forall_sem in H1.
      specialize (H1 v).
      firstorder. }
    { revert H2. eapply IHctx; eauto.
      revert H1.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red. intros; equivs. firstorder. }
  Qed.

  Lemma pctxD_ctxD_safe
  : forall tus tvs ctx s P,
      pctxD tus tvs ctx s = Some P ->
      exists P',
        ctxD tus tvs ctx s = Some P'.
  Proof.
    induction ctx; simpl; intros; forward; inv_all; subst; eauto;
    match goal with
      | H : pctxD _ _ _ _ = _ |- _ =>
        eapply IHctx in H; forward_reason;
        Cases.rewrite_all_goal; eauto
    end.
  Qed.

  Lemma ctxD_pctxD_safe
  : forall tus tvs ctx s P,
      ctxD tus tvs ctx s = Some P ->
      exists P',
        pctxD tus tvs ctx s = Some P'.
  Proof.
    induction ctx; simpl; intros; forward; inv_all; subst; eauto;
    match goal with
      | H : ctxD _ _ _ _ = _ |- _ =>
        eapply IHctx in H; forward_reason;
        Cases.rewrite_all_goal; eauto
    end.
  Qed.

  Lemma pctxD_to_ctxD
  : forall tus tvs ctx s pC,
      pctxD tus tvs ctx s = Some pC ->
      exists C,
        ctxD tus tvs ctx s = Some C /\
        forall us vs (P Q : exprT _ _ Prop),
          pC (fun a b => P a b -> Q a b) us vs ->
          C P us vs -> C Q us vs.
  Proof.
    clear. intros.
    destruct (pctxD_ctxD_safe _ _ H).
    eexists; split; eauto.
    apply (pctxD_ctxD _ _ H H0).
  Qed.

  Lemma ctxD_to_pctxD
  : forall tus tvs ctx s C,
      ctxD tus tvs ctx s = Some C ->
      exists pC,
        pctxD tus tvs ctx s = Some pC /\
        forall us vs (P Q : exprT _ _ Prop),
          pC (fun a b => P a b -> Q a b) us vs ->
          C P us vs -> C Q us vs.
  Proof.
    clear. intros.
    destruct (ctxD_pctxD_safe _ _ H).
    eexists; split; eauto.
    apply (pctxD_ctxD _ _ H0 H).
  Qed.

(*
  Lemma Proper_ctxD_iff tus tvs ctx s
  : Proper (Roption (RexprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) iff ==>
                            (RexprT tus tvs iff)))%signature
      (ctxD tus tvs ctx s).
  Proof.
  Abort.

  Lemma Proper_ctxD_impl tus tvs ctx s
  : Proper (Roption (RexprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Basics.impl ==>
                            (RexprT tus tvs Basics.impl)))%signature
      (ctxD tus tvs ctx s).
  Abort.

  Instance Transitive_CtxMorphism a b c d : Transitive (@CtxMorphism a b c d).
  Proof.
    clear. red. red. intuition.
    specialize (H1 us vs).
    eapply H0. 2: eapply H. 3: eassumption.
    eapply H1. auto.
  Qed.
*)

  Lemma ctxD_SubstMorphism
  : forall tus tvs ctx s s',
      SubstMorphism tus tvs ctx s s' ->
      forall C C',
      ctxD tus tvs ctx s = Some C ->
      ctxD tus tvs ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C' P us vs -> C P us vs.
  Proof.
    induction 1; simpl; intros; forward; inv_all; subst.
    { specialize (IHSubstMorphism _ _ eq_refl eq_refl); eauto. }
    { destruct (ctxD_to_pctxD _ _ H5) as [ ? [ ? ? ] ].
      rewrite H6 in *.
      eapply (IHSubstMorphism _ _ H7 H5).
      revert H3.
      eapply H9.
      destruct (ctxD_pctxD_safe _ _ H7).
      rewrite H3 in *.
      generalize (H8 us vs).
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      clear.
      do 6 red; intros; equivs.
      rewrite _exists_sem.
      rewrite _exists_sem in H2. destruct H2 as [ v ? ]; exists v.
      firstorder. }
    { specialize (IHSubstMorphism _ _ eq_refl eq_refl); eauto. }
    { simpl in *. forward; inv_all; subst.
      intuition. }
  Qed.

  Lemma rtac_local_spec_rtac_spec
  : forall tus tvs ctx s g r,
      rtac_local_spec tus tvs ctx s g r ->
      rtac_spec tus tvs ctx s g r.
  Proof.
    clear.
    unfold rtac_local_spec, rtac_spec.
    destruct r; auto; intros; forward_reason; split; auto.
    { forward. inv_all; subst.
      destruct (ctxD_to_pctxD _ _ H2) as [ ? [ ? ? ] ].
      rewrite H4 in *.
      forward.
      destruct (pctxD_to_ctxD _ _ H3) as [ ? [ ? ? ] ].
      Cases.rewrite_all_goal.
      destruct H7.
      generalize (@ctxD_SubstMorphism tus tvs ctx s s0 H7 _ _ H2 H8);
        intro; clear H7.
      intros us vs.
      repeat match goal with
               | H : _ |- _ => specialize (H us vs)
             end.
      intros. eapply H11; clear H11.
      eapply H9; [ | eassumption ].
      eauto. }
    { forward. inv_all; subst.
      destruct (ctxD_to_pctxD _ _ H2) as [ ? [ ? ? ] ].
      rewrite H4 in *.
      forward.
      destruct (pctxD_to_ctxD _ _ H3) as [ ? [ ? ? ] ].
      Cases.rewrite_all_goal.
      destruct H6.
      generalize (@ctxD_SubstMorphism tus tvs ctx s s0 H6 _ _ H2 H7);
        intro; clear H7.
      intros us vs.
      repeat match goal with
               | H : _ |- _ => specialize (H us vs)
             end.
      intros. eapply H10; clear H10.
      eapply H8; [ | eassumption ].
      simpl.
      generalize (Proper_pctxD_impl tus tvs ctx s0).
      Cases.rewrite_all_goal.
      intros; inv_all. revert H9. eapply H10; try reflexivity.
      do 6 red. clear.
      intros; equivs; eauto. }
  Qed.

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
              let ts := map fst tes in
              match runOnGoals' (length tes + nus) nvs (CExs ctx ts) s' g with
                | Fail => Fail
                | Solved s'' =>
                  (** Here I can drop anything that is already instantiated. **)
                  let '(s''',tes') := forgets nus ts s'' in
                  let tes' := combine ts tes' in
                  More_ s''' (GExs tes' GSolved)
                | More_ s'' g' =>
                  let '(s''',tes') := forgets nus ts s'' in
                  let tes' := combine ts tes' in
                  More_ s''' (GExs tes' g')
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

    Definition runOnGoals (tus : tenv typ) (tvs : tenv typ)
               (ctx : Ctx) (s : subst) (g : Goal)
    : Result :=
      runOnGoals' (length tus + countUVars ctx)
                  (length tvs + countVars ctx) ctx s g.

    Variables tus tvs : tenv typ.
    Hypothesis Htac
    : forall ctx s ge result,
        tac ctx s ge = result ->
        rtac_local_spec tus tvs ctx s (GGoal ge) result.

    Lemma WellFormed_remembers
    : forall a b s s',
        remembers a b s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s'.
    Admitted.
    Lemma WellFormed_forgets
    : forall a b c s s',
        forgets a b s = (s',c) ->
        WellFormed_subst s ->
        WellFormed_subst s'.
    Admitted.

    Lemma remembers_forgets_safe
    : forall tes s s' s'' sD es eD,
        remembers (length tus) tes s = Some s' ->
        forgets (length tus) (map fst tes) s' = (s'',es) ->
        substD tus tvs s = Some sD ->
        goal_substD tus tvs (map fst tes) (map snd tes) = Some eD ->
        exists eD',
          goal_substD tus tvs (map fst tes) es = Some eD'.
    Proof.
      clear Htac tac.
      induction tes; simpl; intros; inv_all; subst; eauto.
      forward. subst. simpl in *.
      inv_all; subst.
      destruct o0; forward; inv_all; subst.
      { (*
        
        eapply forget_sound in H3; eauto.
        forward_reason.
        specialize (@H5 _ _ _ _ H1).
*)
    Admitted.


    Lemma runOnGoals'_sound_ind
    : forall g ctx s,
        rtac_local_spec tus tvs ctx s g
                        (runOnGoals' (length tus + countUVars ctx)
                                     (length tvs + countVars ctx)
                                     ctx s g).
    Proof.
      red. induction g; fold runOnGoals' in *.
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
        { generalize (Proper_pctxD_impl tus tvs ctx s0).
          simpl in *.
          forward; inv_all; subst.
          forward_reason.
          inversion H7; clear H7; subst.
          split; eauto.
          intros us vs.
          eapply H5; [ | reflexivity | reflexivity | eapply H8 ].
          do 6 red. clear.
          intros. equivs. eauto. }
        { generalize (Proper_pctxD_impl tus tvs ctx s0).
          simpl in *.
          forward; inv_all; subst.
          forward_reason.
          inversion H6; clear H6; subst.
          split; eauto. } }
      { (* Exs *)
        intros; simpl in *.
        forward.
        specialize (IHg (CExs ctx (map fst l)) s0).
        revert IHg. revert H; simpl.
        repeat rewrite countUVars_getUVars.
        repeat rewrite countVars_getVars.
        do 2 rewrite <- app_length.
        intros; forward.
        match goal with
          | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X;
              [ remember X as X' ; destruct X'
              | f_equal ; simpl; repeat rewrite app_length;
                rewrite map_length; omega ]
        end; intros; auto;
        match goal with
          | |- context [ forgets ?A ?B ?C ] =>
            consider (forgets A B C)
        end; intros; simpl in *.
        { consider (forgets (length (tus ++ getUVars ctx)) (map fst l) s0); intros; auto.
          inv_all; subst.
          generalize (WellFormed_remembers _ _ _ H H4); intros.
          forward_reason.
          split; [ eapply WellFormed_forgets; eauto | ].
          forward. inv_all; subst.
          revert H8. revert H9.
          
              inv_all; subst
            { admit. }
            

          admit. }
        { consider (forgets (length tus + countUVars ctx) (map fst l) s1); intros; auto.
          inv_all; subst.
          admit. } }
      { simpl; intros.
        specialize (IHg (CHyp ctx e) s).
(*        match goal with
          | H : match ?X with _ => _ end
            |- match match ?Y with _ => _ end with _ => _ end =>
            replace Y with X; [ remember X as X' ; destruct X' | f_equal ; simpl ; rewrite map_length; omega ]
        end; auto;
        intros; forward_reason; split; eauto; simpl in *;
        unfold subst_pctxD in *; forward; subst; inv_all; subst.
        { destruct H10.
          inversion H1; clear H1; subst. split; auto.
          generalize (Proper_subst_pctxD_impl tus tvs ctx s0).
          simpl.
          rewrite H12 in *; inv_all; subst.
          unfold subst_pctxD.
          Cases.rewrite_all_goal.
          do 3 intro; inv_all.
          eapply H1; [ | reflexivity | reflexivity | eapply H5 ].
          do 6 red.
          intros. eapply equiv_eq_eq in H6; eapply equiv_eq_eq in H8; subst.
          tauto. }
        { destruct H9.
          inversion H1; clear H1; subst. split; auto.
          generalize (Proper_subst_pctxD_impl tus tvs ctx s0).
          simpl.
          rewrite H11 in *. inv_all; subst.
          unfold subst_pctxD.
          Cases.rewrite_all_goal.
          do 3 intro; inv_all.
          eapply H1; [ | reflexivity | reflexivity | eapply H5 ].
          do 6 red.
          intros. eapply equiv_eq_eq in H6; eapply equiv_eq_eq in H8; subst.
          tauto. } *)
        admit. }
      { (* Conj *)
        simpl; intros; clear Htac.
        specialize (IHg1 ctx s).
        rename g1 into A.
        rename g2 into B.
        destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                              ctx s A); auto.
        { rename g into A'.
          specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          { rename g into B'.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H12 us vs).
            revert H11.
            eapply (Applicative_pctxD _ _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H12.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. }
          { change (rtac_local_spec tus tvs ctx s (GConj_ A B) (More s1 A')).
            eapply Proper_rtac_local_spec; [ reflexivity | eapply More_More_ | ].
            reflexivity. reflexivity.
            simpl.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H11 us vs).
            specialize (H10 us vs).
            revert H10.
            eapply (Applicative_pctxD _ _ H8).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H11.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. } }
        { specialize (IHg2 ctx s0).
          destruct (runOnGoals' (length tus + countUVars ctx) (length tvs + countVars ctx)
                                ctx s0 B); auto.
          { rename g into B'.
            intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H10 us vs).
            specialize (H11 us vs).
            revert H10.
            eapply (Applicative_pctxD _ _ H7).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H11.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. }
          { intros; forward_reason; split; auto.
            simpl. forward. forward_reason.
            split; [ etransitivity; eassumption | ].
            intros us vs.
            specialize (H9 us vs).
            specialize (H10 us vs).
            revert H9.
            eapply (Applicative_pctxD _ _ H7).
            eapply pctxD_SubstMorphism.
            3: eassumption. eassumption. eassumption.
            revert H10.
            eapply (Fmap_pctxD_impl _ _ H3); try reflexivity.
            clear. do 6 red.
            intros. equivs. firstorder. } } }
      { (* Goal *)
        clear - Htac; simpl; intros.
        specialize (@Htac ctx s e _ eq_refl).
        eapply Htac. }
      { (* Solved *)
        clear. simpl.
        intros. split; auto.
        forward. split.
        reflexivity.
        intros.
        eapply (@Applicative_pctxD tus tvs ctx s); eauto. }
    Qed.

    Theorem runOnGoals_sound ctx s g
    : rtac_local_spec tus tvs ctx s g
                      (runOnGoals' (length tus + countUVars ctx)
                                   (length tvs + countVars ctx)
                                   ctx s g).
    Proof.
      eapply runOnGoals'_sound_ind.
    Qed.

  End runOnGoals'.

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
