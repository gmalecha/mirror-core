Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
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

(*  Unset Elimination Schemes. *)

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

  Fixpoint GConj (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | g :: nil => g
      | g :: gs => GConj_ g (GConj gs)
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
  (** End: Auxiliary Functions **)

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

  Fixpoint ctxD (tus tvs : tenv typ) (ctx : Ctx)
           {struct ctx}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match ctx as ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | CTop => Some (fun k us vs => k (hlist_app us Hnil) (hlist_app vs Hnil))
      | CAll ctx' t =>
        match ctxD tus tvs ctx' with
          | Some cD =>
            Some
              (fun k : exprT _ _ Prop =>
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
        match ctxD tus tvs ctx' with
          | Some cD =>
            Some
              (fun k : exprT _ _ Prop =>
                 cD (fun us vs =>
                       _exists typD ts (fun us' =>
                         k match
                             app_ass_trans tus (getUVars ctx') ts in (_ = t0)
                             return (hlist typD t0)
                           with
                             | eq_refl => hlist_app us us'
                           end
                           vs)))
          | None => None
        end
      | CHyp ctx' h =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match ctxD tus tvs ctx' with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

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

  Fixpoint ctxD' (tus tvs : tenv typ) (ctx : Ctx) (s : subst)
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
            Some (fun k us vs => sD us vs /\ k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
      | CAll ctx' t =>
(*        if strengthenV (length (tvs ++ getVars ctx')) 1 s then *)
          match ctxD' tus tvs ctx' s with
            | Some cD =>
              Some
                (fun k : exprT _ _ Prop =>
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
                , ctxD' tus tvs ctx' s'
            with
              | Some sD , Some cD =>
                Some
                  (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                     cD (fun us vs =>
                           _exists typD ts (fun us' =>
                                          sD (hlist_app us match eq_sym pf in _ = t return hlist _ t with
                                                             | eq_refl => us'
                                                           end) vs /\
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
          | Some pD => match ctxD' tus tvs ctx' s with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

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

  Definition CtxFunctor tus tvs : Ctx * subst -> Ctx * subst -> Prop :=
    fun cs1 cs2 =>
      let '(c1,s1) := cs1 in
      let '(c2,s2) := cs2 in
      match ctxD' tus tvs c1 s1
          , ctxD' tus tvs c2 s2
      with
        | None , _ => True
        | Some _ , None => False
        | Some c1D , Some c2D =>
          exists f : exprT _ _ (hlist typD _ * hlist typD _),
                     forall (P : exprT _ _ Prop) (Q : exprT _ _ Prop),
                       (forall x y, P x y -> Q (fst (f x y)) (snd (f x y))) ->
                     forall us vs,
                       c2D P us vs -> c1D Q us vs
      end.

  Definition CtxMorphism {tus tvs tus' tvs' tus'' tvs''}
             (c1D : exprT tus' tvs' Prop -> exprT tus tvs Prop)
             (c2D : exprT tus'' tvs'' Prop -> exprT tus tvs Prop)
  : Prop :=
    exists f : exprT _ _ (hlist typD _ * hlist typD _),
      forall (P : exprT _ _ Prop) (Q : exprT _ _ Prop),
        (forall x y, P x y -> Q (fst (f x y)) (snd (f x y))) ->
        forall us vs,
          c2D P us vs -> c1D Q us vs.

  Definition osgD (tus tvs : tenv typ) (osg : option (subst * Goal))
  : option (exprT tus tvs Prop) :=
    match osg with
      | None => None
      | Some (s,g) =>
        match goalD tus tvs g
            , substD tus tvs s
        with
          | Some gD , Some sD =>
            Some (fun us vs => sD us vs /\ gD us vs)
          | _ , _ => None
        end
    end.

  Fixpoint toGoal (nus nvs : nat) (ctx : Ctx) (s : subst) (g : Goal)
  : option (subst * Goal) :=
    match ctx with
      | CTop => Some (s, g)
      | CAll ctx' l =>
(*        if strengthenV (nvs + countVars ctx') 1 s then *)
          toGoal nus nvs ctx' s (GAll l g)
(*        else
          None *)
      | CExs  ctx' ts =>
        (** TODO: It seems to be a problem that this is not directly
         ** related to [CEx]
         **)
        let '(s',tes) := forgets (nus + countUVars ctx') ts s in
(*        if strengthenU (nus + countUVars ctx') (length ts) s' then *)
          toGoal nus nvs ctx' s' (GExs tes g)
(*        else
          None *)
      | CHyp ctx' h =>
        toGoal nus nvs ctx' s (GHyp h g)
    end.

  Definition rtac_spec tus tvs ctx s g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match ctxD' tus tvs ctx s
              , goalD _ _ g
              , ctxD' tus tvs ctx s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            CtxMorphism cD cD' /\
            forall us vs,
              cD' (fun _ _ => True) us vs ->
              cD gD us vs
        end
      | More_ s' g' =>
        WellFormed_subst s ->
        WellFormed_subst s' /\
        match ctxD' tus tvs ctx s
              , goalD _ _ g
              , ctxD' tus tvs ctx s'
              , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            CtxMorphism cD cD' /\
            forall us vs,
              cD' gD' us vs ->
              cD gD us vs
        end
    end.

  Definition EqGoal tus tvs : relation Goal :=
    fun g1 g2 =>
      forall ctx s,
        Roption (RexprT tus tvs iff)
                (osgD tus tvs (toGoal (length tus) (length tvs) ctx s g1))
                (osgD tus tvs (toGoal (length tus) (length tvs) ctx s g2)).

  Instance Reflexive_EqGoal tus tvs : Reflexive (EqGoal tus tvs).
  Admitted.
  Instance Symmetric_EqGoal tus tvs : Symmetric (EqGoal tus tvs).
  Admitted.
  Instance Transitive_EqGoal tus tvs : Transitive (EqGoal tus tvs).
  Admitted.

  Inductive Eqpair {T U} (rT : relation T) (rU : relation U) : relation (T * U) :=
  | Eqpair_both : forall a b c d, rT a b -> rU c d -> Eqpair rT rU (a,c) (b,d).

  Definition EqResult tus tvs : relation Result :=
    fun r1 r2 =>
      Roption (Eqpair (@eq _) (EqGoal tus tvs))
              (fromResult r1) (fromResult r2).

  Instance Reflexive_EqResult tus tvs : Reflexive (EqResult tus tvs).
  Admitted.
  Instance Symmetric_EqResult tus tvs : Symmetric (EqResult tus tvs).
  Admitted.
  Instance Transitive_EqResult tus tvs : Transitive (EqResult tus tvs).
  Admitted.

  Theorem rtac_spec_respects tus tvs ctx s
  : Proper (EqGoal tus tvs ==> EqResult tus tvs ==> iff)
           (rtac_spec tus tvs ctx s).
  Proof.
    red. red. red.
    unfold rtac_spec.
    unfold EqGoal.
    unfold EqResult.
    intros.
    specialize (H ctx s).
    inversion H.
    { clear - H0.
      destruct x0; destruct y0; simpl in *;
      try solve [ reflexivity
                | inversion H0; subst; inversion H2; subst; reflexivity ].
      { inversion H0; subst; inversion H2; subst.
        eapply impl_iff; [ reflexivity | intro ].
        eapply and_iff; [ reflexivity | intro ].
        forward.
        admit. }
      { admit. }
      { admit. }
      { admit. } }
    { (*
      destruct x0; destruct y0; simpl in *;
      try solve [ reflexivity
                | inversion H0 ].
      - inversion H0; clear H0. inversion H6; clear H6; subst.
        apply impl_iff; [ reflexivity | intro ].
        apply and_iff; [ reflexivity | intro ].
        specialize (H11 ctx s1); destruct H11; try reflexivity.
        apply forall_iff; intro.
        apply forall_iff; intro.
        apply impl_iff. apply H5; reflexivity. intro.
        apply H3; reflexivity.
      - inversion H0; clear H0. inversion H6; clear H6; subst.
        apply impl_iff; [ reflexivity | intro ].
        apply and_iff; [ reflexivity | intro ].
        specialize (H11 ctx s1); destruct H11; try reflexivity.
        apply forall_iff; intro.
        apply forall_iff; intro.
        apply impl_iff. apply H5; reflexivity. intro.
        apply H3; reflexivity.
      - inversion H0; clear H0. inversion H6; clear H6; subst.
        apply impl_iff; [ reflexivity | intro ].
        apply and_iff; [ reflexivity | intro ].
        specialize (H11 ctx s1); destruct H11; try reflexivity.
        apply forall_iff; intro.
        apply forall_iff; intro.
        apply impl_iff. apply H5; reflexivity. intro.
        apply H3; reflexivity.
      - inversion H0; clear H0. inversion H6; clear H6; subst.
        apply impl_iff; [ reflexivity | intro ].
        apply and_iff; [ reflexivity | intro ].
        specialize (H11 ctx s1); destruct H11; try reflexivity.
        apply forall_iff; intro.
        apply forall_iff; intro.
        apply impl_iff. reflexivity.
        intro. apply H3; reflexivity. *) admit. }
  Qed.

  Definition rtac_sound (tus tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      rtac_spec tus tvs ctx s g result.

  Lemma Proper_ctxD tus tvs ctx
  : Roption (RexprT _ _ iff ==> RexprT tus tvs iff)%signature
            (ctxD tus tvs ctx)
            (ctxD tus tvs ctx).
  Proof.
    induction ctx; simpl.
    { constructor. unfold RexprT, OpenTeq, OpenTrel; simpl.
      red. intros.
      do 2 rewrite hlist_app_nil_r.
      eapply H.
      - rewrite hlist_app_nil_r.
        generalize (app_nil_r_trans tus).
        generalize (tus ++ nil). intros; subst.
        apply H0.
      - rewrite hlist_app_nil_r.
        generalize (app_nil_r_trans tvs).
        generalize (tvs ++ nil). intros; subst.
        apply H1. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      red. intros.
      inversion IHctx; subst.
      eapply H4; eauto.
      do 5 red.
      intros. eapply forall_iff. intro.
      eapply H; eauto.
      apply equiv_eq_eq in H3. subst. reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      red. intros.
      inversion IHctx; subst.
      eapply H4; eauto.
      do 5 red.
      intros. eapply _exists_iff. intro.
      eapply H; eauto.
      apply equiv_eq_eq in H2. subst. reflexivity. }
    { intros.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      red; unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      inversion IHctx; clear IHctx; subst.
      eapply H4; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      repeat match goal with
               | H : equiv_hlist _ _ _ |- _ =>
                 apply equiv_eq_eq in H
             end; subst.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
  Qed.

  Lemma Proper_ctxD' tus tvs ctx
  : forall s,
      Roption (RexprT _ _ iff ==> RexprT tus tvs iff)%signature
              (ctxD' tus tvs ctx s)
              (ctxD' tus tvs ctx s).
  Proof.
    induction ctx; simpl.
    { intros.
      destruct (substD tus tvs s); try constructor.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      red. intros.
      eapply equiv_eq_eq in H0; eapply equiv_eq_eq in H1; subst.
      apply and_iff. reflexivity.
      intros. apply H; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intro s; specialize (IHctx s).
      destruct (ctxD' tus tvs ctx s); constructor.
      red. inversion IHctx; clear IHctx; subst.
      intros. eapply H1; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      apply equiv_eq_eq in H3; apply equiv_eq_eq in H4; subst.
      apply forall_iff; intros.
      eapply H. reflexivity. reflexivity. }
    { intros.
      generalize dependent (forgets_map_fst l (length (tus ++ getUVars ctx)) s).
      destruct (forgets (length (tus ++ getUVars ctx)) l s).
      intros; subst. simpl.
      specialize (IHctx s0).
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      red; unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      inversion IHctx; clear IHctx; subst.
      eapply H4; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl; intros.
      eapply _exists_iff; intros.
      repeat match goal with
               | H : equiv_hlist _ _ _ |- _ =>
                 apply equiv_eq_eq in H
             end; subst.
      eapply and_iff; intros.
      reflexivity.
      eapply H; reflexivity. }
    { intros.
      specialize (IHctx s).
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      red; unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      inversion IHctx; clear IHctx; subst.
      eapply H4; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      repeat match goal with
               | H : equiv_hlist _ _ _ |- _ =>
                 apply equiv_eq_eq in H
             end; subst.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
  Qed.

  Lemma Proper_ctxD'_impl tus tvs ctx
  : forall s,
      Roption (RexprT _ _ Basics.impl ==> RexprT tus tvs Basics.impl)%signature
              (ctxD' tus tvs ctx s)
              (ctxD' tus tvs ctx s).
  Proof.
    induction ctx; simpl.
    { intros.
      destruct (substD tus tvs s); try constructor.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      red. intros.
      eapply equiv_eq_eq in H0; eapply equiv_eq_eq in H1; subst.
      red. intuition. eapply H; eauto. reflexivity. reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intro s; specialize (IHctx s).
      destruct (ctxD' tus tvs ctx s); constructor.
      red. inversion IHctx; clear IHctx; subst.
      intros. eapply H1; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      apply equiv_eq_eq in H3; apply equiv_eq_eq in H4; subst.
      red. intros. specialize (H3 x2).
      eapply H; try reflexivity. eassumption. }
    { intros.
      generalize dependent (forgets_map_fst l (length (tus ++ getUVars ctx)) s).
      destruct (forgets (length (tus ++ getUVars ctx)) l s).
      intros; subst. simpl.
      specialize (IHctx s0).
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      red; unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      inversion IHctx; clear IHctx; subst.
      eapply H4; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl; intros.
      red.
      do 2 rewrite _exists_sem.
      intros. destruct H5. exists x4.
      repeat match goal with
               | H : equiv_hlist _ _ _ |- _ =>
                 apply equiv_eq_eq in H
             end; subst.
      rewrite <- H. eassumption.
      reflexivity. reflexivity. }
    { intros.
      specialize (IHctx s).
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor ; [ ]
             end.
      red; unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      inversion IHctx; clear IHctx; subst.
      eapply H4; eauto.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      repeat match goal with
               | H : equiv_hlist _ _ _ |- _ =>
                 apply equiv_eq_eq in H
             end; subst.
      red. rewrite <- H by reflexivity.
      auto. }
  Qed.

  Local Existing Instance Transitive_Roption.
  Local Existing Instance Symmetric_Roption.
  Local Existing Instance Reflexive_Roption.
  Local Existing Instance Transitive_RexprT.
  Local Existing Instance Symmetric_RexprT.
  Local Existing Instance Reflexive_RexprT.

  Lemma osgD_toGoal
  : forall tus tvs ctx s g,
      Roption (RexprT tus tvs iff)
              (osgD tus tvs (toGoal (length tus) (length tvs) ctx s g))
              (match ctxD' tus tvs ctx s
                     , goalD _ _ g
               with
                 | Some F , Some gD =>
                   Some (F (fun us vs => gD us vs))
                 | _ , _ => None
               end).
  Proof.
    induction ctx; simpl.
    { intros.
      rewrite goalD_conv with (pfu := eq_sym (app_nil_r_trans _))
                                (pfv := eq_sym (app_nil_r_trans _)).
      autorewrite with eq_rw.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor
             end.
      unfold RexprT, OpenTeq, OpenTrel; simpl.
      intros.
      apply equiv_eq_eq in H; apply equiv_eq_eq in H0; subst.
      do 2 rewrite hlist_app_nil_r.
      autorewrite with eq_rw.
      reflexivity. }
    { intros.
      specialize (IHctx s (GAll t g)).
      etransitivity; [ apply IHctx | clear IHctx ].
      simpl.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; try constructor; [ ]
             end.
      reflexivity. }
    { intros.
      rewrite app_length.
      rewrite <- (countUVars_getUVars ctx).
      generalize (forgets_map_fst l (length tus + countUVars ctx) s).
      destruct (forgets (length tus + countUVars ctx) l s).
      simpl. intros; subst.
      etransitivity; [ eapply IHctx | clear IHctx ].
      simpl.
      generalize (Proper_ctxD' tus tvs ctx s0).
      destruct (ctxD' tus tvs ctx s0).
      { destruct (goal_substD (tus ++ getUVars ctx) (tvs ++ getVars ctx) l0).
        { rewrite goalD_conv with (pfu := app_ass_trans _ _ _) (pfv := eq_refl).
          autorewrite with eq_rw.
          destruct (goalD ((tus ++ getUVars ctx) ++ map fst l0) (tvs ++ getVars ctx) g); try constructor.
          inversion H; clear H; subst.
          eapply H2; clear H2.
          unfold RexprT, OpenTeq, OpenTrel; simpl; intros.
          eapply _exists_iff; intros.
          eapply equiv_eq_eq in H; eapply equiv_eq_eq in H0; subst.
          apply and_iff. reflexivity. intro.
          autorewrite with eq_rw. reflexivity. }
        { destruct (goalD ((tus ++ getUVars ctx) ++ map fst l0) (tvs ++ getVars ctx) g); constructor. } }
      { destruct (goal_substD (tus ++ getUVars ctx) (tvs ++ getVars ctx) l0); constructor. } }
    { intros.
      etransitivity; [ eapply IHctx | clear IHctx ].
      simpl.
      generalize (Proper_ctxD' tus tvs ctx s).
      destruct (propD (tus ++ getUVars ctx) (tvs ++ getVars ctx) e);
        destruct (ctxD' tus tvs ctx s); try constructor.
      destruct (goalD (tus ++ getUVars ctx) (tvs ++ getVars ctx) g); try constructor.
      inversion H; clear H; subst.
      eapply H2. simpl. reflexivity. }
  Qed.

  Section runRTac'.
    Variable tac : Ctx -> subst -> expr -> Result.

    Fixpoint runRTac' (nus nvs : nat) (ctx : Ctx) (s : subst) (g : Goal)
             {struct g}
    : Result :=
      match g with
        | GGoal e => tac ctx s e
        | GSolved => Solved s
        | GAll t g =>
          match runRTac' nus (S nvs) (CAll ctx t) s g with
            | Fail => Fail
            | Solved s => Solved s
            | More_ s g => More s (GAll t g)
          end
        | GExs tes g =>
          match remembers nus tes s with
            | None => Fail
            | Some s' =>
              match runRTac' (length tes + nus) nvs (CExs ctx (map fst tes)) s' g with
                | Fail => Fail
                | Solved s'' =>
                  Fail
                | More_ s'' g' =>
                  Fail
              end
          end
        | GHyp h g =>
          match runRTac' nus nvs (CHyp ctx h) s g with
            | Fail => Fail
            | Solved s => Solved s
            | More_ s g => More_ s (GHyp h g)
          end
        | GConj_ l r =>
          match runRTac' nus nvs ctx s l with
            | Fail => Fail
            | Solved s' => runRTac' nus nvs ctx s' r
            | More_ s' g' =>
              match runRTac' nus nvs ctx s' r with
                | Fail => Fail
                | Solved s'' => More s'' g'
                | More_ s'' g'' => More s'' (GConj_ g' g'')
              end
          end
      end.

    Definition runRTac (tus : tenv typ) (tvs : tenv typ)
               (ctx : Ctx) (s : subst) (g : Goal)
    : Result :=
      runRTac' (length tus + countUVars ctx) (length tvs + countVars ctx) ctx s g.

    Lemma More_More_ tus tvs :
      (@eq subst ==> EqGoal tus tvs ==> EqResult tus tvs)%signature
                                                         More More_.
    Proof.
      red. red. red.
      simpl. intros; subst.
      destruct x0; simpl; repeat constructor; assumption.
    Qed.
(*
    Lemma GConj_GConj_ tus tvs :
      (@eq _ ==> EqGoal tus tvs)%signature GConj GConj_.
    Proof.
      red. intros; subst.
      destruct y; simpl.
      - unfold EqGoal. intros.
        etransitivity; [ eapply osgD_toGoal | ].
        etransitivity; [ | symmetry; eapply osgD_toGoal ].
        simpl. reflexivity.
      - destruct y; try reflexivity.
        unfold EqGoal; intros.
        etransitivity; [ eapply osgD_toGoal | ].
        etransitivity; [ | symmetry; eapply osgD_toGoal ].
        simpl.
        destruct (ctxD' tus tvs ctx s); try constructor.
        destruct (goalD (tus ++ getUVars ctx) (tvs ++ getVars ctx) g); try constructor.
        reflexivity.
    Qed.
*)

    Theorem runOnGoals'_sound
    : forall tus tvs,
        (forall ctx s ge result,
           tac ctx s ge = result ->
           rtac_spec tus tvs ctx s (GGoal ge) result) ->
        rtac_sound tus tvs (fun ctx s g =>
                              runRTac' (length tus + countUVars ctx)
                                       (length tvs + countVars ctx)
                                       ctx s g).
    Proof.
      red. intros tus tvs Htac ctx s g ? ?; subst.
      revert ctx s.
      red.
      induction g; fold runRTac' in *.
      { (* All *)
        (*
        clear Htac. simpl; intros.
        specialize (IHg (CAll ctx t) s).
        simpl in *.
        rewrite <- plus_n_Sm in IHg.
        match goal with
          | H : match ?X with _ => _ end
          |- match match ?Y with _ => _ end with _ => _ end =>
            change Y with X ; consider X; intros; auto
        end.
        intros; forward_reason; split; auto.
        forward.
        generalize (osgD_toGoal tus tvs ctx s0 GSolved).
        generalize (osgD_toGoal tus tvs ctx s0 (GAll t GSolved)).
        rewrite H3.
        intro XXX; inversion XXX; clear XXX.
        simpl.
        forward; inv_all; subst.
        inversion H9; clear H9; subst.
        intros. eapply H4; clear H4.
        eapply H10 in H8; [ clear H10 | reflexivity | reflexivity ].
        eapply H7. reflexivity. reflexivity.
        generalize (Proper_ctxD' tus tvs ctx s0).
        rewrite H6. inversion 1. subst.
        eapply H11. 4: eassumption.
        2: reflexivity.
        2: reflexivity.
        repeat red. auto. *) admit. }
      { (* Ex *)
        admit. }
      { (* Hyp *)
        clear Htac.
        simpl in *. intros.
        specialize (IHg (CHyp ctx e) s).
        simpl in *.
        forward.
        forward_reason.
        destruct (runRTac' (length tus + countUVars ctx)
                           (length tvs + countVars ctx)
                           (CHyp ctx e) s g); auto.
        { intros; forward_reason.
          split; auto. simpl.
          forward; inv_all; subst.
          destruct H6.
          split.
          { clear H7.
            generalize (Proper_ctxD'_impl tus tvs ctx s0).
            generalize (Proper_ctxD'_impl tus tvs ctx s).
            Cases.rewrite_all_goal.
            do 2 (intro XXX; inversion XXX; clear XXX); subst.
            destruct H6. eexists x.
            intros.
            specialize (H6 P Q H7); clear H7.
            eapply H9.
            4: eapply H6.
            { do 5 red. red.
            2: reflexivity.
            2: reflexivity.
            4: eapply H13.
            7: eassumption.

            3: reflexivity.
            3: reflexivity.
            { do 6 red.
              

        split; auto.
        clear - H2 H4.
        generalize (osgD_toGoal tus tvs ctx s0 (GHyp e GSolved)).
        generalize (osgD_toGoal tus tvs ctx s0 GSolved).
        rewrite H2.
        destruct (osgD tus tvs (toGoal (length tus) (length tvs) ctx s0 GSolved)).
        { inversion 1; inversion 1; subst.
          forward; inv_all; subst.
          eapply H4; clear H4.
          eapply H8. reflexivity. reflexivity.
          simpl.
          eapply H3 in H6; [ | reflexivity | reflexivity ].
          generalize (Proper_ctxD' tus tvs ctx s0).
          rewrite H.
          inversion 1. subst.
          eapply H10. 4: eassumption.
          2: reflexivity.
          2: reflexivity.
          clear.
          unfold RexprT, OpenTeq, OpenTrel; simpl; intros.
          intuition. }
        { inversion 1. forward. inversion H3. } }
      { (* Conj *)
        fold runRTac' in *. clear Htac. intros ctx s.
        specialize (IHg1 ctx s).
        destruct (runRTac' (length tus + countUVars ctx)
                           (length tvs + countVars ctx) ctx s g1); auto.
        { admit. }
        { specialize (IHg2 ctx s0).
          destruct (runRTac' (length tus + countUVars ctx) (length tvs + countVars ctx) ctx
                             s0 g2); auto.
          { intros; forward_reason.
            split; auto.

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



            generalize (osgD_toGoal tus tvs ctx s (GConj_ g1 g2)).
            generalize (osgD_toGoal tus tvs ctx s0 g2).
            generalize (osgD_toGoal tus tvs ctx s g2).
            generalize (osgD_toGoal tus tvs ctx s g1).
            generalize (osgD_toGoal tus tvs ctx s0 GSolved).
            forward.
            repeat match goal with
                     | H : Roption _ (Some _) _ |- _ =>
                       inversion H ; clear H ; subst
                     | H : Roption _ _ (Some _) |- _ =>
                       inversion H ; clear H ; subst
                     | |- _ => forward; inv_all; subst
                   end.

            Print osgD.


(*
            generalize (osgD_toGoal tus tvs ctx s (GConj_ g1 g2)).
            generalize (osgD_toGoal tus tvs ctx s g1).
            generalize (osgD_toGoal tus tvs ctx s g2).
            simpl. symmetry in H11.
            Cases.rewrite_all_goal.
            rewrite <- H11.
*)
            repeat match goal with
                     | H : osgD _ _ _ = _ |- _ => clear H
                     | H : goalD _ _ _ = _ |- _ => clear H
                     | H : WellFormed_subst _ |- _ => clear H
                   end.
            generalize (Proper_ctxD' tus tvs ctx s).
            generalize (Proper_ctxD' tus tvs ctx s0).
            rewrite H9. rewrite H6.
            do 2 (intro XXX; inversion XXX; clear XXX); subst.
            (** start rewriting **)
            eapply H12; clear H12; try reflexivity.
            eapply H15 in H18; clear H15.
            unfold RexprT, OpenTeq,OpenTrel in H17.
            eapply H17 in H18; clear H17; try reflexivity.
            eapply H19 in H18; clear H19; [ | | reflexivity | reflexivity ].

            eapply H22; clear H22; [ | reflexivity | reflexivity | ].
            Focus 4.
            eapply H14; clear H14; try reflexivity.
            eapply H13; clear H13.
            eapply H16; clear H16; try reflexivity.
            eapply H19; clear H19.
            Focus 4.
            eapply H17; clear H17; try reflexivity.
            eapply H15. eassumption.
            2: reflexivity.
            2: reflexivity.
            


            inversion H7; clear H7; subst.
            forward. inv_all; subst.
            inversion H8; clear H8; subst.
            

            consider (ctxD' tus tvs ctx s0).
            { intros. revert H3. inversion H11; clear H11; subst.
              destruct (osgD tus tvs (toGoal (length tus) (length tvs) ctx s1 g)); auto.
              intros. eapply H10; clear H10. reflexivity. reflexivity.
              generalize (Proper_ctxD' tus tvs ctx s).
              rewrite H5. inversion 1. subst.
              eapply H17. symmetry in H13. 4: eapply H13.
              Focus 6.
            }
            { (** NOT TRUE!!! **)
              admit. }
            
          

}
          { intros; simpl.
            specialize (H ctx s).
            destruct (runRTac' (length tus + countUVars ctx)
                               (length tvs + countVars ctx)
                               ctx s x).
            - compute; trivial.
            - 
            intros.
                  
        
                
              
 }
      { (* Goal *)
        intros.
        specialize (Htac ctx s e _ eq_refl).
        assumption. }
      { (* Solved *)
        intros. split; auto.
        clear Htac.
        forward. }
    Qed.

  Theorem ctxD'_no_hyps
  : forall ctx tus tvs (P : exprT tus tvs Prop),
      (forall us vs, P us vs) ->
      @ctxD tus tvs ctx P.
  Proof.
    induction ctx; simpl; intros; auto; forward; subst; auto.
  Qed.


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

End parameterized.

Arguments rtac_sound {typ expr subst _ _ _ _ _} tus tvs tac : rename.

Arguments GEx {typ expr} _ _ _ : rename.
Arguments GAll {typ expr} _ _ : rename.
Arguments GHyp {typ expr} _ _ : rename.
Arguments GConj {typ expr} _ : rename.
Arguments GGoal {typ expr} _ : rename.
Arguments GSolved {typ expr} : rename.
Arguments CTop {typ expr} : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Arguments Fail {typ expr subst} : rename.
Arguments More {typ expr subst} _ _ : rename.
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
