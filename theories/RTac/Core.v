Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

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

  (** NOTE: For performance this should be inverted, otherwise
   ** every operation is going to be expensive.
   ** - Solving this problem is the purpose of [Ctx]
   **)
  (** TODO: Make [GAll] and [GEx] more symmetric **)
  Inductive Goal :=
  | GAll    : typ -> Goal -> Goal
  (** The first element in the list has the lowest index
   ** in the final goal.
   **)
  | GExs    : list (typ * option expr) -> Goal -> Goal
  | GHyp    : expr -> Goal -> Goal
  | GConj_   : list Goal -> Goal
  | GGoal   : expr -> Goal
  | GSolved : Goal.

  Definition GAlls (ts : list typ) (g : Goal) : Goal :=
    fold_right (fun x y => GAll x y) g ts.

  Definition GEx (t : typ) (e : option expr) (g : Goal) : Goal :=
    match g with
      | GExs tes g' => GExs ((t,e) :: tes) g'
      | _ => GExs ((t, e) :: nil) g
    end.

  Definition GConj (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | g :: nil => g
      | _ :: _ :: _ => GConj_ ls
    end.

  Inductive Ctx :=
  | CTop
  | CAll : Ctx -> typ -> Ctx
  | CEx  : Ctx -> typ -> Ctx
  | CHyp : Ctx -> expr -> Ctx.

  (** StateT subst Option Goal **)
  Inductive Result :=
  | Fail
  | More   : subst -> Goal -> Result
  | Solved : subst -> Result.

  Definition fromResult (r : Result) : option (subst * Goal) :=
    match r with
      | Fail => None
      | More s g => Some (s, g)
      | Solved s => Some (s, GSolved)
    end.

  Definition DEAD : Result.
    exact Fail.
  Qed.

  (** Treat this as opaque! **)
  Definition rtac : Type :=
    Ctx -> subst -> expr -> Result.

  Fixpoint countVars' (ctx : Ctx) acc : nat :=
    match ctx with
      | CTop => acc
      | CAll ctx' t => countVars' ctx' (S acc)
      | CEx  ctx' _
      | CHyp ctx' _ => countVars' ctx' acc
    end.

  Fixpoint countUVars' (ctx : Ctx) acc : nat :=
    match ctx with
      | CTop => acc
      | CEx  ctx' t => countUVars' ctx' (S acc)
      | CAll ctx' _
      | CHyp ctx' _ => countUVars' ctx' acc
    end.

  Definition countVars ctx := countVars' ctx 0.
  Definition countUVars ctx := countUVars' ctx 0.

  Fixpoint getEnvs' (ctx : Ctx) (tus tvs : tenv typ)
  : tenv typ * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CEx  ctx' t => getEnvs' ctx' (t :: tus) tvs
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv typ * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Section runRTac'.
    Variable tac : rtac.

    (** This is sound but it could be more liberal
     **)
    Definition mapUnderEx (t : typ) (nus : nat) (r : Result) : Result :=
      match r with
        | Fail => Fail
        | Solved s' =>
          match forget nus s' with
            | (s'',None) => More s'' (GEx t None GSolved)
            | (s'',Some e) =>
              if strengthenU nus 1 s'' then
                Solved s''
              else Fail
          end
        | More s' g' =>
          let '(s'',e) := forget nus s' in
          More s'' (GEx t e g')
      end.

    Fixpoint runRTac' (ctx : Ctx) (s : subst) (g : Goal) (nus nvs : nat) {struct g}
    : Result :=
      match g with
        | GGoal e => tac ctx s e
        | GSolved => Solved s
        | GAll t g =>
          match runRTac' (CAll ctx t) s g nus (S nvs) with
            | Fail => Fail
            | Solved s => Solved s
            | More s g => More s (GAll t g)
          end
        | GExs tes g =>
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
                       | None => DEAD
                       | Some s' =>
                         mapUnderEx t nus (go (S nus) tes s' (CEx ctx t))
                     end
                 end
             end) nus tes s ctx
        | GHyp h g =>
          match runRTac' (CHyp ctx h) s g nus nvs with
            | Fail => Fail
            | Solved s => Solved s
            | More s g => More s (GHyp h g)
          end
        | GConj_ gs =>
          (fix do_each (gs : list Goal) (s : subst)
               (acc : list Goal -> subst -> Result)
           : Result :=
             match gs with
               | nil => acc nil s
               | g :: gs =>
                 match runRTac' ctx s g nus nvs with
                   | Fail => Fail
                   | Solved s => do_each gs s acc
                   | More s g =>
                     do_each gs s (fun other s => acc (g :: other) s)
                 end
             end) gs s
                  (fun rem s =>
                     match rem with
                       | nil => Solved s
                       | g :: nil => More s g
                       | _ :: _ => More s (GConj rem)
                     end)
      end.

    Definition runRTac (ctx : Ctx) (s : subst) (g : Goal)
    : Result :=
      runRTac' ctx s g (countUVars ctx) (countVars ctx).
  End runRTac'.

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

  Fixpoint _foralls (ls : list typ)
  : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD l,
                              _foralls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (OpenT typD ls Prop) -> Prop :=
    match ls as ls return (OpenT typD ls Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD l,
                              _exists (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> _impls ls P
    end.

  Section _and.
    Context {A B : Type}.
    Variables (a : A) (b : B).
    Fixpoint _and (ls : list (A -> B -> Prop)) :=
      match ls with
        | nil => True
        | l :: nil => l a b
        | l :: ls => l a b /\ _and ls
      end.
  End _and.

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

  (** Well_formedness is about acyclicity, but we don't have enough now
   ** to guarantee that.
   ** We could make a acyclic judgement on a map and just construct the map.
   ** Either way things are getting a lot more complex here than I wanted them
   ** too.
   **)
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

  Fixpoint hlist_mapT {T : Type} {F : T -> Type}
           {ls : list T} (h : HList.hlist (fun x => option (F x)) ls)
  : option (HList.hlist F ls) :=
    match h in HList.hlist _ ls return option (HList.hlist F ls) with
      | HList.Hnil => Some (HList.Hnil)
      | HList.Hcons _ _ x y =>
        match x , hlist_mapT y with
          | Some x , Some y => Some (HList.Hcons x y)
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
  : option (exprT tus tvs Prop).
  refine
    match goal with
      | GAll tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_foralls (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tes goal' =>
        let tus_ext := map fst tes in
        match goalD (tus ++ tus_ext) tvs goal'
            , goal_substD tus tvs tes with
          | None , _ => None
          | Some _ , None => None
          | Some D , Some sD =>
            Some (fun us vs => @_exists tus_ext
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
      | GConj_ ls =>
        (** This is actually:
        match mapT (T:=list) (F:=option) (goalD tus tvs) ls with
          | None => None
          | Some lD =>
            Some (fun us vs => _and us vs lD)
        end
        **)
        match mapT_list (F:=option) (goalD tus tvs) ls with
          | None => None
          | Some lD => Some (fun us vs => _and us vs lD)
        end
      | GSolved => Some (fun _ _ => True)
      | GGoal goal' => propD tus tvs goal'
    end.
  Defined.

  Fixpoint getUVars (ctx : Ctx) (acc : tenv typ) : tenv typ :=
    match ctx with
      | CTop => acc
      | CAll ctx' _ => getUVars ctx' acc
      | CEx  ctx' t => getUVars ctx' (t :: acc)
      | CHyp ctx' _ => getUVars ctx' acc
    end.
  Fixpoint getVars (ctx : Ctx) (acc : tenv typ) : tenv typ :=
    match ctx with
      | CTop => acc
      | CAll ctx' t => getVars ctx' (t :: acc)
      | CEx  ctx' _ => getVars ctx' acc
      | CHyp ctx' _ => getVars ctx' acc
    end.

  Theorem getEnvs'_getUVars_getVars
  : forall ctx tus tvs,
      getEnvs' ctx tus tvs = (getUVars ctx tus, getVars ctx tvs).
  Proof.
    clear. induction ctx; simpl; intros; auto.
  Qed.

  Theorem getEnvs_getUVars_getVars
  : forall ctx,
      getEnvs ctx = (getUVars ctx nil, getVars ctx nil).
  Proof.
    intros. rewrite <- (getEnvs'_getUVars_getVars ctx nil nil).
    unfold getEnvs. destruct (getEnvs' ctx nil nil); reflexivity.
  Qed.

  Section ctxD.

    Fixpoint ctxD' (tus tvs : tenv typ) (ctx : Ctx)
             {struct ctx}
    : exprT tus tvs Prop -> Prop :=
      match ctx return exprT tus tvs Prop -> Prop with
        | CTop => fun k => forall us vs, k us vs
        | CEx ctx' t =>
          match tus as tus return exprT tus tvs Prop -> Prop with
            | t' :: tus' => fun k =>
              t = t' ->
              @ctxD' tus' tvs ctx'
                     (fun us vs => forall x : typD t', k (Hcons x us) vs)
            | nil => fun _ => True
          end
        | CAll ctx' t =>
          match tvs as tvs return exprT tus tvs Prop -> Prop with
            | t' :: tvs' => fun k =>
              t = t' ->
              @ctxD' tus tvs' ctx'
                     (fun us vs => forall x : typD t', k us (Hcons x vs))
            | nil => fun _ => True
          end
        | CHyp ctx' h =>
          match propD (rev tus) (rev tvs) h with
            | None => fun _ => True
            | Some P => fun k =>
              @ctxD' tus tvs ctx' (fun us vs => P (hlist_rev us) (hlist_rev vs) -> k us vs)
          end
      end.


  End ctxD.

  Definition rtac_sound (tus tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      match result with
        | Fail => True
        | Solved s' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let tus' := tus ++ getUVars ctx nil in
          let tvs' := tvs ++ getVars ctx nil in
          match propD  tus' tvs' g
              , substD tus' tvs' s
              , substD tus' tvs' s'
          with
            | None , _ , _
            | Some _ , None , _ => True
            | Some _ , Some _ , None => False
            | Some gD , Some sD , Some sD' =>
              @ctxD' (rev tus') (rev tvs') ctx
                     (fun us vs =>
                        let us : hlist typD tus' := hlist_unrev us in
                        let vs : hlist typD tvs' := hlist_unrev vs in
                        sD' us vs ->
                        sD us vs /\ gD us vs)
          end
        | More s' g' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let tus' := tus ++ getUVars ctx nil in
          let tvs' := tvs ++ getVars ctx nil in
          match propD  tus' tvs' g
              , substD tus' tvs' s
              , goalD  tus' tvs' g'
              , substD tus' tvs' s'
          with
            | None , _ , _ , _
            | Some _ , None , _ , _ => True
            | Some _ , Some _ , None , _
            | Some _ , Some _ , Some _ , None => False
            | Some gD , Some sD , Some gD' , Some sD' =>
              @ctxD' (rev tus') (rev tvs') ctx
                     (fun us vs =>
                        let us : hlist typD tus' := hlist_unrev us in
                        let vs : hlist typD tvs' := hlist_unrev vs in
                        sD' us vs -> gD' us vs ->
                        sD us vs /\ gD us vs)
          end
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

  Lemma _impls_sem
  : forall ls P,
      _impls ls P <-> (Forall (fun x => x) ls -> P).
  Proof.
    induction ls; simpl; intros.
    + intuition.
    + rewrite IHls. intuition.
      inversion H0. eapply H; eauto.
  Qed.
  Lemma _exists_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_exists ls P <-> @_exists ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply exists_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.
  Lemma _forall_iff
  : forall ls P Q,
      (forall x, P x <-> Q x) ->
      (@_foralls ls P <-> @_foralls ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply forall_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.

  Lemma _exists_sem : forall ls P,
                        _exists (ls := ls) P <->
                        exists x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. exists HList.Hnil. auto.
      destruct H. rewrite (HList.hlist_eta x) in H.
      assumption.
    - intros. split.
      + destruct 1.
        eapply IHls in H.
        destruct H. eauto.
      + destruct 1.
        exists (HList.hlist_hd x).
        eapply IHls.
        exists (HList.hlist_tl x).
        rewrite (HList.hlist_eta x) in H.
        assumption.
  Qed.
  Lemma _forall_sem : forall ls P,
                        _foralls (ls := ls) P <->
                        forall x, P x.
  Proof.
    clear. induction ls; simpl; auto.
    - intuition. rewrite (HList.hlist_eta x).
      assumption.
    - intros. split.
      + intros.
        rewrite (HList.hlist_eta x).
        eapply IHls in H.
        eapply H.
      + intros.
        eapply IHls.
        intros. eapply H.
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

  Fixpoint toGoal (ctx : Ctx) (s : subst) (g : Goal)
           (su : nat)
           (un vn : nat)
  : option (subst * Goal) :=
    match ctx with
      | CTop => Some (s, g)
      | CAll ctx' l =>
        match vn with
          | 0 => (** STUCK **)
            None
          | S vn' =>
            (** TODO: Drop var **)
            if strengthenU un su s then
              if strengthenV vn' 1 s then
                toGoal ctx' s g 0 un vn'
              else
                None
            else
              None
        end
      | CEx  ctx' l =>
        match un with
          | 0 => (** STUCK **)
            None
          | S un' =>
            let '(s',ne) := forget un' s in
            match ne with
              | None =>
                toGoal ctx' s' (GEx l ne g) (S su) un' vn
              | Some e =>
                toGoal ctx' s' (GEx l (Some e) g) (S su) un' vn
            end
        end
      | CHyp ctx' h =>
        if strengthenU un su s then
          toGoal ctx' s (GHyp h g) 0 un vn
        else
          None
    end.

  Definition osgD (tus tvs : tenv typ) (osg : option (subst * Goal))
  : option (exprT tus tvs Prop) :=
    match osg with
      | None => None
      | Some sg =>
        let (s,g) := sg in
        match goalD tus tvs g
            , substD tus tvs s
        with
          | Some gD , Some sD =>
            Some (fun us vs => sD us vs /\ gD us vs)
          | _ , _ => None
        end
    end.

  Definition rtac_sound2 (tus tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      match result with
        | Fail => True
        | Solved s' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let tus' := tus ++ getUVars ctx nil in
          let tvs' := tvs ++ getVars ctx nil in
          match osgD tus tvs (toGoal ctx s (GGoal g) 0 (length tus') (length tvs'))
              , substD tus tvs s'
          with
            | None , _ => True
            | Some _ , None => False
            | Some gD , Some sD' =>
              forall us vs,
                sD' us vs ->
                gD us vs
          end
        | More s' g' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let tus' := tus ++ getUVars ctx nil in
          let tvs' := tvs ++ getVars ctx nil in
          match osgD tus tvs (toGoal ctx s (GGoal g) 0 (length tus') (length tvs'))
              , osgD tus tvs (toGoal ctx s' g'  0 (length tus') (length tvs'))
          with
            | None , _ => True
            | Some _ , None => False
            | Some gD , Some gD' =>
              forall us vs,
                gD' us vs -> gD us vs
          end
      end.

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

  Lemma forall_hlist_nil
  : forall T (F : T -> Type) (P : _ -> Prop),
      (forall hs : hlist F nil, P hs) <-> P Hnil.
  Proof.
    clear; split; eauto.
    intros. rewrite hlist_eta. assumption.
  Qed.
  Lemma forall_hlist_cons
  : forall T (F : T -> Type) l ls (P : _ -> Prop),
      (forall hs, P hs) <->
      (forall (h : F l) (hs : hlist F ls), P (Hcons h hs)).
  Proof.
    clear. intros.
    split; eauto; intros.
    rewrite hlist_eta. eauto.
  Qed.
  Lemma forall_hlist_app
  : forall T (F : T -> Type) ls' ls (P : _ -> Prop),
      (forall hs, P hs) <->
      (forall (hs : hlist F ls) (hs' : hlist F ls'), P (hlist_app hs hs')).
  Proof.
    clear. induction ls; simpl.
    { intros. rewrite forall_hlist_nil. reflexivity. }
    { intros. repeat rewrite forall_hlist_cons.
      eapply forall_iff; intro.
      apply IHls. }
  Qed.

  Lemma forall_comm : forall (A B : Type) (P : A -> B -> Prop),
                        (forall x y, P x y) <->
                        (forall y x, P x y).
  Proof. clear. intuition. Qed.


  Lemma Hcons_cast2
  : forall T (F : T -> Type) l ls ls' x hs (pf : ls = ls'),
      Hcons x match pf in _ = Z return hlist F Z with
                | eq_refl => hs
              end =
      match pf in _ = Z return hlist F (l :: Z) with
        | eq_refl => Hcons x hs
      end.
  Proof.
    clear. destruct pf. reflexivity.
  Qed.

  Lemma hlist_rev'_hlist_rev_hlist_app
  : forall T (F : T -> Type) ls (h : hlist F ls) ls' (h' : hlist F ls'),
      hlist_rev' h h' = hlist_app (hlist_rev h) h'.
  Proof.
    clear.
    induction h; simpl; auto.
    intros. rewrite IHh; clear IHh.
    unfold hlist_rev. simpl.
    Lemma app_nil_r_trans_app
    : forall T (ls' ls : list T),
        app_nil_r_trans (ls ++ ls') =
        eq_trans (app_ass_trans ls ls' nil)
                 (f_equal (app ls) (app_nil_r_trans ls')).
    Proof.
      clear.
      induction ls; simpl.
      { intros; destruct (app_nil_r_trans ls'). reflexivity. }
      { intros. rewrite IHls; clear IHls.
        destruct (app_nil_r_trans ls').
        reflexivity. }
    Qed.
  Admitted.

  Lemma hlist_rev_rw
  : forall T (F : T -> Type) ls (P : _ -> Prop),
      (forall us : hlist F (rev ls), P (hlist_unrev us)) <->
      (forall us : hlist F ls, P us).
  Proof.
    clear. unfold hlist_unrev.
    intros.
    induction ls; simpl.
    { eapply forall_iff. intro.
      rewrite (hlist_eta x). reflexivity. }
    { rewrite forall_hlist_app.
      repeat setoid_rewrite forall_hlist_cons.
      setoid_rewrite forall_hlist_nil.
      rewrite forall_comm.
      eapply forall_iff; intro.
      unfold eq_ind_r, eq_ind, eq_rect, eq_rec.
      rewrite <- IHls; clear IHls.
      apply forall_iff; intro.
      generalize dependent (rev_involutive_trans ls).
      unfold hlist_rev.
      simpl. generalize dependent (rev ls).
      intros; subst. simpl.
      match goal with
        | |- _ ?X <-> _ ?Y =>
          cutrewrite (X = Y); try reflexivity
      end.
      clear.
      induction x0.
      { simpl. reflexivity. }
      { simpl. unfold eq_ind_r, eq_ind, eq_rect, eq_rec.
        revert IHx0.
        autorewrite with eq_rw.
        intros.
        generalize dependent (hlist_app x0 (Hcons x Hnil)).
        generalize dependent (rev_app_distr_trans ls (a :: nil)).
        intros.
        rewrite hlist_rev'_hlist_rev_hlist_app with (h' := Hcons f Hnil).
        rewrite hlist_rev'_hlist_rev_hlist_app with (h' := Hcons f Hnil).
        unfold hlist_rev.
        generalize dependent (hlist_rev' h Hnil).
        generalize dependent (hlist_rev' x0 Hnil).
        generalize dependent (Hcons f Hnil).
        generalize dependent (rev (ls ++ a :: nil)).
        intros; subst; simpl in *.
        unfold eq_trans, f_equal in *.
        generalize dependent (app_nil_r_trans (rev ls)).
        generalize dependent (app_nil_r_trans (rev ls ++ l :: nil)).
        generalize dependent (app_ass_trans (rev ls) (l :: nil) nil).
        generalize dependent (rev ls).
        intros.
        generalize dependent ((l0 ++ l :: nil) ++ nil).
        intros.
        subst l1.
        simpl.
        generalize dependent (l0 ++ nil).
        intros; subst. subst.
        simpl.
        clear.
        generalize dependent (hlist_app h1 h0).
        intro. rewrite Hcons_cast2.
        generalize dependent (Hcons x h).
        intros.
        simpl in *.
        generalize dependent (l0 ++ l :: nil).
        destruct e0. reflexivity. } }
  Qed.

  Theorem rtac_sound_rtac_sound2
  : forall tus tvs tac,
      rtac_sound tus tvs tac <-> rtac_sound2 tus tvs tac.
  Proof.
    unfold rtac_sound, rtac_sound2; intros.
    do 4 (eapply forall_iff; intro).
    eapply impl_iff; [ reflexivity | intros; subst ].
    destruct (tac x x0 x1).
    { reflexivity. }
    { eapply impl_iff; [ reflexivity | intro ].
      eapply and_iff; [ reflexivity | intro ].
      clear. revert tus tvs x0 x1 s g.
      (** TODO: this is a very complex proof because
       ** toGoal is so complicated
       **)
(*
      induction x.
      { simpl.
        intros.
        unfold propD.
        rewrite exprD'_typ0_conv
           with (pfu := app_nil_r_trans tus) (pfv := app_nil_r_trans tvs).
        repeat rewrite goalD_conv
           with (pfu := app_nil_r_trans tus) (pfv := app_nil_r_trans tvs).
        repeat rewrite substD_conv
           with (pfu := app_nil_r_trans tus) (pfv := app_nil_r_trans tvs).
        autorewrite with eq_rw.
        forward.
        symmetry.
        rewrite <- hlist_rev_rw.
        eapply forall_iff; intro.
        rewrite <- hlist_rev_rw.
        eapply forall_iff; intro.
        intuition. }
      { simpl.
*)
  Abort.

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
