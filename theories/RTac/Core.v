Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

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
       rewrite rev_app_distr. rewrite IHl. reflexivity.
Defined.

Definition hlist_unrev {T} {F : T -> Type} {ls} (h : hlist F (rev ls))
: hlist F ls :=
  match rev_involutive_trans ls in _ = t return hlist F t with
    | eq_refl => hlist_rev h
  end.


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

  Fixpoint getEnvs' (ctx : Ctx) (tus : tenv (ctyp typ)) (tvs : tenv typ)
  : tenv (ctyp typ) * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CEx  ctx' t => getEnvs' ctx' (mkctyp tvs t :: tus) tvs
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv (ctyp typ) * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Section runRTac'.
    Variable tac : rtac.

    Definition mapUnderEx (t : typ) (nus : nat) (r : Result) : Result :=
      match r with
        | Fail => Fail
        | Solved s' =>
          match lookup nus s' with
            | None => let s'' := s' in
                      More s'' (GEx t None GSolved)
            | Some e =>
              match drop nus s' with
                | None => DEAD
                | Some s'' => Solved s''
              end
          end
        | More s' g' =>
          match lookup nus s' with
            | None => let s'' := s' in
                      More s' (GEx t None g')
            | Some e =>
              match drop nus s' with
                | None => DEAD
                | Some s'' => More s'' (GEx t (Some e) g')
              end
          end
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


  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Section _quants.
    Context {T : Type}.
    Variable TD : T -> Type.

    Fixpoint _foralls (ls : list T)
    : OpenT TD ls Prop -> Prop :=
      match ls as ls return OpenT TD ls Prop -> Prop with
        | nil => fun P => P HList.Hnil
        | l :: ls => fun P => forall x : TD l,
                                _foralls (fun z => P (HList.Hcons x z))
      end.

    Fixpoint _exists (ls : list T)
    : OpenT TD ls Prop -> Prop :=
      match ls as ls return OpenT TD ls Prop -> Prop with
        | nil => fun P => P HList.Hnil
        | l :: ls => fun P => exists x : TD l,
                                _exists (fun z => P (HList.Hcons x z))
      end.
  End _quants.

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

(*
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
*)

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
           (* Acyclic_from tus tvs tes
        /\ *) WellFormed_goal (tus + length tes) tvs goal'
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

  Fixpoint goal_substD (tus : tenv (ctyp typ)) (tvs : tenv typ) (tes : list (typ * option expr))
  : option (OpenT ctxD (tus ++ map (fun x => mkctyp tvs (fst x)) tes) Prop).
  refine
    match tes as tes
          return option (OpenT ctxD (tus ++ map (fun x => mkctyp tvs (fst x)) tes) Prop)
    with
      | nil => Some (fun _ => True)
      | (t,None) :: tes =>
        _ (goal_substD (tus ++ mkctyp tvs t :: nil) tvs tes)
      | (t,Some e) :: tes' =>
        match exprD' (tus ++ mkctyp tvs t :: map (fun x => mkctyp tvs (fst x)) tes') tvs e t
            , goal_substD (tus ++ mkctyp tvs t :: nil) tvs tes'
        with
          | Some eD , Some sD => _
          | _ , _ => None
        end
    end.
  { rewrite app_ass_trans in sD.
    refine (Some (fun us => sD us /\ forall vs, hlist_get_cons_after_app us vs = eD us vs)). }
  { rewrite app_ass_trans. refine (fun x => x). }
  Defined.

  (** NOTE:
   ** Appending the newly introduced terms makes tactics non-local.
   ** Requiring globalness seems bad.
   ** - The alternative, however, is to expose a lot more operations
   **   on substitute
   **)
  Fixpoint goalD (tus : tenv (ctyp typ)) (tvs : tenv typ) (goal : Goal) {struct goal}
  : option (exprT tus tvs Prop).
  refine
    match goal with
      | GAll tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_foralls _ typD (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tes goal' =>
        let tus_ext := map (fun x => mkctyp tvs (fst x)) tes in
        match goalD (tus ++ tus_ext) tvs goal'
            , @goal_substD tus tvs tes with
          | None , _ => None
          | Some _ , None => None
          | Some D , Some sD =>
            Some (fun (us : hlist ctxD tus)
                      (vs : hlist typD tvs) => @_exists _ ctxD tus_ext
                                        (fun us' => sD (HList.hlist_app us us')
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

(*
  Fixpoint getUVars (ctx : Ctx) (acc : tenv (ctyp typ)) : tenv (ctyp typ) :=
    match ctx with
      | CTop => acc
      | CAll ctx' _ => getUVars ctx' acc
      | CEx  ctx' t => getUVars ctx' (mkctyp t :: acc)
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
*)

  Section ctxD.

    Fixpoint ctxD' (tus : tenv (ctyp typ)) (tvs : tenv typ) (ctx : Ctx)
             {struct ctx}
    : exprT tus tvs Prop -> Prop :=
      match ctx return exprT tus tvs Prop -> Prop with
        | CTop => fun k => forall us vs, k us vs
        | CEx ctx' t =>
          match tus as tus return exprT tus tvs Prop -> Prop with
            | t' :: tus' => fun k =>
              mkctyp tvs t = t' ->
              @ctxD' tus' tvs ctx'
                     (fun us vs => forall x : ctxD t', k (Hcons x us) vs)
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

  Definition rtac_sound (tus : tenv (ctyp typ)) (tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      match result with
        | Fail => True
        | Solved s' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let (tux,tvx) := getEnvs ctx in
          let tus' := tus ++ tux in
          let tvs' := tvs ++ tvx in
          match propD  tus' tvs' g
              , substD tus' s
              , substD tus' s'
          with
            | None , _ , _
            | Some _ , None , _ => True
            | Some _ , Some _ , None => False
            | Some gD , Some sD , Some sD' =>
              @ctxD' (rev tus') (rev tvs') ctx
                     (fun us vs =>
                        let us : hlist ctxD tus' := hlist_unrev us in
                        let vs : hlist typD tvs' := hlist_unrev vs in
                        sD' us ->
                        sD us /\ gD us vs)
          end
        | More s' g' =>
          WellFormed_subst s ->
          WellFormed_subst s' /\
          let (tux,tvx) := getEnvs ctx in
          let tus' := tus ++ tux in
          let tvs' := tvs ++ tvx in
          match propD  tus' tvs' g
              , substD tus' s
              , goalD  tus' tvs' g'
              , substD tus' s'
          with
            | None , _ , _ , _
            | Some _ , None , _ , _ => True
            | Some _ , Some _ , None , _
            | Some _ , Some _ , Some _ , None => False
            | Some gD , Some sD , Some gD' , Some sD' =>
              @ctxD' (rev tus') (rev tvs') ctx
                     (fun us vs =>
                        let us : hlist ctxD tus' := hlist_unrev us in
                        let vs : hlist typD tvs' := hlist_unrev vs in
                        sD' us -> gD' us vs ->
                        sD us /\ gD us vs)
          end
      end.

(*
  Section at_bottom.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Variable gt : list typ -> list typ -> subst -> option expr -> m Goal.

    Let under (gt : Goal -> Goal) (x : m Goal) : m Goal :=
      bind x (fun x => ret (gt x)).

    Fixpoint at_bottom tus tvs (g : Goal) : m Goal :=
      match g with
        | GAll x g' => under (GAll x) (at_bottom tus (tvs ++ x :: nil) g')
        | GEx  x g' => under (GEx  x) (at_bottom (tus ++ x :: nil) tvs g')
        | GHyp x g' => under (GHyp x) (at_bottom tus tvs g')
        | GGoal s e => gt tus tvs s e
      end.
  End at_bottom.
*)
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
  : forall T F ls P Q,
      (forall x, P x <-> Q x) ->
      (@_exists T F ls P <-> @_exists _ F ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply exists_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.
  Lemma _forall_iff
  : forall T F ls P Q,
      (forall x, P x <-> Q x) ->
      (@_foralls T F ls P <-> @_foralls T F ls Q).
  Proof.
    clear.
    induction ls; simpl; intros.
    + eapply H.
    + apply forall_iff; intro. eapply IHls.
      intro; eapply H.
  Qed.

(*
  Lemma at_bottom_sound_option
  : forall goal tus tvs f goal',
      (forall tus' tvs' s e e',
         f (tus ++ tus') (tvs ++ tvs') s e = Some e' ->
         WellFormed_subst s ->
         match goalD (tus ++ tus') (tvs ++ tvs') (GGoal s e)
             , goalD (tus ++ tus') (tvs ++ tvs') e'
         with
           | None , _ => True
           | Some _ , None => False
           | Some g , Some g' =>
             forall us vs,
               g' us vs -> g us vs
         end) ->
      at_bottom f tus tvs goal = Some goal' ->
      forall (Hwf : WellFormed_goal goal),
      match goalD tus tvs goal
          , goalD tus tvs goal'
      with
        | None , _ => True
        | Some _ , None => False
        | Some g , Some g' =>
          forall us vs,
            g' us vs -> g us vs
      end.
  Proof.
    induction goal; simpl; intros.
    { forwardy. inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; auto.
      { simpl. forward. auto. }
      { intros.
        specialize (H tus' (t :: tvs') s e).
        rewrite app_ass in H1. simpl in *.
        eapply H in H1; clear H; auto.
        forward.
        rewrite substD_conv
           with (pfu := eq_refl _) (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H.
        unfold propD in *.
        rewrite exprD'_typ0_conv with (pfu := eq_refl _)
             (pfv := eq_sym (HList.app_ass_trans _ _ _)) in H.
        simpl in *.
        unfold ResType in *.
        autorewrite with eq_rw in *.
        destruct e; forwardy.
        { inv_all; subst.
          rewrite H in *.
          autorewrite with eq_rw in H3.
          forwardy.
          rewrite H3 in *.
          inv_all; subst.
          rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (HList.app_ass_trans _ _ _)).
          simpl.
          forwardy.
          autorewrite with eq_rw.
          rewrite H1.
          intros us vs. autorewrite with eq_rw.
          clear - H4.
          match goal with
            | |- _ _ match ?X with _ => _ end ->
                 _ _ match ?Y with _ => _ end /\
                 _ _ match ?Z with _ => _ end =>
              change X with Y ; change Z with Y ; destruct Y
          end.
          eauto. }
        { rewrite H in *.
          rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (HList.app_ass_trans _ _ _)).
          simpl.
          forwardy.
          autorewrite with eq_rw.
          rewrite H1. intros.
          inv_all; subst.
          revert H6.
          match goal with
            | |- match ?X with _ => _ end _ _ ->
                 match ?Y with _ => _ end _ _ =>
              change Y with X ; destruct X
          end. auto. } } }
    { forwardy; inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; auto.
      + simpl; forward; eauto.
        destruct H3. eauto.
      + intros.
        rewrite goalD_conv
           with (pfu := eq_sym (HList.app_ass_trans _ _ _))
                (pfv := eq_refl).
        autorewrite with eq_rw.
        simpl. forward.
        rewrite HList.app_ass_trans in H1.
        simpl in H1.
        eapply H in H1; clear H; eauto.
        destruct e; forward.
        - inv_all; subst.
          revert H7. autorewrite with eq_rw.
          eauto.
        - inv_all; subst.
          revert H6. autorewrite with eq_rw.
          eauto. }
    { forwardy; inv_all; subst.
      eapply IHgoal in H0; clear IHgoal; eauto.
      + simpl; forward; eauto.
        inv_all. subst.
        eapply _impls_sem; intro.
        eapply _impls_sem in H5; eauto. }
    { specialize (H nil nil s o goal').
      simpl in H.
      repeat rewrite HList.app_nil_r_trans in H.
      eapply H in H0; clear H; auto. }
  Qed.
*)

  Lemma _exists_sem : forall T F ls P,
                        @_exists T F ls P <->
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
  Lemma _forall_sem : forall T F ls P,
                        @_foralls T F ls  P <->
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

(*
  Lemma at_bottom_WF_option
  : forall f,
      (forall a b c d g,
         f a b c d = Some g ->
         WellFormed_subst c ->
         WellFormed_goal g) ->
    forall g tus tvs g',
      at_bottom f tus tvs g = Some g' ->
      WellFormed_goal g ->
      WellFormed_goal g'.
  Proof.
    clear.
    induction g; simpl; intros; forwardy; inv_all; subst; simpl in *; eauto.
  Qed.
*)

(*
  Lemma WellFormed_goal_GAll
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GAll g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GEx
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GEx g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GHyp
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GHyp g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
*)

(*
  Instance Monad_writer_nat : Monad (fun T : Type => (T * nat)%type) :=
  { ret := fun T x => (x,0)
  ; bind := fun T U c c1 =>
              let (x,n) := c in
              let (y,n') := c1 x in
              (y,n+n')
  }.

  (** On [Proved], I need to check, that means that I probably need to do
   ** deltas so that I know where I need to pull to...
   **)
  Definition with_new_uvar (t : typ) (k : nat -> rtac)
  : rtac :=
    fun g =>
      let (g',n) :=
          at_bottom (m := fun T => (T * nat))%type
                    (fun tus _ s g => (GEx t (GGoal s g), length tus)) nil nil g
      in
      k n g'.
*)
(*
  Axiom ty : typ.
  Axiom s : subst.

  Eval compute in fun (f : nat -> rtac) => with_new_uvar ty f (GGoal s None).

  Definition with_new_var (t : typ) (k : nat -> rtac)
  : rtac :=
    fun g =>
      let (g',uv) :=
          at_bottom (fun _ tvs g => (GAll t g, length tvs)) nil nil g
      in
      k uv g'.
*)

  (** NOTE: Probably not neccessary **)
  Fixpoint closeGoal (ctx : Ctx) (s : subst) (g : Goal) (nus : nat)
  : Goal :=
    match ctx with
      | CTop => g
      | CAll c t => closeGoal c s (GAll t g) nus
      | CEx  c t =>
        closeGoal c s (GEx t (lookup nus s) g) (S nus)
      | CHyp c h => closeGoal c s (GHyp h g) nus
    end.

  Theorem ctxD'_no_hyps
  : forall ctx tus tvs (P : exprT _ _ Prop),
      (forall us vs, P us vs) ->
      @ctxD' tus tvs ctx P.
  Proof.
    induction ctx; simpl; intros; auto; forward; subst; auto.
  Qed.

End parameterized.

(*
Arguments propD {typ expr _ _ _} tus tvs e : rename.
Arguments rtac_sound {typ expr subst} tus tvs tac : rename.
*)
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
