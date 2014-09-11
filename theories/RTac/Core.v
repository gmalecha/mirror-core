Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.STac.Core.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Can I do alternation if I can do strengthening of both
 ** unification variables and regular variables?
 ** 1) This means that substD needs strengthening
 ** 2) It also means that hypotheses need to be eliminatable
 **
 **    goal :=
 **      Alls : list typ -> goal -> goal
 **    | Exs : list typ -> goal -> goal
 **    | Hyps : list expr -> goal -> goal
 **    | Goal : expr -> goal.
 **
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  (** NOTE: It seems for performance this should be inverted, otherwise
   ** every operation is going to be very expensive.
   **)
  Inductive Goal :=
  | GAlls : typ -> Goal -> Goal
  | GExs  : typ -> Goal -> Goal
  | GHyps : expr -> Goal -> Goal
  | GGoal : subst -> option expr -> Goal.

  Definition Result := option Goal.

  (** Treat this as opaque! **)
  Definition rtac : Type :=
    Goal -> Result.

  Definition runRTac (tac : rtac) (g : Goal) : option Goal :=
    tac g.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.

  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Fixpoint _foralls (ls : list typ)
  : (HList.hlist typD ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist typD ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD l,
                              _foralls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (HList.hlist typD ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist typD ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD l,
                              _exists (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> _impls ls P
    end.

  Fixpoint WellFormed_goal (goal : Goal) : Prop :=
    match goal with
      | GAlls _ goal'
      | GExs _ goal'
      | GHyps _ goal' => WellFormed_goal goal'
      | GGoal s _ => WellFormed_subst s
    end.

  (** NOTE:
   ** Appending the newly introduced terms makes tactics non-local.
   ** Requiring globalness seems really bad.
   **)
  Fixpoint goalD (tus tvs : list typ) (goal : Goal)
  : ResType tus tvs Prop :=
    match goal with
      | GAlls tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_foralls (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tu goal' =>
        match goalD (tus ++ tu :: nil) tvs goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_exists (tu :: nil)
                      (fun us' => D (HList.hlist_app us us') vs))
        end
      | GHyps hyp' goal' =>
        match mapT (T:=list) (F:=option) (propD tus tvs) (hyp' :: nil) with
          | None => None
          | Some hs =>
            match goalD tus tvs goal' with
              | None => None
              | Some D =>
                Some (fun us vs => _impls (map (fun x => x us vs) hs) (D us vs))
            end
        end
      | GGoal sub' None =>
        match substD tus tvs sub' with
          | Some sD => Some (fun us vs => sD us vs)
          | _ => None
        end
      | GGoal sub' (Some goal') =>
        match substD tus tvs sub'
            , propD tus tvs goal'
        with
          | Some sD , Some gD =>
            Some (fun (us : HList.hlist typD tus)
                      (vs : HList.hlist typD tvs)  => sD us vs /\ gD us vs)
          | _ , _ => None
        end
    end.

  (** The worry is that this isn't going to be strong enough,
   ** especially when it comes to substitutions.
   **)
  Definition rtac_sound tus tvs (tac : rtac) : Prop :=
    forall g g',
      tac g = Some g' ->
      WellFormed_goal g ->
      WellFormed_goal g' /\
      match goalD tus tvs g
          , goalD tus tvs g'
      with
        | None , _ => True
        | Some _ , None => False
        | Some g , Some g' =>
          forall us vs,
            g' us vs ->
            g us vs
      end.

  Section at_bottom.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Variable gt : list typ -> list typ -> subst -> option expr -> m Goal.

    Let under (gt : Goal -> Goal) (x : m Goal) : m Goal :=
      bind x (fun x => ret (gt x)).

    Fixpoint at_bottom tus tvs (g : Goal) : m Goal :=
      match g with
        | GAlls x g' => under (GAlls x) (at_bottom tus (tvs ++ x :: nil) g')
        | GExs  x g' => under (GExs  x) (at_bottom (tus ++ x :: nil) tvs g')
        | GHyps x g' => under (GHyps x) (at_bottom tus tvs g')
        | GGoal s e => gt tus tvs s e
      end.
  End at_bottom.

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

  Lemma WellFormed_goal_GAlls
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GAlls g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GExs
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GExs g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.
  Lemma WellFormed_goal_GHyps
  : forall ls g,
      WellFormed_goal g <-> WellFormed_goal (fold_right GHyps g ls).
  Proof.
    clear. induction ls; simpl; intros; auto.
    reflexivity.
  Qed.

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
                    (fun tus _ s g => (GExs t (GGoal s g), length tus)) nil nil g
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
          at_bottom (fun _ tvs g => (GAlls t g, length tvs)) nil nil g
      in
      k uv g'.
*)

End parameterized.

Arguments propD {typ expr _ _ _} tus tvs e : rename.
Arguments rtac_sound {typ expr subst _ _ _ _ _} tus tvs tac : rename.
Arguments GExs {typ expr subst} _ _ : rename.
Arguments GAlls {typ expr subst} _ _ : rename.
Arguments GHyps {typ expr subst} _ _ : rename.
Arguments GGoal {typ expr subst} _ _ : rename.