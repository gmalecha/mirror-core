Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
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

  (** This is a way to put everything inside there,
   ** an alternative representation is to use a simpler type, i.e.
   **     [list (All | Ex | Hyp)]
   ** to interpret the flattened environments
   **)
  (** NOTE: It seems for performance this should be inverted, otherwise
   ** every operation is going to be very expensive.
   **)
  Inductive Goal :=
  | GAlls : typ -> Goal -> Goal
  | GExs  : typ -> Goal -> Goal
  | GHyps : expr -> Goal -> Goal
  | GGoal : subst -> option expr -> Goal.

  (** GoalD **)

  Definition Result := option Goal.

  Definition rtac : Type :=
    Goal -> Result.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Let propD := @exprD'_typ0 _ _ _ _ Prop _.

(*
  Definition propD (tus tvs : list typ) (goal : expr) : ResType tus tvs Prop :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return ResType tus tvs Prop with
      | None => None
      | Some val =>
        Some match typ0_cast nil in _ = T return HList.hlist _ tus -> HList.hlist _ tvs -> T with
               | eq_refl => val
             end
    end.
*)

  Fixpoint _foralls (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD nil l,
                              _foralls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD nil l,
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
            Some (fun (us : HList.hlist (typD nil) tus)
                      (vs : HList.hlist (typD nil) tvs)  => sD us vs /\ gD us vs)
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

  Definition THEN (c1 c2 : rtac) : rtac :=
    fun gl =>
      match c1 gl with
        | Some gl' => c2 gl'
        | None => None
      end.

  Theorem THEN_sound
  : forall tus tvs tac1 tac2,
      rtac_sound tus tvs tac1 ->
      rtac_sound tus tvs tac2 ->
      rtac_sound tus tvs (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros.
    forward.
    eapply H in H1; clear H.
    eapply H1 in H2; clear H1.
    destruct H2.
    eapply H0 in H3; eauto.
    specialize (H3 H). forward_reason.
    split; auto.
    forward. eauto.
  Qed.

  Definition TRY (tac : rtac) : rtac :=
    fun gl => match tac gl with
                | None => Some gl
                | Some gl' => Some gl'
              end.

  Theorem TRY_sound
  : forall tus tvs tac, rtac_sound tus tvs tac -> rtac_sound tus tvs (TRY tac).
  Proof.
    unfold TRY, rtac_sound.
    intros.
    specialize (H g g').
    destruct (tac g); inv_all; subst.
    { eapply H; eauto. }
    { forward. }
  Qed.

  Variable substV : (nat -> option expr) -> expr -> expr.
  Variable Var : nat -> expr.

  Definition INTRO
             (open : expr -> option ((typ * (expr -> expr)) + (expr * expr)))
  : rtac :=
    fun g => at_bottom (m := option)
                       (fun tus tvs s g =>
                          match g with
                            | None => None
                            | Some g =>
                              match open g with
                                | None => None
                                | Some (inl (t, g')) =>
                                  let nv := length tvs in
                                  Some (GAlls t (GGoal s (Some (g' (Var nv)))))
                                | Some (inr (t, g')) =>
                                  Some (GHyps t (GGoal s (Some g')))
                              end
                          end)
               nil nil g.

  Definition open_sound (open : expr -> option ((typ + expr) * expr)) : Prop :=
    forall tus tvs e eD h e',
      open e = Some (h,e') ->
      propD tus tvs e = Some eD ->
      match h with
        | inl t =>
          exists eD',
          propD tus (t :: tvs) e' = Some eD' /\
          forall us vs,
            (eD us vs) -> (forall x : typD nil t, eD' us (HList.Hcons x vs))
        | inr h =>
          False
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

(*
  Theorem INTRO_sound
  : forall open, open_sound open ->
                 rtac_sound nil nil (INTRO open).
  Proof.
    unfold rtac_sound, INTRO.
    intros.
    eapply at_bottom_sound_option in H0; eauto.
(*
    { destruct (goalD nil nil g); destruct (goalD nil nil g'); auto.
*)
  Abort.
*)

  Definition STAC_no_hyps (tac : stac typ expr subst) : rtac :=
    at_bottom (m := option)
              (fun tus tvs sub gl =>
                 match gl with
                   | None => Some (GGoal sub None)
                   | Some gl =>
                     match tac tus tvs sub nil gl with
                       | Fail => None
                       | More tus' tvs' sub' hs' gl' =>
                         ret (List.fold_right GExs
                               (List.fold_right GAlls
                                 (List.fold_right GHyps
                                   (GGoal sub' (Some gl')) hs') tvs') tus')
                       | Solved tus' tvs' sub' =>
                         ret (List.fold_right GExs
                               (List.fold_right GAlls
                                 (GGoal sub' None) tvs') tus')
                     end
                 end)
              nil nil.

  Lemma goalD_fold_right_GExs
  : forall tvs g ls tus,
      match goalD tus tvs (fold_right GExs g ls)
          , goalD (tus ++ ls) tvs g
      with
        | Some D , Some D' =>
          forall us vs,
            D us vs <->
            _exists
              (fun us' : HList.hlist (typD nil) ls =>
                 D' (HList.hlist_app us us') vs)
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    clear.
    induction ls; simpl.
    { intros.
      rewrite goalD_conv
      with (pfu := eq_sym (HList.app_nil_r_trans _)) (pfv := eq_refl).
      autorewrite with eq_rw.
      destruct (goalD tus tvs g); auto.
      intros. rewrite HList.hlist_app_nil_r.
      clear.
      match goal with
        | |- _ <-> (match ?X with _ => _ end
                      match ?Y with _ => _ end _) =>
          change Y with X ; destruct X
      end.
      reflexivity. }
    { intros.
      specialize (IHls (tus ++ a :: nil)).
      rewrite goalD_conv
      with (pfu := eq_sym (HList.app_ass_trans _ _ _)) (pfv := eq_refl)
        in IHls.
      autorewrite with eq_rw in IHls. simpl in *.
      destruct (goalD (tus ++ a :: nil) tvs (fold_right GExs g ls));
        destruct (goalD (tus ++ a :: ls) tvs g); auto.
      intros.
      eapply exists_iff; intro.
      etransitivity. eapply IHls.
      eapply _exists_iff; intro.
      autorewrite with eq_rw.
      match goal with
        | |- ?X <-> ?Y =>
          cutrewrite (X = Y); try reflexivity
      end.
      f_equal.
      clear.
      change (HList.Hcons x x0)
      with (HList.hlist_app (HList.Hcons x HList.Hnil) x0).
      rewrite HList.hlist_app_assoc.
      simpl.
      apply Eq.match_eq_sym_eq'. }
  Qed.

  Lemma goalD_fold_right_GAlls
  : forall tus g ls tvs,
      match goalD tus tvs (fold_right GAlls g ls)
          , goalD tus (tvs ++ ls) g
      with
        | Some D , Some D' =>
          forall us vs,
            D us vs <->
            _foralls
              (fun vs' : HList.hlist (typD nil) ls =>
                 D' us (HList.hlist_app vs vs'))
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    clear.
    induction ls; simpl.
    { intros.
      rewrite goalD_conv
      with (pfu := eq_refl) (pfv := eq_sym (HList.app_nil_r_trans _)).
      autorewrite with eq_rw.
      destruct (goalD tus tvs g); auto.
      intros. rewrite HList.hlist_app_nil_r.
      clear.
      match goal with
        | |- _ <-> (match ?X with _ => _ end
                      _ match ?Y with _ => _ end) =>
          change Y with X ; destruct X
      end.
      reflexivity. }
    { intros.
      specialize (IHls (tvs ++ a :: nil)).
      rewrite goalD_conv
      with (pfu := eq_refl) (pfv := eq_sym (HList.app_ass_trans _ _ _))
        in IHls.
      autorewrite with eq_rw in IHls. simpl in *.
      destruct (goalD tus (tvs ++ a :: nil) (fold_right GAlls g ls));
        destruct (goalD tus (tvs ++ a :: ls) g); auto.
      intros.
      eapply forall_iff; intro.
      etransitivity. eapply IHls.
      eapply _forall_iff; intro.
      autorewrite with eq_rw.
      match goal with
        | |- ?X <-> ?Y =>
          cutrewrite (X = Y); try reflexivity
      end.
      f_equal.
      clear.
      change (HList.Hcons x x0)
      with (HList.hlist_app (HList.Hcons x HList.Hnil) x0).
      rewrite HList.hlist_app_assoc.
      simpl.
      apply Eq.match_eq_sym_eq'. }
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


  Theorem STAC_no_hyps_sound
  : forall tac, stac_sound tac ->
                rtac_sound nil nil (STAC_no_hyps tac).
  Proof.
(*
    intros.
    unfold rtac_sound, STAC_no_hyps.
    intros. split.
    { eapply at_bottom_WF_option in H0; auto.
      destruct d.
      + intros. specialize (H a b c nil e H3).
        destruct (tac a b c nil e); try congruence.
        - destruct H. clear - H H2.
          inversion H2.
          apply WellFormed_goal_GExs.
          apply WellFormed_goal_GAlls.
          simpl. assumption.
        - destruct H; clear - H H2.
          inversion H2.
          apply WellFormed_goal_GExs.
          apply WellFormed_goal_GAlls.
          apply WellFormed_goal_GHyps.
          simpl. assumption.
      + clear. inversion 1.
        refine (fun x => x). }
    eapply at_bottom_sound_option in H0; eauto; clear H0.
    simpl.
    intros.
    destruct e.
    { assert (WellFormed_subst s) by admit.
      consider (tac tus' tvs' s nil e); try congruence;
      intros; inv_all; subst.
      { specialize (H tus' tvs' s nil e H1).
        rewrite H0 in H; clear H0 H1.
        forward_reason.
        unfold stateD in *.
        unfold propD, Core.propD in *.
        forward.
        simpl in H2.
        forwardy.
        specialize (goalD_fold_right_GExs tvs'
                      (fold_right GAlls (GGoal s0 None) l0)
                      l tus').
        match goal with
          | |- match ?X with _ => _ end ->
               match ?Y with _ => _ end =>
            change Y with X ; destruct X
        end;
        specialize (goalD_fold_right_GAlls (tus' ++ l)
                      (GGoal s0 None)
                      l0 tvs');
        match goal with
          | |- match ?X with _ => _ end ->
               match ?Y with _ => _ end -> _ =>
            change Y with X ; destruct X
        end; auto.
        { simpl. intros; forwardy.
          inv_all; subst.
          eapply H3; auto; clear H3.
          eapply H5 in H6; clear H5.
          eapply _exists_sem in H6.
          destruct H6.
          exists x.
          intros.
          change_rewrite H2 in H4.
          inv_all; subst.
          eapply H7 in H3; clear H7.
          eapply _forall_sem in H3. eapply H3. }
        { inversion 2. }
        { simpl. rewrite H2. auto. } }
      { specialize (H tus' tvs' s nil e H1).
        rewrite H0 in H.
        

 } }
    { inv_all; subst.
      simpl. forward. }
*)
  Abort.

  Eval compute in fun open t1 t2 e3 s goal =>
    INTRO open (GAlls t1 (GExs t2 (GHyps e3 (GGoal s (Some goal))))).

  Instance Monad_id : Monad (fun T : Type => T) :=
  { ret := fun T x => x
  ; bind := fun T U c c1 => c1 c
  }.

  Definition GOAL_map (f : list typ -> list typ -> subst -> expr -> expr)
  : rtac :=
    fun g =>
      Some (at_bottom (m := fun T => T)
                      (fun tus tvs s e =>
                         match e with
                           | None => GGoal s None
                           | Some e => GGoal s (Some (f tus tvs s e))
                         end)
                      nil nil g).

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