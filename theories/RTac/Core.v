Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.InstantiateI.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  (** TODO: I might want some way to maintain external state **)
  Variable subst : Type.

  (** This is a way to put everything inside there,
   ** an alternative representation is to use a simpler type, i.e.
   **     [list (All | Ex | Hyp)]
   ** to interpret the flattened environments
   **)
  Inductive GoalInterp :=
  | GAll (_ : GoalInterp)
  | GEx  (_ : GoalInterp)
  | GHyp (_ : GoalInterp)
  | Top.

  Inductive Result : Type :=
  | Fail
  | More : list typ (** in-order **) -> list typ (** in-order **) ->
           list expr -> GoalInterp ->
           subst -> option expr (** None = True **) -> Result.

  (** Is it feasible to cps-convert this? **)
  Definition rtac : Type :=
    list typ (* in-order *) -> list typ (* in-order *) ->
    list expr -> GoalInterp -> subst -> expr ->
    Result.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition propD (tus tvs : list typ) (goal : expr) : ResType tus tvs Prop :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return ResType tus tvs Prop with
      | None => None
      | Some val =>
        Some match typ0_cast nil in _ = T
                   return HList.hlist _ tus -> HList.hlist _ tvs -> T with
               | eq_refl => val
             end
    end.

  Definition OpenT tus tvs T :=
    hlist (typD nil) tus -> hlist (typD nil) tvs -> T.

  Fixpoint goalD (tus tvs tus' tvs' : list typ) (hyps : list expr)
           (gi : GoalInterp) {struct gi}
  : option (   OpenT (tus ++ rev tus') (tvs ++ rev tvs') Prop
            -> OpenT tus tvs Prop).
  refine (
      match gi with
        | GAll gi =>
          match tvs' with
            | nil => None
            | t :: tvs' =>
              match goalD tus tvs tus' tvs' hyps gi with
                | None => None
                | Some gD =>
                  Some _
              end
          end
        | GEx gi =>
          match tus' with
            | nil => None
            | t :: tus' =>
              match goalD tus tvs tus' tvs' hyps gi with
                | None => None
                | Some gD =>
                  Some _
              end
          end
        | GHyp gi =>
          match hyps with
            | nil => None
            | h :: hyps =>
              match propD (tus ++ rev tus') (tvs ++ rev tvs') h with
                | None => None
                | Some P =>
                  match goalD tus tvs tus' tvs' hyps gi with
                    | None => None
                    | Some gD => Some _
                  end
              end
          end
        | Top =>
          match tus' as tus'
              , tvs' as tvs'
                return option (OpenT (tus ++ rev tus') (tvs ++ rev tvs') Prop -> OpenT tus tvs Prop)
          with
            | nil , nil => Some _
            | _ , _ => None
          end
      end).
  { simpl in *.
    intro. apply gD.
    rewrite <- app_ass_trans in X.
    intros us vs.
    refine (forall x : typD nil t, X us (hlist_app vs (Hcons x Hnil))). }
  { simpl in *.
    intro. apply gD.
    rewrite <- app_ass_trans in X.
    intros us vs.
    refine (exists x : typD nil t, X (hlist_app us (Hcons x Hnil)) vs). }
  { intro. apply gD.
    refine (fun us vs => P us vs -> X us vs). }
  { simpl. rewrite app_nil_r_trans. rewrite app_nil_r_trans.
    refine (fun x => x). }
  Defined.

  Fixpoint GI_app (a b : GoalInterp) : GoalInterp :=
    match a with
      | Top => b
      | GHyp a => GHyp (GI_app a b)
      | GEx a => GEx (GI_app a b)
      | GAll a => GAll (GI_app a b)
    end.

  Lemma rev_app_distr_trans
  : forall T (ls ls' : list T),
      rev (ls ++ ls') = rev ls' ++ rev ls.
  Proof.
    clear. induction ls; simpl.
    { intros. symmetry. eapply app_nil_r_trans. }
    { intros. rewrite IHls.
      rewrite app_ass_trans. reflexivity. }
  Defined.

  Lemma rev_involutive_trans
  : forall T (ls : list T), rev (rev ls) = ls.
  Proof.
    clear. induction ls; try reflexivity.
    simpl.
    rewrite rev_app_distr_trans.
    rewrite IHls. reflexivity.
  Defined.

  Definition rev_rev_hlist {T} {F : T -> Type} {ls} (h : hlist F (rev (rev ls)))
  : hlist F ls :=
    match rev_involutive_trans ls in _ = T return hlist F T with
      | eq_refl => h
    end.

  Definition app_rev_rev_hlist {T} {F : T -> Type} {ls' ls}
             (h : hlist F (ls' ++ rev (rev ls)))
  : hlist F (ls' ++ ls) :=
    match rev_involutive_trans ls in _ = T return hlist F (ls' ++ T) with
      | eq_refl => h
    end.

  Definition rtac_sound (r : rtac) : Prop
  := forall tus tvs hyps gi sub goal,
       WellFormed_subst sub ->
       match r tus tvs hyps gi sub goal with
         | Fail => True
         | More tus' tvs' hyps' gi' sub' goal' =>
           WellFormed_subst sub' /\
           match propD tus tvs goal
               , substD tus tvs sub
               , goalD nil nil (rev tus) (rev tvs) hyps gi
           with
             | Some GD , Some SD , Some PD =>
               let tus_f := tus ++ tus' in
               let tvs_f := tvs ++ tvs' in
               match match goal' with
                       | None => Some (fun _ _ => True)
                       | Some goal => propD  tus_f tvs_f goal
                     end
                   , substD tus_f tvs_f sub'
                   , goalD tus tvs (rev tus') (rev tvs') hyps' gi'
               with
                 | Some GD' , Some SD' , Some PD' =>
                   PD (fun us vs =>
                         let us := rev_rev_hlist us in
                         let vs := rev_rev_hlist vs in
                         PD' (fun us' vs' =>
                                let us' := app_rev_rev_hlist us' in
                                let vs' := app_rev_rev_hlist vs' in
                                SD' us' vs' /\ GD' us' vs') us vs
                         -> SD us vs /\ GD us vs) Hnil Hnil
                 | _ , _ , _ => False
               end
             | _ , _ , _ => True
           end
       end.

  Ltac length_apply H :=
    match type of H with
      | ?X = ?Y =>
        cut (length X = length Y); [ | f_equal; exact H ]
    end.

  Lemma goalD_goalD
  : forall tus tvs gi tus' tvs' hyps hyps' gi' o1 o2,
      goalD tus tvs tus' tvs' hyps' gi = Some o1 ->
      goalD nil nil (rev tus) (rev tvs) hyps gi' = Some o2 ->
      exists o3,
           goalD nil nil (rev (tus ++ rev tus')) (rev (tvs ++ rev tvs'))
                 (hyps' ++ hyps) (GI_app gi gi') = Some o3
        /\ forall (P : OpenT (tus ++ rev tus') (tvs ++ rev tvs') Prop),
             o2 (fun us' vs' =>
                   o1 P
                      (rev_rev_hlist us') (rev_rev_hlist vs')) Hnil Hnil ->
             o3 (fun us' vs' =>
                   P (rev_rev_hlist us') (rev_rev_hlist vs')) Hnil Hnil.
  Proof.
    induction gi.
    { simpl. intros.
      forward. subst. inv_all; subst.
      specialize (IHgi _ _ _ _ _ _ _ H1 H0).
      forward_reason.
      (*
remember (rev (tvs ++ rev (t :: l))).
      destruct l0.
      { clear - Heql0. exfalso.
        rewrite rev_app_distr in Heql0.
        length_apply Heql0.
        simpl. repeat rewrite app_length.
        simpl.
        rewrite rev_length. rewrite app_length.
        simpl. omega. }
      { assert (l0 = rev (tvs ++ rev l)).
        { rewrite rev_app_distr in Heql0.
          simpl in Heql0.
          rewrite rev_app_distr in Heql0.
          simpl in *.
          inversion Heql0; subst.
          rewrite rev_app_distr.
          rewrite rev_involutive.
          reflexivity. }
        clear Heql0.
        subst.
        rewrite H. eauto. } *) admit. }
    { admit. }
    { admit. }
    { admit. }
  Qed.

  Lemma goalD_conv
  : forall a b c d e f a' b' c' d'
           (pfu : a' = a) (pfv : b' = b) (pfu' : c' = c) (pfv' : d' = d),
      goalD a b c d e f =
      match pfu in _ = A , pfv in _ = B , pfu' in _ = C , pfv' in _ = D
            return option (OpenT (A ++ rev C) (B ++ rev D) Prop ->
                           OpenT A B Prop)
      with
        | eq_refl , eq_refl , eq_refl , eq_refl => goalD a' b' c' d' e f
      end.
  Proof.
    destruct pfu; destruct pfv; destruct pfu'; destruct pfv'. reflexivity.
  Qed.

  Lemma propD_conv
  : forall a b c a' b' (pfu : a' = a) (pfv : b' = b),
      propD a b c =
      match pfu in _ = A , pfv in _ = B
            return option (OpenT A B Prop)
      with
        | eq_refl , eq_refl => propD a' b' c
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Variable SU : SubstUpdate subst expr.

  Definition IDTAC : rtac
  := fun tus tvs hs gi s goal =>
       More nil nil nil Top s (Some goal).

  Lemma goalD_prove
  : forall tus tvs gi tus' tvs' hyps D,
      goalD tus tvs tus' tvs' hyps gi = Some D ->
      forall us vs (P : OpenT _ _ Prop),
        (forall us' vs', P (hlist_app us us') (hlist_app vs vs')) ->
        D P us vs.
  Proof.
    induction gi.
    { simpl; intros.
      destruct tvs'; try congruence.
      forwardy. inv_all; subst.
      eapply IHgi in H. eapply H. intros.
      simpl. intros.
      specialize (H0 us' (hlist_app vs' (Hcons x Hnil))).
      clear - H0.
      rewrite hlist_app_assoc.
      match goal with
        | H : P _ ?X |- context [ ?Y ] =>
          change Y with X ; generalize dependent X
      end.
      generalize (app_ass_trans tvs (rev tvs') (t :: nil)).
      clear.
      generalize dependent ((tvs ++ rev tvs') ++ t :: nil).
      intros; subst. apply H0. }
    { admit. (** SAME **) }
    { admit. (** SAME **) }
    { simpl. intros.
      forwardy. destruct tus'; try congruence.
      destruct tvs'; try congruence.
      inv_all; subst.
      simpl in *.
      specialize (H0 Hnil Hnil).
      do 2 rewrite hlist_app_nil_r in H0.
      generalize dependent (app_nil_r_trans tus).
      generalize dependent (app_nil_r_trans tvs).
      generalize dependent (tus ++ nil).
      generalize dependent (tvs ++ nil).
      intros; subst.
      apply H0. }
  Qed.

  Theorem IDTAC_sound : rtac_sound IDTAC.
  Proof.
    red. simpl. intros.
    split; auto.
    forward.
    rewrite propD_conv with (pfu := eq_sym (app_nil_r_trans tus)) (pfv := eq_sym (app_nil_r_trans tvs)).
    rewrite substD_conv with (pfu := eq_sym (app_nil_r_trans tus)) (pfv := eq_sym (app_nil_r_trans tvs)).
    rewrite H1. rewrite H0.
    unfold ResType.
    generalize (app_nil_r_trans tus).
    generalize (app_nil_r_trans tvs).
    intros.
    autorewrite with eq_rw.
    eapply goalD_prove; eauto.
    simpl. intros.
    generalize dependent (rev_rev_hlist us').
    generalize dependent (rev_rev_hlist vs').
    clear.
    unfold app_rev_rev_hlist.
    simpl.
    generalize dependent (tvs ++ nil).
    generalize dependent (tus ++ nil).
    intros; subst. apply H3.
  Qed.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  (** The idea here is to pop-off all the outer stuff
   ** naively I need to do it everywhere, but in actuallity
   ** I can lump them together.
   ** In reality, I probably rarely do this to more than a few things.
   **)
  Fixpoint peel_all (gi : GoalInterp) : rtac :=
    match gi with
      | Top => IDTAC
      | GAll gi => IDTAC
      | GEx gi => IDTAC
      | GHyp gi => IDTAC
    end.

  Definition unify (e1 e2 : expr) (t : typ)
  : rtac :=
    fun tus tvs hs gi sub goal =>
      match exprUnify tus tvs 0 e1 e2 t sub with
        | None => Fail
        | Some sub' =>
          More nil nil nil Top sub' (Some goal)
      end.

  Definition unify_sound
  : forall e1 e2 t,
      (** NOTE: There is nothing that I can write here! **)
      rtac_sound (unify e1 e2 t).
  Abort.

  Definition with_new_uvar (t : typ) (k : nat -> rtac) : rtac
  := fun tus tvs hs gi s goal =>
       let uv := length tus in
       match (k uv) (tus ++ t :: nil) tvs hs (GEx gi) s goal with
         | Fail => Fail
         | More tus' tvs' hyps' gi' sub' goal' =>
           match tus' , tvs' with
             | nil , nil =>
               match pull (expr:=expr) uv 1 sub' with
                 | None => Fail
                 | Some sub'' =>
                   More nil nil hyps' gi' sub''
                        (fmap (F:=option) (instantiate (fun u => lookup u sub') 0) goal')
               end
             | _ , _ => Fail
           end
       end.

  Definition with_new_var (t : typ) (k : nat -> rtac) : rtac
  := fun tus tvs hs gi s goal =>
       let v := length tvs in
       match (k v) tus (tvs ++ t :: nil) hs (GAll gi) s goal with
         | Fail => Fail
         | More tus' tvs' hyps' gi' sub' goal' =>
           match tus' , tvs' with
             | nil , nil =>
               (** check that the variable is not mentioned in the conclusion
                ** since that is the only place that it can be mentioned
                **)
               if match goal' with
                    | None => false
                    | Some goal' => mentionsV v goal'
                  end
               then
                 Fail
               else
                 More nil nil hyps' gi' sub' goal'
             | _ , _ => Fail
           end
       end.

  Theorem with_new_uvar_sound
  : forall t (kTac : nat -> rtac),
      (forall uv, rtac_sound (kTac uv)) ->
      rtac_sound (with_new_uvar t kTac).
  Proof.
    unfold with_new_uvar. red; intros.
    forward. subst.
    inversion H5; clear H5; subst.
    specialize (H (length tus) (tus ++ t :: nil) tvs hyps (GEx gi) sub goal H0).
    rewrite H3 in H; clear H3. forward_reason.
    eapply pull_sound in H4; eauto.
    2: admit. 2: admit. 2: admit.
    forward_reason. split; auto.
    forward.
    admit.
  Qed.

  Definition THEN (a b : rtac) : rtac :=
    fun tus tvs hs gi s goal =>
      match a tus tvs hs gi s goal with
        | Fail => Fail
        | More tus' tvs' hyps' gi' sub' None =>
          More tus' tvs' hyps' gi' sub' None
        | More tus' tvs' hyps' gi' sub' (Some goal') =>
          match
            b (tus ++ tus') (tvs ++ tvs') (hyps' ++ hs) (GI_app gi' gi) sub' goal'
          with
            | Fail => Fail
            | More tus'' tvs'' hyps'' gi'' sub'' goal'' =>
              More (tus' ++ tus'') (tvs' ++ tvs'')
                   hyps'' (GI_app gi'' gi') sub'' goal''
          end
      end.

  Theorem THEN_sound
  : forall a b, rtac_sound a -> rtac_sound b ->
                rtac_sound (THEN a b).
  Proof.
    unfold rtac_sound, THEN; intros.
    forward.
    specialize (H tus tvs hyps gi sub goal H1).
    rewrite H2 in H; clear H2. forward_reason.
    destruct o0; forward.
    { inversion H4; clear H4; subst.
      specialize (H0 (tus ++ l2) (tvs ++ l3) (l4 ++ hyps) (GI_app g0 gi) s0 e H).
      rewrite H3 in H0; clear H3. forward_reason.
      split; auto. forward.
      simpl in *.
      destruct (goalD_goalD _ _ _ _ _ _ H8 H5); clear H8 H5; forward_reason.
      revert H5; revert H8. revert x.
      repeat match goal with
               | |- context [ rev (rev ?X) ] =>
                 rewrite (rev_involutive X)
             end.
      intros. (*rewrite H5 in H7.
      forward.
      destruct o.
      {
      match goal with
               | |- context [ rev (rev ?X) ] =>
                 rewrite (rev_involutive X)
             end.
      rewrite (rev_involutive l2).

      simpl.

*) admit. }
    { subst. inversion H9; clear H9; subst.
      inv_all; subst.
      split; auto.
      rewrite H6. rewrite H7.
      assumption. }
  Qed.

(*
  Variable t1 t2 t3 t4 : typ.
  Variable e1 e2 : expr.
  Variable s : subst.

  Eval cbv beta iota zeta delta - [ hlist_app typD ]  in fun f =>
      match @goalD nil nil (t1 :: t3 :: nil) (t2 :: t4 :: nil) (e1 :: e2 :: nil)
                   (GHyp (GAll (GEx (GHyp (GAll (GEx Top)))))) with
        | None => None
        | Some X => Some (X f Hnil Hnil)
      end.
*)


  (** TODO: This is breaking me at the moment b/c I can not add/compose
   ** more things under this.
   **)
  Definition proof_stateD (tus tvs tus' tvs' : list typ)
             (hyps : list expr) (gi : GoalInterp) (sub : subst)
             (goal : option expr)
  : option (OpenT tus tvs Prop) :=
    let tus_f := tus ++ rev tus' in
    let tvs_f := tvs ++ rev tvs' in
    match match goal with
            | None => Some (fun _ _ => True)
            | Some goal => propD  tus_f tvs_f goal
          end
        , substD tus_f tvs_f sub
        , goalD tus tvs tus' tvs' hyps gi
    with
      | Some GD , Some SD , Some PD =>
        Some (PD (fun us vs => SD us vs /\ GD us vs))
      | _ , _ , _ => None
    end.

(*
  Goal forall T U V W (P : _ -> _ -> Prop) (Q : _ -> _ -> _ -> _ -> Prop),
    (forall x : T, exists y : U,
          (forall a : V, exists b : W, Q x y a b)
       -> P x y)
    ->
    ((forall x, forall y, forall a, exists b, Q x y a b) ->
     (forall x, exists y, P x y)).
  Proof.
    clear. intros.
    { intros. specialize (H0 x).
      specialize (H x). destruct H.
      exists x0. apply H. auto. }
  Qed.
*)
