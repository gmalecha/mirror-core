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
Require Import MirrorCore.RTac.Ctx.

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

Ltac equivs :=
  repeat match goal with
           | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
         end; subst.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprVarOk_expr : ExprVarOk _}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.
  Context {MentionsAny_expr : MentionsAny expr}.
  Context {MentionsAnyOk_expr : MentionsAnyOk _ _ _}.

  Inductive Goal :=
  | GAll    : typ -> Goal -> Goal
  | GExs    : list typ -> amap expr -> Goal -> Goal
  | GHyp    : expr -> Goal -> Goal
  | GConj_  : Goal -> Goal -> Goal
  | GGoal   : expr -> Goal
  | GSolved : Goal.

  Inductive WellFormed_Goal (tus tvs : tenv typ) : Goal -> Prop :=
  | WFExs : forall ts s g,
              WellFormed_bimap (length tus) (length ts) s ->
              WellFormed_Goal (tus ++ ts) tvs g ->
              WellFormed_Goal tus tvs (GExs ts s g)
  | WFAll : forall t g, WellFormed_Goal tus (tvs ++ t :: nil) g ->
                        WellFormed_Goal tus tvs (GAll t g)
  | WFHyp : forall t g, WellFormed_Goal tus tvs g ->
                        WellFormed_Goal tus tvs (GHyp t g)
  | WFConj_ : forall g1 g2, WellFormed_Goal tus tvs g1 ->
                            WellFormed_Goal tus tvs g2 ->
                            WellFormed_Goal tus tvs (GConj_ g1 g2)
  | WFGoal : forall g, WellFormed_Goal tus tvs (GGoal g)
  | WFSovled : WellFormed_Goal tus tvs GSolved.


  Global Instance Injective_WellFormed_Goal_GAll tus tvs t g
  : Injective (WellFormed_Goal tus tvs (GAll t g)) :=
    { result := WellFormed_Goal tus (tvs ++ t :: nil) g }.
  Proof. inversion 1; auto. Defined.
  Global Instance Injective_WellFormed_Goal_GHyp tus tvs t g
  : Injective (WellFormed_Goal tus tvs (GHyp t g)) :=
    { result := WellFormed_Goal tus tvs g }.
  Proof. inversion 1; auto. Defined.
  Global Instance Injective_WellFormed_Goal_GExs tus tvs l a g
  : Injective (WellFormed_Goal tus tvs (GExs l a g)) :=
    { result := WellFormed_Goal (tus ++ l) tvs g /\
                WellFormed_bimap (length tus) (length l) a }.
  Proof.
    refine (fun pf =>
              match pf in WellFormed_Goal _ _ G
                    return match G return Prop with
                             | GExs l a g =>
                               WellFormed_Goal (tus ++ l) tvs g /\
                               WellFormed_bimap (length tus) (length l) a
                             | _ => True
                           end
              with
                | WFExs _ _ _ a b => conj b a
                | _ => I
              end).
  Defined.
  Global Instance Injective_WellFormed_Goal_GConj tus tvs a b
  : Injective (WellFormed_Goal tus tvs (GConj_ a b)) :=
  { result := WellFormed_Goal tus tvs a /\ WellFormed_Goal tus tvs b }.
  Proof. inversion 1. auto. Defined.


  Definition GAlls (ts : list typ) (g : Goal) : Goal :=
    fold_right (fun x y => GAll x y) g ts.

  Definition GEx_empty (nus : nat) (t : typ) (g : Goal) : Goal :=
    match g with
      | GExs ts sub g' => GExs (t :: ts) sub g'
      | _ => GExs (t :: nil) (amap_empty _) g
    end.

(*
  Definition GEx nus (t : typ) (e : option expr) (g : Goal) : Goal :=
    match g with
      | GExs ts sub g' =>
        match e with
          | None => GExs (t :: ts) sub g'
          | Some e => GExs (t :: ts) (amap_check_set nus e sub) g'
        end
      | _ =>
        GExs (t :: nil)
             match e with
               | None => amap_empty
               | Some e => amap_check_set _ nus e (amap_empty _)
             end g
    end.
*)


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
      | GSolved :: gs => GConj_list_filter gs
      | g :: gs => match GConj_list_filter gs with
                     | GSolved => g
                     | g' => GConj_ g g'
                   end
    end.

  Local Notation "'CSUBST' c" := (ctx_subst (typ:=typ) (expr:=expr) c) (at level 0).

  (** StateT subst Option Goal **)
  Inductive Result c :=
  | Fail
  | More_  : CSUBST c -> Goal -> Result c
  | Solved : CSUBST c -> Result c.

  Definition More {c} (s : CSUBST c) (g : Goal) : Result c :=
    match g with
      | GSolved => Solved s
      | _ => More_ s g
    end.

  Definition fromResult {c} (r : Result c) : option (ctx_subst c * Goal) :=
    match r with
      | Fail => None
      | More_ s g => Some (s, g)
      | Solved s => Some (s, GSolved)
    end.

  Definition DEAD {c} : Result c.
    exact (Fail c).
  Qed.

  (** Treat this as opaque! **)
  Definition rtac : Type :=
    tenv typ -> tenv typ -> nat -> nat ->
    forall c : Ctx typ expr, ctx_subst c -> expr -> Result c.

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

(*
  (** NOTE: This definition is kind of in the way **)
  Definition hlist_get_cons_after_app
             {T : Type} {F : T -> Type} {t} {a b : list T}
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
*)

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
      | GExs ts sub goal' =>
        let tus_ext := ts in
        match goalD (tus ++ ts) tvs goal'
            , amap_substD (tus ++ ts) tvs sub with
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

  Local Existing Instance Transitive_Roption.
  Local Existing Instance Symmetric_Roption.
  Local Existing Instance Reflexive_Roption.
  Local Existing Instance Transitive_RexprT.
  Local Existing Instance Symmetric_RexprT.
  Local Existing Instance Reflexive_RexprT.

  Definition EqGoal tus tvs : relation Goal :=
    fun g1 g2 =>
      (WellFormed_Goal tus tvs g1 <-> WellFormed_Goal tus tvs g2) /\
      Roption (RexprT tus tvs iff)
              (goalD tus tvs g1)
              (goalD tus tvs g2).

  Global Instance Reflexive_EqGoal tus tvs : Reflexive (EqGoal tus tvs).
  Proof. red. red. split; reflexivity. Qed.
  Global Instance Transitive_EqGoal tus tvs : Transitive (EqGoal tus tvs).
  Proof.
    red. unfold EqGoal. intros.
    intuition.
    etransitivity; eauto.
  Qed.
  Global Instance Symmetric_EqGoal tus tvs : Symmetric (EqGoal tus tvs).
  Proof.
    red; unfold EqGoal. intros.
    intuition.
  Qed.

  Definition EqResult c : relation (Result c) :=
    fun r1 r2 =>
      Roption (Eqpair (@eq _) (EqGoal (getUVars c) (getVars c)))
              (fromResult r1) (fromResult r2).

  Global Instance Reflexive_EqResult c
  : Reflexive (@EqResult c).
  Proof.
    red. red. intros. reflexivity.
  Qed.
  Global Instance Symmetric_EqResult c
  : Symmetric (@EqResult c).
  Proof.
    red. unfold EqResult; inversion 1; constructor.
    symmetry; eauto.
  Qed.
  Global Instance Transitive_EqResult c
  : Transitive (@EqResult c).
  Proof.
    red; unfold EqResult; inversion 1; inversion 1; constructor.
    subst.
    etransitivity; eauto.
  Qed.

  Lemma More_More_ c s :
    (EqGoal (getUVars c) (getVars c) ==> @EqResult c)%signature
       (@More c s) (@More_ c s).
  Proof.
    red. red.
    simpl. intros; subst.
    destruct x; simpl;
    try solve [ repeat (constructor; try assumption) ].
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
    - split.
      { split; intro.
        + inversion H0. assumption.
        + constructor. constructor. assumption. }
      destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite and_comm. rewrite and_True_iff.
      equivs. reflexivity.
    - split.
      { split; intro.
        inversion H0; assumption.
        constructor. assumption. constructor. }
      destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite and_True_iff.
      equivs. reflexivity.
    - split; reflexivity.
  Qed.

  Lemma GConj_GConj_rel : forall g1 g2, GConj_rel g1 g2 (GConj g1 g2).
  Proof.
    intros; destruct g1; destruct g2; simpl; try constructor.
  Qed.

  Lemma GConj_GConj_ tus tvs :
    (EqGoal tus tvs ==> EqGoal tus tvs ==> EqGoal tus tvs)%signature
                                                          GConj GConj_.
  Proof.
    unfold respectful; simpl.
    intros.
    etransitivity.
    - symmetry. eapply GConj_rel_sound. eapply (GConj_GConj_rel x x0).
    - simpl. inversion H; try reflexivity.
      inversion H0; try reflexivity.
      split.
      { split; inversion 1; constructor; subst; tauto. }
      simpl.
      destruct (goalD tus tvs x); destruct (goalD tus tvs x0);
      inversion H2; inversion H4; subst; constructor.
      do 5 red.
      intros. eapply and_iff. eapply H7; auto. intro.
      eapply H10; eauto.
  Qed.

  Definition rtac_spec ctx (s : CSUBST ctx) g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match pctxD s
            , goalD (getUVars ctx) (getVars ctx) g
            , pctxD s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            SubstMorphism s s' /\
            forall us vs,
              cD' gD us vs
        end
      | More_ s' g' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        WellFormed_Goal (getUVars ctx) (getVars ctx) g' /\
        match pctxD s
            , goalD (getUVars ctx) (getVars ctx) g
            , pctxD s'
            , goalD (getUVars ctx) (getVars ctx) g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            SubstMorphism s s' /\
            forall us vs, cD' (fun us vs => gD' us vs -> gD us vs) us vs
        end
    end.

  Definition GoalImplies ctx (sg : CSUBST ctx * Goal) (sg' : CSUBST ctx * Goal)
  : Prop :=
    let (s,g) := sg in
    let (s',g') := sg' in
    WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
    WellFormed_ctx_subst s ->
    WellFormed_ctx_subst s' /\
    WellFormed_Goal (getUVars ctx) (getVars ctx) g' /\
    match pctxD s
        , goalD (getUVars ctx) (getVars ctx) g
        , pctxD s'
        , goalD (getUVars ctx) (getVars ctx) g'
    with
      | None , _ , _ , _
      | Some _ , None , _ , _ => True
      | Some _ , Some _ , None , _
      | Some _ , Some _ , Some _ , None => False
      | Some cD , Some gD , Some cD' , Some gD' =>
        SubstMorphism s s' /\
        forall us vs, cD' (fun us vs => gD' us vs -> gD us vs) us vs
    end.

  Definition rtac_spec_modular ctx (s : CSUBST ctx) g r : Prop :=
    match fromResult r with
      | None => True
      | Some (s', g') => GoalImplies (s, g) (s', g')
    end.

  Lemma WellFormed_Goal_Solved_iff
  : forall tus tvs, WellFormed_Goal tus tvs GSolved <-> True.
  Proof.
    split. intros; inv_all; subst. auto.
    intros. constructor.
  Qed.

  Lemma rtac_spec_rtac_spec_modular ctx
  : (eq ==> eq ==> eq ==> iff)%signature
       (@rtac_spec ctx) (@rtac_spec_modular ctx).
  Proof.
    do 3 red; intros; subst.
    destruct y1; unfold rtac_spec_modular; simpl; try reflexivity.
    - unfold GoalImplies.
      eapply impl_iff; try tauto; intro.
      eapply impl_iff; try tauto; intro.
      eapply and_iff; try tauto; intro.
      rewrite WellFormed_Goal_Solved_iff.
      rewrite and_comm. rewrite and_True_iff.
      simpl.
      forward.
      apply and_iff; try tauto; intro.
      apply forall_iff; intro.
      apply forall_iff; intro.
      eapply Fmap_pctxD_iff; eauto; try reflexivity.
      do 5 red; intros.
      rewrite impl_True_iff. equivs. reflexivity.
  Qed.

  Definition rtac_sound (tac : rtac) : Prop :=
    forall ctx s g result,
      (let tus := getUVars ctx in
       let tvs := getVars ctx in
       tac tus tvs (length tus) (length tvs) ctx s g = result) ->
      @rtac_spec ctx s (GGoal g) result.

  Lemma left_side : forall (P Q R : Prop), P ->
                                           (Q <-> R) ->
                                           ((P /\ Q) <-> R).
  Proof. clear. tauto. Qed.

  Lemma right_side : forall (P Q R : Prop), P ->
                                           (Q <-> R) ->
                                           (Q <-> (P /\ R)).
  Proof. clear. tauto. Qed.

  Definition WellTyped_Goal tus tvs (g : Goal) : Prop :=
    exists gD, goalD tus tvs g = Some gD.

  Definition WellTyped_ctx_subst c (cs : ctx_subst c) : Prop :=
    exists csD, ctx_substD (getUVars c) (getVars c) cs = Some csD.

  Definition WellTyped_Result c (r : Result c) : Prop :=
    match r with
      | Fail => True
      | Solved cs =>  WellTyped_ctx_subst cs
      | More_ cs g => WellTyped_Goal (getUVars c) (getVars c) g /\
                      WellTyped_ctx_subst cs
    end.

  Theorem Proper_rtac_spec ctx s
  : Proper (EqGoal (getUVars ctx) (getVars ctx) ==>
            @EqResult ctx ==> iff)
           (@rtac_spec ctx s).
  Proof.
    clear RTypeOk_typ ExprOk_expr.
    red. red. red. unfold rtac_spec.
    inversion 2.
    { destruct x0; destruct y0; simpl in *; try congruence.
      reflexivity. }
    { destruct x0; destruct y0; simpl in *;
      try solve [ reflexivity | congruence ]; inv_all; subst; inv_all;
      repeat match goal with
               | H : ?X , H' : ?X |- _ => clear H'
               | H : EqGoal _ _ _ _ |- _ => destruct H
               | |- (_ -> _) <-> (_ -> _) =>
                 eapply impl_iff; [ solve [ eauto | reflexivity ] | ]; intros
               | |- (_ /\ _) <-> (_ /\ _) =>
                 eapply and_iff; [ solve [ eauto | reflexivity ] | ]; intros
               | H : Roption _ _ _ |- _ => inversion H; clear H
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; intros; try reflexivity; [ ]
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; intros; reflexivity
               | |- (forall x, _) <-> (forall y, _) =>
                 eapply forall_iff; intro
               | |- _ =>
                 eapply left_side; [ match goal with
                                       | H : _ <-> _ |- _ => apply H; constructor
                                     end | ]
               | |- _ =>
                 eapply right_side; [ match goal with
                                       | H : _ <-> _ |- _ => apply H; constructor
                                     end | ]
             end.
      { eapply Fmap_pctxD_iff; eauto; try reflexivity.
        do 5 red; intros.
        apply impl_iff; [ eapply H10; eauto | intro ].
        apply H12; eauto. }
      { eapply Fmap_pctxD_iff; eauto; try reflexivity.
        do 5 red; intros.
        do 5 red in H9. subst.
        rewrite H9; eauto.
        rewrite impl_True_iff.
        eapply H11; eauto. }
      { eapply Fmap_pctxD_iff; eauto; try reflexivity.
        do 5 red; intros.
        do 5 red in H9. subst.
        rewrite <- H9; eauto.
        rewrite impl_True_iff.
        eapply H11; eauto. }
      { eapply Fmap_pctxD_iff; eauto; try reflexivity. } }
  Qed.

  Theorem rtac_spec_More_
  : forall ctx (s : ctx_subst ctx) g,
      rtac_spec s (GGoal g) (More_ s (GGoal g)).
  Proof.
    unfold rtac_spec.
    intros; subst.
    split; auto.
    simpl. forward.
    split; auto.
    split; try reflexivity.
    intros. eapply Applicative_pctxD; eauto.
  Qed.

  Theorem rtac_spec_Fail
  : forall ctx (s : ctx_subst ctx) g,
      rtac_spec s g (Fail _).
  Proof.
    intros. exact I.
  Qed.

  Lemma rtac_spec_trans
  : forall ctx (c c' : ctx_subst ctx) g g' r,
      rtac_spec c g (More_ c' g') ->
      rtac_spec c' g' r ->
      rtac_spec c g r.
  Proof.
    destruct r; simpl; intros; auto; forward; forward_reason;
    split; eauto.
    - split; auto.
      split; [ eapply Transitive_SubstMorphism; eauto | ].
      intros us vs. generalize (H14 us vs); clear H14.
      eapply Ap_pctxD; eauto.
      eapply pctxD_SubstMorphism; eauto.
      generalize (H11 us vs); clear H11.
      eapply Fmap_pctxD_impl;
        [ eassumption | | reflexivity | reflexivity ].
      clear. do 6 red.
      intros; equivs. tauto.
    - split; [ eapply Transitive_SubstMorphism; eauto | ].
      intros us vs. generalize (H12 us vs); clear H12.
      eapply Ap_pctxD; eauto.
      eapply pctxD_SubstMorphism; eauto.
      generalize (H10 us vs); clear H10.
      eapply Fmap_pctxD_impl;
        [ eassumption | | reflexivity | reflexivity ].
      clear. do 6 red.
      intros; equivs. tauto.
  Qed.

  Global Instance Reflexive_GoalImplies c : Reflexive (GoalImplies (ctx:=c)).
  Proof.
    red. destruct x; simpl; intros;
         forward_reason.
    split; auto.
    split; auto.
    forward.
    split; [ reflexivity | ].
    intros. eapply Pure_pctxD; eauto.
  Qed.
  Global Instance Transitive_GoalImplies c : Transitive (GoalImplies (ctx:=c)).
  Proof.
    red. destruct x; destruct y; destruct z; simpl; intros;
         forward_reason.
    split; auto.
    split; auto.
    forward. forward_reason.
    split; [ etransitivity; eassumption | ].
    intros. gather_facts.
    eapply pctxD_SubstMorphism; [ eassumption | eauto | eauto | ].
    gather_facts.
    eapply Pure_pctxD; eauto.
  Qed.

End parameterized.

Arguments rtac_sound {typ expr _ _ _ _} tac : rename.

(*Arguments GEx {typ expr} _ _ _ : rename. *)
Arguments GAll {typ expr} _ _ : rename.
Arguments GHyp {typ expr} _ _ : rename.
Arguments GConj {typ expr} _ _ : rename.
Arguments GConj_ {typ expr} _ _ : rename.
Arguments GConj_list {typ expr} _ : rename.
Arguments GGoal {typ expr} _ : rename.
Arguments GSolved {typ expr} : rename.

Arguments Fail {typ expr _} : rename.
Arguments More {typ expr _} _ _ : rename.
Arguments More_ {typ expr _} _ _ : rename.
Arguments Solved {typ expr _} _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.SubstI.
Export MirrorCore.ExprDAs.
Export MirrorCore.RTac.Ctx.
