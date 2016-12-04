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
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Set.
  Variable expr : Set.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

(*
  (** TODO(gmalecha): These should go somewhere more useful *)
  Fixpoint forgets (from : nat) (ts : list typ) (s : subst)
  : list (option expr) :=
    match ts with
      | nil => nil
      | t :: ts =>
        let rr := forgets (S from) ts s in
        let ne := subst_lookup from s in
        ne :: rr
    end.

  Fixpoint remembers (from : nat) (tes : list (typ * option expr)) (s : subst)
  : option subst :=
    match tes with
      | nil => Some s
      | (_,None) :: tes' => remembers (S from) tes' s
      | (_,Some e) :: tes' =>
        (* This should not be necessary but to eliminate it, we must have a
         * syntactic soundness condition for [set] *)
        match subst_lookup from s with
          | None =>
            match subst_set from e s with
              | None => None
              | Some s' => remembers (S from) tes' s'
            end
          | Some _ => None
        end
    end.
*)


  Definition rtacK_spec ctx (s : ctx_subst ctx) (g : Goal _ _)
             (r : Result ctx) : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match pctxD s
            , goalD _ _ g
            , pctxD s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            SubstMorphism s s' /\
            forall us vs, cD' gD us vs
        end
      | More_ s' g' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        WellFormed_Goal (getUVars ctx) (getVars ctx) g' /\
        match pctxD s
            , goalD _ _ g
            , pctxD s'
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            SubstMorphism s s' /\
            forall us vs,
              cD' (fun us vs => gD' us vs -> gD us vs) us vs
        end
    end.

  Definition rtacK_spec_wf ctx (s : ctx_subst ctx) (g : Goal _ _)
             (r : Result ctx) : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s'
      | More_ s' g' =>
        WellFormed_Goal (getUVars ctx) (getVars ctx) g ->
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst (c:=ctx) s' /\
        WellFormed_Goal (getUVars ctx) (getVars ctx) g'
    end.

  Theorem rtacK_spec_rtacK_spec_wf : forall ctx s g r,
      @rtacK_spec ctx s g r ->
      @rtacK_spec_wf ctx s g r.
  Proof.
    unfold rtacK_spec, rtacK_spec_wf; destruct r; tauto.
  Qed.

  Theorem Proper_rtacK_spec ctx s
  : Proper (EqGoal (getUVars ctx) (getVars ctx) ==>
            @EqResult _ _ _ _ _ ctx ==> iff)
           (@rtacK_spec ctx s).
  Proof.
    red. red. red.
    unfold rtacK_spec.
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
               | |- ?X _ _ _ <-> ?X _ _ _ =>
                 (eapply Fmap_pctxD_iff; try reflexivity; eauto);
                   [  ]
             end.
      { do 5 red; intros; equivs.
        apply impl_iff; [ eapply H10; try reflexivity; eauto | intro ].
        apply H12; reflexivity. }
      { subst. do 5 red; intros; equivs.
        do 5 red in H9.
        rewrite H9; try reflexivity.
        rewrite impl_True_iff.
        eapply H11; reflexivity. }
      { subst. do 5 red in H9.
        do 5 red; intros; equivs.
        rewrite <- H9; try reflexivity.
        rewrite impl_True_iff.
        eapply H11; reflexivity. }
      { eapply Fmap_pctxD_iff; try reflexivity; eauto. } }
  Qed.

  (** Treat this as opaque! **)
  Definition rtacK : Type :=
    forall c : Ctx typ expr, ctx_subst c -> Goal typ expr -> Result c.

  Definition rtacK_sound (tac : rtacK)
  : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      @rtacK_spec ctx s g result.

  Definition WellFormed_rtacK (tac : rtacK)
  : Prop :=
    forall ctx s g result,
      tac ctx s g = result ->
      @rtacK_spec_wf ctx s g result.

  Theorem rtacK_sound_WellFormed_rtacK : forall tac,
      rtacK_sound tac -> WellFormed_rtacK tac.
  Proof.
    intros. red. intros.
    eapply rtacK_spec_rtacK_spec_wf. eauto.
  Qed.

End parameterized.

Delimit Scope rtacK_scope with rtacK.

Arguments rtacK_sound {typ expr _ _ _} tac%rtacK : rename.
Arguments WellFormed_rtacK {typ expr _ _} tac%rtacK : rename.

Delimit Scope or_rtacK_scope with or_rtacK.

Notation " [ ] " := (@nil (rtacK _ _)) : or_rtacK_scope.
Notation " [  x ] " := (@cons (rtacK _ _) x%rtacK (@nil (rtacK _ _))) : or_rtacK_scope.
Notation " [  x  | ..  | y  ] " := (@cons (rtacK _ _) x%rtacK .. (@cons (rtacK _ _) y%rtacK (@nil (rtacK _ _))) ..) : or_rtacK_scope.

Export MirrorCore.ExprI.
Export MirrorCore.SubstI.
Export MirrorCore.ExprDAs.
Export MirrorCore.RTac.Core.
