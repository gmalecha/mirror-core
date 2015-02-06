Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Lemma.

Set Implicit Arguments.
Set Strict Implicit.

Section lemma_apply.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyProp : typ := @typ0 _ _ _ _.
  Context {subst : Type}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk Subst_subst}.
  (** TODO: Ideally I wouldn't need these things, but they are necessary b/c of
   ** where [substR] fits into things
   **)
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : SubstUpdateOk _ _}.

  Variable unify : unifier typ expr subst.

  Hypothesis Hunify : unify_sound unify.

  Definition eapplicable (s : subst) (tus tvs : EnvI.tenv typ)
             (lem : lemma typ expr expr) (e : expr)
  : option subst :=
    let pattern := vars_to_uvars 0 (length tus) lem.(concl) in
    unify (tus ++ lem.(vars)) tvs 0 pattern e tyProp s.

  Ltac fill_holes :=
    let is_prop P := match type of P with
                       | Prop => idtac
                       | _ => fail
                     end
    in
    repeat match goal with
             | |- _ => progress intros
             | H : exists x , _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | |- exists x, _ /\ _ =>
               eexists; split; [ solve [ eauto ] | ]
             | |- _ /\ _ =>
               (split; eauto); [ ]
             | [ H : _ -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 specialize (H H')
             | [ H : forall x, @?X x -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 specialize (@H _ H')
             | [ H : forall x y, @?X x y -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ H')
                       | specialize (fun y => @H _ y H')
                       | specialize (fun x => @H x _ H')
                       | specialize (@H _ _ eq_refl)
                       | specialize (fun y => @H _ y eq_refl)
                       | specialize (fun x => @H x _ eq_refl)
                       ]
             | [ H : forall x y z, @?X x y z -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ _ H')
                       | specialize (fun x => @H x _ _ H')
                       | specialize (fun y => @H _ y _ H')
                       | specialize (fun z => @H _ _ z H')
                       | specialize (fun x y => @H x y _ H')
                       | specialize (fun y z => @H _ y z H')
                       | specialize (fun x z => @H x _ z H')
                       | specialize (@H _ _ _ eq_refl)
                       | specialize (fun x => @H x _ _ eq_refl)
                       | specialize (fun y => @H _ y _ eq_refl)
                       | specialize (fun z => @H _ _ z eq_refl)
                       | specialize (fun x y => @H x y _ eq_refl)
                       | specialize (fun y z => @H _ y z eq_refl)
                       | specialize (fun x z => @H x _ z eq_refl)
                       ]
             | [ H : forall x y z a, @?X x y z a -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ _ _ H')
                       | specialize (fun x => @H x _ _ _ H')
                       | specialize (fun y => @H _ y _ _ H')
                       | specialize (fun z => @H _ _ z _ H')
                       | specialize (fun a => @H _ _ _ a H')
                       | specialize (fun x y => @H x y _ _ H')
                       | specialize (fun y z => @H _ y z _ H')
                       | specialize (fun z a => @H _ _ z a H')
                       | specialize (fun x a => @H x _ _ a H')
                       | specialize (fun x y z => @H x y z _ H')
                       | specialize (fun y z a => @H _ y z a H')
                       | specialize (fun x z a => @H x _ z a H')
                       | specialize (fun x y a => @H x y _ a H')
                       | specialize (fun x => @H x _ _ _ eq_refl)
                       | specialize (fun y => @H _ y _ _ eq_refl)
                       | specialize (fun z => @H _ _ z _ eq_refl)
                       | specialize (fun a => @H _ _ _ a eq_refl)
                       | specialize (fun x y => @H x y _ _ eq_refl)
                       | specialize (fun y z => @H _ y z _ eq_refl)
                       | specialize (fun z a => @H _ _ z a eq_refl)
                       | specialize (fun x a => @H x _ _ a eq_refl)
                       | specialize (fun x y z => @H x y z _ eq_refl)
                       | specialize (fun y z a => @H _ y z a eq_refl)
                       | specialize (fun x z a => @H x _ z a eq_refl)
                       | specialize (fun x y a => @H x y _ a eq_refl)
                       ]
           end.

  Lemma eapplicable_sound'
  : forall s tus tvs lem g s1,
      eapplicable s tus tvs lem g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall sD (gD : exprT _ _ Prop),
        (@lemmaD _ _ _ _ _ (exprD'_typ0 (T:=Prop)) _ nil nil lem) ->
        substD (tus ++ lem.(vars)) tvs s = Some sD ->
        exprD'_typ0 (tus ++ lem.(vars)) tvs g = Some gD ->
        exists s1D (pDs : list (exprT _ _ Prop)),
          substR (tus ++ lem.(vars)) tvs s s1 /\
          substD (tus ++ lem.(vars)) tvs s1 = Some s1D /\
          mapT (fun e => exprD'_typ0 (tus ++ lem.(vars)) tvs (vars_to_uvars 0 (length tus) e)) lem.(premises) = Some pDs /\
          forall (us : hlist _ tus) (us' : hlist _ lem.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            (Forall (fun pD => pD (hlist_app us us') vs) pDs -> gD (hlist_app us us') vs)
            /\ sD (hlist_app us us') vs.
  Proof.
    unfold eapplicable. intros.
    eapply (@Hunify (tus ++ vars lem) tvs _ _ _ _ _ nil) in H; auto.
    forward_reason.
    split; eauto.

    simpl in *. intros.
    unfold exprD'_typ0 in H4; forward.
    inv_all; subst.
    specialize (fun v1 Hv1 => @H1 v1 _ _ Hv1 H4 H3).

    unfold lemmaD in H2. simpl in H2.
    forward.
    eapply lemmaD'_weakenU in H2; eauto.
    { revert H2. instantiate (1 := tus). simpl. intro.
      destruct H2 as [ ? [ ? ? ] ].
      unfold lemmaD' in H2. forward; inv_all; subst.
      rewrite exprD'_typ0_conv
         with (pfu := eq_refl) (pfv := eq_sym (app_nil_r_trans lem.(vars))) in H7.
      autorewrite with eq_rw in H7.
      unfold exprD'_typ0 in H7. forward; inv_all; subst.
      eapply (@vars_to_uvars_sound _ _ _ _ _ _ _ _ tus (concl lem) nil tyProp) in H7; eauto.
      forward_reason.
      eapply exprD'_weakenV with (tvs' := tvs) in H7; eauto.
      forward_reason.
      specialize (H1 _ H7).
      forward_reason.
      assert (exists pDs,
                List.mapT_list (F:=option)
                  (fun e1 : expr =>
                     exprD'_typ0 (tus ++ vars lem) tvs (vars_to_uvars 0 (length tus) e1))
                  (premises lem) = Some pDs /\
                forall us vs vs',
                  Forall (fun p => p (hlist_app us vs') vs) pDs <-> Forall (fun p => p us (hlist_app vs' Hnil)) l).
      { clear - H2 ExprOk_expr RTypeOk_typ ExprUVarOk_expr.
        revert l H2. induction (premises lem); simpl; intros; inv_all; subst.
        + eexists; split; [ reflexivity | intuition; constructor ].
        + forward; inv_all; subst.
          eapply IHl in H0; clear IHl.
          rewrite exprD'_typ0_conv
             with (pfu := eq_refl) (pfv := eq_sym (app_nil_r_trans _)) in H.
          autorewrite with eq_rw in H.
          forward.
          unfold exprD'_typ0 in H.
          forward.
          change (vars lem) with (nil ++ vars lem) in H.
          eapply vars_to_uvars_sound in H; eauto with typeclass_instances.
          forward_reason.
          eapply exprD'_weakenV with (tvs' := tvs) in H; eauto.
          forward_reason.
          unfold exprD'_typ0.
          change_rewrite H.
          change_rewrite H0.
          eexists; split; [ reflexivity | ].
          inv_all; subst.
          intros. autorewrite with eq_rw.
          Lemma Forall_iff : forall {T} (P : T -> Prop) a b,
                               Forall P (a :: b) <-> (P a /\ Forall P b).
          Proof. clear. split.
                 - inversion 1; auto.
                 - constructor; tauto.
          Qed.
          do 2 rewrite Forall_iff.
          Require Import ExtLib.Data.Prop.
          Lemma and_split_iff : forall (P Q R S : Prop),
                                  (P <-> R) -> (Q <-> S) ->
                                  ((P /\ Q) <-> (R /\ S)).
          Proof. clear. tauto. Qed.
          eapply and_split_iff; eauto.
          { specialize (H5 (hlist_app us vs') Hnil vs).
            simpl in *.
            rewrite <- H5; clear H5.
            rewrite <- H3; clear H3.
            simpl. rewrite hlist_app_nil_r.
            clear.
            generalize dependent (app_nil_r_trans (vars lem)).
            generalize dependent (vars lem ++ nil).
            intros; subst. reflexivity. } }
      forward_reason.
      do 2 eexists; split; eauto.
      split; eauto.
      split; eauto.
      intros.
      eapply H11 in H14; clear H11.
      clear - H14 H13 H12 H6 H9 H8 H5.
      destruct H14.
      repeat match goal with
               | H : _ , H' : _ |- _ =>
                 first [ specialize (H H') | specialize (H Hnil) ]
             end.
      rewrite H13; clear H13.
      split; auto.
      intros. autorewrite with eq_rw.
      simpl in *. rewrite <- H0; clear H0.
      specialize (H9 (hlist_app us us') Hnil vs).
      simpl in *. rewrite <- H9; clear H9.
      rewrite <- H8; clear H8.
      eapply H6 in H5; clear H6.
      rewrite foralls_sem in H5.
      specialize (H5 us').
      eapply impls_sem in H5.
      { revert H5.
        autorewrite with eq_rw.
        rewrite hlist_app_nil_r.
        generalize (app_nil_r_trans (vars lem)).
        generalize (vars lem ++ nil). intros; subst. eapply H5. }
      { rewrite List.Forall_map. assumption. } }
    { clear - ExprOk_expr.
      intros. eapply exprD'_typ0_weaken in H.
      destruct H. exists x.
      forward_reason; split; eauto.
      intros. rewrite <- H0. reflexivity. }
  Qed.

End lemma_apply.