Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Subst.FastSubst.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprSubst.
Require Import MirrorCore.Ext.ExprUnifySyntactic3.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

(** NOTE: This entire prover could be over an arbitrary logic if we change
 **       lemma to be over an arbitrary ILogic
 **)
Section parameterized.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : SymI.RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.

  (** TODO: This should be generalized **)
  Let Expr_expr := @Expr_expr ts func RSym_func.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  Record Hints : Type :=
  { Apply : list (lemma typ (expr func) (expr func))
  ; Extern : @EProver typ (expr func)
  }.

  Record HintsOk (h : Hints) : Type :=
  { ApplyOk : Forall (@lemmaD _ _ _ Expr_expr (expr func)
                              (fun tus tvs g =>
                                 @exprD' ts _ RSym_func tus tvs g tyProp)
                              tyProp
                              (fun x => x)
                              nil nil) h.(Apply)
  ; ExternOk : @EProverOk _ (typD ts) (expr func) _ tyProp (fun x => x) h.(Extern)
  }.

  (** TODO: This is essentially [filter_map] **)
  Section get_applicable.
    Variable subst : Type.
    Variable Subst_subst : Subst subst (expr func).
    Variable goal : expr func.

    Variable applicable : forall (l : lemma typ (expr func) (expr func)) (g : expr func),
      option subst.

    Fixpoint get_applicable (ls : list (lemma typ (expr func) (expr func)))
    : list (lemma typ (expr func) (expr func) * subst) :=
        match ls with
          | nil => nil
          | l :: ls =>
            match applicable l goal with
              | None => get_applicable ls
              | Some s => (l,s) :: get_applicable ls
            end
        end.
  End get_applicable.

  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr func).
  Variable SubstOk_subst : SubstOk _ Subst_subst.
  Variable SU : SubstUpdate subst (expr func).
  Variable SubstUpdateOk : SubstUpdateOk SU _.

  Variable hints : Hints.
  Hypothesis hintsOk : HintsOk hints.

  Definition fuel := 100.
  Let eapplicable :=
    @eapplicable typ (expr func) tyProp subst
                 (fun s a e => vars_to_uvars e s a)
                 (fun tus tvs under e1 e2 ty sub =>
                    @exprUnify subst _ _ RSym_func Subst_subst SU fuel
                               tus tvs under sub e1 e2 ty).

  Definition auto_prove_rec
             (auto_prove : hints.(Extern).(Facts) -> EnvI.tenv typ -> EnvI.tenv typ -> expr func -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus tvs : EnvI.tenv typ) (g : expr func) (s : subst) : option subst :=
    match @Prove _ _ hints.(Extern) subst _ facts tus tvs s g with
      | Some s =>
        (** solved by extern **)
        Some s
      | None =>
        (** try resolution **)
        let len_tus := length tus in
        let check lem_sub :=
            (** check to make sure that all of the premises are provable **)
            let '(lem,sub) := lem_sub in
            let from := length lem.(vars) in
            match
              all_success (fun h sub =>
                             let e :=
                                 instantiate (fun x => lookup x sub) 0
                                             (vars_to_uvars h 0 len_tus)
                             in
                             auto_prove facts (tus ++ lem.(vars)) tvs e sub)
                          lem.(premises)
                          sub
            with
              | None => None
              | Some sub =>
                pull len_tus from sub
            end
        in
        first_success check
                      (@get_applicable subst g (eapplicable s tus tvs) hints.(Apply))
    end.

  Fixpoint auto_prove (fuel : nat)
           (facts : hints.(Extern).(Facts))
           (tus tvs : EnvI.tenv typ) (g : expr func) (s : subst) : option subst :=
    match fuel with
      | 0 => None
      | S fuel =>
        auto_prove_rec
          (** NOTE: eta-expansion here is important **)
          (fun facts a b c d => auto_prove fuel facts a b c d)
          facts tus tvs g s
    end.

  Definition auto_prove_sound_ind
             (auto_prove : forall (facts : hints.(Extern).(Facts))
                                  (tus tvs : EnvI.tenv typ) (g : expr func)
                                  (s : subst), option subst)
  := forall facts tus tvs g s s' (Hok : HintsOk hints),
       auto_prove facts tus tvs g s = Some s' ->
       WellFormed_subst s ->
       WellFormed_subst s' /\
       forall fD sD gD,
         factsD Hok.(ExternOk) tus tvs facts = Some fD ->
         substD tus tvs s = Some sD ->
         exprD' tus tvs g tyProp = Some gD ->
         exists sD',
           substD tus tvs s' = Some sD' /\
           forall us vs,
             fD us vs ->
             sD' us vs ->
             gD us vs /\ sD us vs.

  Lemma get_applicable_sound
  : forall g app lems,
      Forall (fun ls : (lemma typ (expr func) (expr func) * subst) =>
                let '(l,s) := ls in
                In l lems /\ app l g = Some s)
             (get_applicable g app lems).
  Proof.
    clear. induction lems; simpl; intros.
    { constructor. }
    { consider (app a g); intros.
      { constructor; eauto.
        eapply Forall_impl; eauto.
        simpl in *. destruct a0. intuition. }
      { eapply Forall_impl; eauto.
        simpl in *. destruct a0. intuition. } }
  Qed.

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

  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        @lemmaD' _ _ _ _ _
                 (fun tus tvs g => @exprD' ts _ RSym_func tus tvs g tyProp)
                 tyProp
                 (fun x => x)
                 nil nil l0 = Some lD ->
        substD tus tvs s = Some sD ->
        exprD' tus tvs g tyProp = Some gD ->
        exists s1D,
          substD (tus ++ l0.(vars)) tvs s1 = Some s1D /\
          forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            exprD (join_env us) (join_env us' ++ join_env vs) l0.(concl) tyProp =
            Some (gD us vs)
            /\ sD us vs.
  Proof.
    intros. unfold eapplicable in H.
    eapply eapplicable_sound with (tyProp := tyProp)
      (tyPropD := fun ts' => (@eq_refl _ Prop) : (typD ts ts' tyProp = Prop)) in H; eauto with typeclass_instances.
    { intuition. }
    { red. intros.
      eapply (@exprUnify_sound _ _ _ _ RSymOk_func _ _ _ SubstUpdateOk
                               fuel tu _ _ _ _ _ _ _ H1); auto. }
    { intros. clear H eapplicable.
      simpl in *.
      generalize (@vars_to_uvars_exprD' _ _ _ tus0 e _ t _ _ H1);
        intuition. }
  Qed.

  Opaque Traversable.mapT impls.

  Lemma exprD'_instantiate_subst_Some
  : forall tus tvs tvs' sub e t eD sD,
      WellFormed_subst sub ->
      substD tus tvs sub = Some sD ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate (fun x => lookup x sub) (length tvs') e) t = Some eD' /\
        forall us vs vs',
          sD us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).
  Proof.
    clear.
    intros.
    destruct (fun H =>
                  @exprD'_instantiate_Some _ _ _ (fun x => lookup x sub)
                                           tus tvs sD H
                                           e tvs' t eD H1) as [ ? [ ? ? ] ].
    { intros.
      eapply substD_lookup in H3; eauto.
      simpl in H3.
      eapply nth_error_get_hlist_nth_Some in H2.
      simpl in *.
      forward_reason.
      assert (t' = x).
      {  clear - x1 x2. rewrite <- x1 in x2. inv_all; auto. }
      subst.
      eexists; split; eauto.
      intros. eapply H4 in H5; clear H4.
      specialize (H2 us).
      rewrite H2; clear H2.
      match goal with
        | H : ?X = _ |- context [ ?Y ] =>
          change Y with X ; rewrite H
      end.
      clear.
      replace x1 with (eq_sym x2).
      { clear. revert x0. revert us.
        change (typD ts nil x)
        with   (match Some x with
                  | Some x1 => typD ts nil x1
                  | None => unit
                end).
        destruct x2.
        reflexivity. }
      { generalize x1. generalize x2.
        rewrite x1. intros.
        uip_all. reflexivity.  (** this is a little messy, but it works **) } }
    { eexists; split; eauto. }
  Qed.

  Lemma auto_prove_rec_sound
  : forall recurse,
      auto_prove_sound_ind recurse ->
      auto_prove_sound_ind (auto_prove_rec recurse).
  Proof.
    red. unfold auto_prove_rec. intros.
    match goal with
      | _ : match ?X with _ => _ end = _ |- _ =>
        consider X; intros; inv_all; subst; auto
    end.
    { (** Extern **)
      eapply (@Prove_sound _ _ _ _ _ _ _ Hok.(ExternOk)) in H0.
      forward_reason.
      split; auto. intros.
      specialize (H2 _ _ _ H3 H4 H5).
      forward_reason.
      eexists; split; eauto.
      intros.
      specialize (H6 _ _ H7). intuition. }
    { (** Apply **)
      clear H0.
      eapply first_success_sound in H2.
      forward_reason.
      forward. subst.
      generalize (get_applicable_sound g (eapplicable s tus tvs) (Apply hints)).
      intro. eapply Forall_forall in H2; [ | eassumption ].
      simpl in *. clear H0. forward_reason.
      specialize (proj1 (Forall_forall _ _) (ApplyOk Hok) _ H0); intro.
      red in H5. simpl in *.
      forward.
      eapply applicable_sound in H2; eauto.
      simpl in *; forward_reason.
      specialize (fun sD gD => H7 _ sD gD H5).
      unfold lemmaD' in H5. forward. inv_all; subst.
      cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ vars l) tvs s0 = Some sD ->
              exprD' tus (vars l ++ tvs) (concl l) tyProp = Some gD ->
              exists sD',
                substD (tus ++ vars l) tvs s1 = Some sD' /\
                (forall (us : hlist (typD ts nil) tus)
                        (vs : hlist (typD ts nil) tvs)
                        (vs' : hlist (typD ts nil) (vars l)),
                   fD us vs ->
                   sD' (hlist_app us vs') vs ->
                      (impls
                         (map (fun x => x Hnil (hlist_app vs' Hnil)) l0)
                         (gD us (hlist_app vs' vs)) ->
                       gD us (hlist_app vs' vs))
                   /\ sD (hlist_app us vs') vs))).
      { clear H3 H5 H recurse H0.
        intros.
        forward_reason.
        eapply pull_sound in H4; eauto.
        forward_reason.
        split; auto. intros.
        assert (exists y,
                  exprD' tus (vars l ++ tvs) (concl l) tyProp = Some y /\
                  forall a b c,
                    t Hnil (hlist_app a Hnil) = y b (hlist_app a c)).
        { eapply (@ExprI.exprD'_weaken _ _ _ Expr_expr)
          with (tus' := tus) (tvs' := tvs) in H8; eauto with typeclass_instances.
          simpl in H8. destruct H8 as [ ? [ ? ? ] ].
          generalize (@exprD'_conv _ _ _ Expr_expr tus tus (vars l ++ tvs) ((vars l ++ nil) ++ tvs) (concl l) tyProp eq_refl (app_ass_trans _ _ _)).
          simpl.
          rewrite H8. intro XXX; rewrite XXX; clear XXX.
          assert (match
                     app_ass_trans (vars l) nil tvs in (_ = tvs')
                     return (ResType (typD ts) tus tvs' Prop)
                   with
                     | eq_refl => Some x
                   end = Some match
                             app_ass_trans (vars l) nil tvs in (_ = tvs')
                             return _ -> hlist _ tvs' -> _
                           with
                             | eq_refl => x
                           end).
          { clear. revert x.
            destruct (app_ass_trans (vars l) nil tvs). reflexivity. }
          eexists; split. eapply H12.
          clear H12. intros. erewrite H11.
          instantiate (1 := c). instantiate (1 := b).
          simpl.
          rewrite hlist_app_assoc.
          clear. revert x.
          simpl. generalize dependent (hlist_app a c).
          generalize (app_ass_trans (vars l) nil tvs).
          change (vars l ++ tvs) with (vars l ++ (nil ++ tvs)).
          destruct e. reflexivity. }
        destruct H11 as [ ? [ ? ? ] ].
        progress fill_holes.
        repeat match goal with
                 | H : _ |- _ => specialize (H us vs)
               end.
        match goal with
          | _ : let x := ?X in _ |- _ => remember X
        end.
        simpl in *.
        specialize (H12 h).
        fill_holes.
        unfold exprD in H13.
        rewrite split_env_app in H13.
        repeat rewrite split_env_join_env in H13.
        simpl in *.
        rewrite H11 in H13.
        inv_all.
        rewrite <- H13; clear H13.
        apply H14; clear H14.
        rewrite foralls_sem with (typD := typD ts) in H6.
        eapply impls_sem. intros.
        rewrite <- H12.
        specialize (H6 h).
        rewrite impls_sem in H6.
        eapply H6. eassumption. }
      { clear H6 H4 H0 H7.
        generalize dependent l0.
        generalize dependent s0.
        generalize dependent (premises l).
        induction l0.
        { simpl. intros; inv_all; subst.
          rewrite list_mapT_nil in H5.
          inv_all; subst.
          split; auto. intros.
          eexists; split; eauto. }
        { simpl. intros.
          rewrite list_mapT_cons in H5.
          forward.
          specialize (H _ _ _ _ _ _ Hok H3 H2); clear H3.
          inv_all; subst.
          destruct H.
          specialize (IHl0 _ H7 H _ H4); clear H7 H4.
          forward_reason. split; auto.
          intros.
          progress fill_holes.
          eapply factsD_weakenU with (tus' := vars l) in H6.
          destruct H6 as [ ? [ ? ? ] ].
          assert (exists y,
                    exprD' (tus ++ vars l) tvs
                           (instantiate (fun x : uvar => lookup x s0) 0
                                        (vars_to_uvars a 0 (length tus))) tyProp =
                    Some y /\
                    forall a b c,
                      sD (hlist_app a b) c ->
                      y (hlist_app a b) c = t0 Hnil (hlist_app b Hnil)).
          { eapply (@exprD'_weakenU _ _ _ Expr_expr) with (tus' := tus) in H0;
            eauto with typeclass_instances.
            destruct H0 as [ ? [ ? ? ] ].
            change (vars l ++ nil) with (nil ++ (vars l ++ nil)) in H0.
            simpl ExprI.exprD' in H0.
            eapply vars_to_uvars_exprD' in H0.
            destruct H0 as [ ? [ ? ? ] ].
            simpl in H0.
            eapply (@exprD'_weakenV _ _ _ Expr_expr) with (tvs' := tvs) (t := tyProp) in H0; eauto with typeclass_instances.
            destruct H0 as [ ? [ ? ? ] ].
            simpl in H0.

            assert (exists y,
                      exprD' (tus ++ vars l) tvs (vars_to_uvars a 0 (length tus))
                             tyProp = Some y /\
                      forall us vs vs',
                        x2 (hlist_app us (hlist_app vs Hnil)) vs' =
                        y (hlist_app us vs) vs').
            { generalize (@exprD'_conv _ _ _ Expr_expr
                                   (tus ++ vars l) (tus ++ vars l ++ nil)
                                   tvs tvs
                                   (vars_to_uvars a 0 (length tus))
                                   tyProp).
              simpl. intro XXX; erewrite XXX; clear XXX.
              instantiate (1 := eq_refl).
              instantiate (1 := match eq_sym (app_nil_r_trans (vars l)) in _ = tvs'
                                      return tus ++ tvs' = tus ++ vars l
                                with
                                  | eq_refl => eq_refl
                                end).
              simpl. rewrite H0.
              exists match
                  match
                    eq_sym (app_nil_r_trans (vars l)) in (_ = tvs')
                    return (tus ++ tvs' = tus ++ vars l)
                  with
                    | eq_refl => eq_refl
                  end in (_ = tus') return hlist _ tus' -> hlist _ tvs -> Prop
                with
                  | eq_refl => x2
                end.
              split.
              { clear. revert x2.
                destruct (app_nil_r_trans (vars l)).
                reflexivity. }
              { clear. intros.
                rewrite hlist_app_nil_r.
                revert x2. revert vs.
                destruct (app_nil_r_trans (vars l)).
                reflexivity. } }
            destruct H14 as [ ? [ ? ? ] ].
            destruct (@exprD'_instantiate_subst_Some
                          (tus ++ vars l)
                          tvs
                          nil
                          s0
                          (vars_to_uvars a 0 (length tus))
                          tyProp _ _ H2 H7 H14) as [ ? [ ? ? ] ].
            simpl in *.
            eexists; split; eauto.
            intros.
            repeat match goal with
                     | [ H : forall x : hlist _ _, _ , H' : _ |- _ ] =>
                       specialize (H H') || specialize (H Hnil)
                   end.
            erewrite H11.
            instantiate (1 := a0).
            simpl.
            specialize (H12 (hlist_app b Hnil) Hnil).
            simpl in H12. rewrite H12; clear H12.
            erewrite H13; clear H13.
            specialize (H17 (hlist_app a0 b) c Hnil H18).
            simpl in H17. rewrite <- H17; clear H17.
            instantiate (1 := c). simpl. eauto. }
          destruct H11 as [ ? [ ? ? ] ].
          progress fill_holes.
          repeat match goal with
                 | H : _ , H' : hlist _ _ |- _ => specialize (H H')
               end.
          apply H10 in H15; clear H10.
          apply H13 in H15; clear H13. destruct H15.
          split; auto.
          eapply H12 in H13; clear H12.
          intros.
          eapply H14; clear H14.
          simpl in H12.
          rewrite impls_sem in H12.
          eapply impls_sem. intros.
          eapply H12. constructor; auto.
          clear H12 H14.
          revert H10 H13. clear.
          intros.
          match goal with
            | H : _ = ?Y |- _ =>
              change Y ; rewrite <- H
          end.
          assumption. } } }
  Qed.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel0.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel0. }
  Qed.

End parameterized.
