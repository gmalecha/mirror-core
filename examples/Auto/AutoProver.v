Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

(** NOTE: This entire prover could be over an arbitrary logic if we change
 **       lemma to be over an arbitrary ILogic
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Expr_expr : Expr _ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.

  Let tyProp : typ := @typ0 _ _ _ _.

  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  Record Hints : Type :=
  { Apply : list (lemma typ expr expr)
  ; Extern : @EProver typ expr
  }.

  Let provable (P : typD nil tyProp) : Prop :=
    match typ0_cast nil in _ = T return T with
      | eq_refl => P
    end.

  Let lemmaD :=
    @lemmaD _ _ _ Expr_expr expr
            (fun tus tvs g =>
               match typ0_cast nil in _ = T return ResType tus tvs T with
                 | eq_refl => @exprD'  _ _ _ _ tus tvs g tyProp
               end)
            tyProp
            provable.

  Let lemmaD' :=
    @lemmaD' _ _ _ Expr_expr expr
            (fun tus tvs g =>
               match typ0_cast nil in _ = T return ResType tus tvs T with
                 | eq_refl => @exprD'  _ _ _ _ tus tvs g tyProp
               end)
            tyProp
            provable.

  Record HintsOk (h : Hints) : Type :=
  { ApplyOk : Forall (lemmaD nil nil) h.(Apply)
  ; ExternOk : @EProverOk _ RType_typ expr _ tyProp provable h.(Extern)
  }.

  (** TODO: This is essentially [filter_map] **)
  Section get_applicable.
    Variable subst : Type.
    Variable Subst_subst : Subst subst expr.
    Variable goal : expr.

    Variable applicable : forall (l : lemma typ expr expr) (g : expr),
      option subst.

    Fixpoint get_applicable (ls : list (lemma typ expr expr))
    : list (lemma typ expr expr * subst) :=
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
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : SubstOk _ Subst_subst.
  Variable SU : SubstUpdate subst expr.
  Variable SubstUpdateOk : SubstUpdateOk SU _.

  Variable hints : Hints.
  Hypothesis hintsOk : HintsOk hints.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Hypothesis exprUnify_sound : unify_sound SubstOk_subst exprUnify.

  Let eapplicable :=
    @eapplicable typ expr tyProp subst vars_to_uvars exprUnify.

  Definition auto_prove_rec
             (auto_prove : hints.(Extern).(Facts) -> EnvI.tenv typ -> EnvI.tenv typ -> expr -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus tvs : EnvI.tenv typ) (g : expr) (s : subst) : option subst :=
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
                                             (vars_to_uvars 0 len_tus h)
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
           (tus tvs : EnvI.tenv typ) (g : expr) (s : subst) : option subst :=
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
                                  (tus tvs : EnvI.tenv typ) (g : expr)
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
             provable (gD us vs) /\ sD us vs.

  Lemma get_applicable_sound
  : forall g app lems,
      Forall (fun ls : (lemma typ expr expr * subst) =>
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

  Hypothesis vars_to_uvars_sound : forall (tus0 : tenv typ) (e : expr) (tvs0 : list typ)
     (t : typ) (tvs' : list typ)
     (val : hlist (typD nil) tus0 ->
            hlist (typD nil) (tvs0 ++ tvs') -> typD nil t),
   exprD' tus0 (tvs0 ++ tvs') e t = Some val ->
   exists
     val' : hlist (typD nil) (tus0 ++ tvs') ->
            hlist (typD nil) tvs0 -> typD nil t,
     exprD' (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
       t = Some val' /\
     (forall (us : hlist (typD nil) tus0) (vs' : hlist (typD nil) tvs')
        (vs : hlist (typD nil) tvs0),
      val us (hlist_app vs vs') = val' (hlist_app us vs') vs).


  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        lemmaD' nil nil l0 = Some lD ->
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
    eapply eapplicable_sound with (tyProp := tyProp) in H;
      eauto with typeclass_instances.
  Qed.

  Opaque Traversable.mapT impls.

  Hypothesis exprD'_instantiate
  : forall f tus tvs e t P val,
      (forall u t' get,
         f u = Some e ->
         nth_error_get_hlist_nth _ tus u = Some (existT _ t' get) ->
         exists val,
           exprD' tus tvs e t' = Some val ->
           forall us vs,
             P us vs ->
             get us = val us vs) ->
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' tus tvs (instantiate f 0 e) t = Some val' /\
        forall us vs,
          P us vs ->
          val us vs = val' us vs.

  Lemma exprD'_instantiate_subst_Some
  : forall tus tvs sub e t eD sD,
      WellFormed_subst sub ->
      substD tus tvs sub = Some sD ->
      exprD' tus tvs e t = Some eD ->
      exists eD',
        exprD' tus tvs (instantiate (fun x => lookup x sub) 0 e) t = Some eD' /\
        forall us vs,
          sD us vs ->
          eD us vs = eD' us vs.
  Proof.
    intros. eapply exprD'_instantiate with (f := fun x => lookup x sub) in H1; eauto.
    { simpl. clear - H H0. intros.
      eapply substD_lookup in H0; eauto.
      forward_reason.
      eapply nth_error_get_hlist_nth_Some in H2.
      simpl in H2.
      destruct H2.
      assert (x = t').
      { clear - x2 x1. rewrite <- x1 in x2.
        inv_all; auto. }
      subst.
      eexists; split; eauto. }
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
      do 2 red in H5. simpl in *.
      forward.
      eapply applicable_sound in H2; eauto.
      simpl in *; forward_reason.
      specialize (fun sD gD => H7 _ sD gD H5).
      unfold Lemma.lemmaD' in H5. forward. inv_all; subst.
      cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ vars l) tvs s0 = Some sD ->
              exprD' tus (vars l ++ tvs) (concl l) tyProp = Some gD ->
              exists sD',
                substD (tus ++ vars l) tvs s1 = Some sD' /\
                (forall (us : hlist (typD nil) tus)
                        (vs : hlist (typD nil) tvs)
                        (vs' : hlist (typD nil) (vars l)),
                   fD us vs ->
                   sD' (hlist_app us vs') vs ->
                      (impls
                         (map (fun x => provable (x Hnil (hlist_app vs' Hnil))) l0)
                         (provable (gD us (hlist_app vs' vs))) ->
                       provable (gD us (hlist_app vs' vs)))
                   /\ sD (hlist_app us vs') vs))).
      { (** This is actually applying the lemma **)
        clear H3 H5 H recurse H0.
        intros.
        forward_reason.
        eapply pull_sound in H4; eauto.
        forward_reason.
        split; auto. intros. progress fill_holes.
        assert (exists y,
                  exprD' tus (vars l ++ tvs) (concl l) tyProp = Some y /\
                  forall a b c,
                    P0 Hnil (hlist_app a Hnil) <-> provable (y b (hlist_app a c))).
        { unfold ResType in H8. rewrite eq_option_eq in H8.
          forward.
          eapply (@ExprI.exprD'_weaken _ _ _ Expr_expr)
          with (tus' := tus) (tvs' := tvs) in H8; eauto with typeclass_instances.
          simpl in H8. destruct H8 as [ ? [ ? ? ] ].
          generalize (@exprD'_conv _ _ _ Expr_expr tus tus (vars l ++ tvs) ((vars l ++ nil) ++ tvs) (concl l) tyProp eq_refl (app_ass_trans _ _ _)).
          simpl.
          rewrite H8. intro XXX; rewrite XXX; clear XXX.
          unfold ResType. rewrite eq_option_eq.
          eexists; split; eauto. inv_all.
          subst.
          intros. repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          erewrite H13.
          instantiate (1 := c). instantiate (1 := b).
          simpl.
          rewrite hlist_app_assoc. simpl. reflexivity. }
        destruct H12 as [ ? [ ? ? ] ].
        progress fill_holes.
        repeat match goal with
                 | H : _ |- _ => specialize (H us vs)
               end.
        match goal with
          | _ : let x := ?X in _ |- _ => remember X
        end.
        simpl in *.
        specialize (H13 h).
        fill_holes.
        unfold exprD in *.
        rewrite split_env_app in *.
        repeat rewrite split_env_join_env in H11.
        simpl in *.
        rewrite H12 in H11.
        inv_all.
        rewrite <- H11; clear H11.
        apply H14; clear H14.
        eapply foralls_sem in H6.
        eapply impls_sem. intro.
        eapply impls_sem in H6; eauto. apply H13. assumption. }
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
          progress fill_holes.
          specialize (IHl0 _ eq_refl).
          forward_reason. split; auto.
          intros.
          progress fill_holes.
          eapply factsD_weakenU with (tus' := vars l) in H9.
          destruct H9 as [ ? [ ? ? ] ].
          assert (exists y,
                    exprD' (tus ++ vars l) tvs
                           (instantiate (fun x => lookup x s0) 0
                                        (vars_to_uvars 0 (length tus) a)) tyProp =
                    Some y /\
                    forall a b c,
                      sD (hlist_app a b) c ->
                      y (hlist_app a b) c = t Hnil (hlist_app b Hnil)).
          { eapply (@exprD'_weakenU _ _ _ Expr_expr) with (tus' := tus) in H0;
            eauto with typeclass_instances.
            destruct H0 as [ ? [ ? ? ] ].
            change (vars l ++ nil) with (nil ++ (vars l ++ nil)) in H0.
            simpl ExprI.exprD' in H0.
            eapply vars_to_uvars_sound in H0.
            destruct H0 as [ ? [ ? ? ] ].
            simpl in H0.
            eapply exprD'_weakenV with (tvs' := tvs) (t := tyProp) in H0; eauto with typeclass_instances.
            destruct H0 as [ ? [ ? ? ] ].
            simpl in H0.
            assert (exists y,
                      exprD' (tus ++ vars l) tvs (vars_to_uvars 0 (length tus) a)
                             tyProp = Some y /\
                      forall us vs vs',
                        x2 (hlist_app us (hlist_app vs Hnil)) vs' =
                        y (hlist_app us vs) vs').
            { generalize (@exprD'_conv _ _ _ Expr_expr
                                   (tus ++ vars l) (tus ++ vars l ++ nil)
                                   tvs tvs
                                   (vars_to_uvars 0 (length tus) a)
                                   tyProp).
              simpl. intro XXX; erewrite XXX; clear XXX.
              instantiate (1 := eq_refl).
              instantiate (1 := match eq_sym (app_nil_r_trans (vars l)) in _ = tvs'
                                      return tus ++ tvs' = tus ++ vars l
                                with
                                  | eq_refl => eq_refl
                                end).
              simpl. rewrite H0.
              unfold ResType. rewrite eq_option_eq.
              eexists; split; eauto.
              { clear. intros.
                rewrite hlist_app_nil_r.
                revert x2. revert vs.
                destruct (app_nil_r_trans (vars l)).
                reflexivity. } }
            destruct H16 as [ ? [ ? ? ] ].
            edestruct (@exprD'_instantiate_subst_Some
                          (tus ++ vars l)
                          tvs
                          s0
                          (vars_to_uvars 0 (length tus) a)
                          tyProp) as [ ? [ ? ? ] ]; eauto.
            simpl in *.
            eexists; split; eauto.
            intros.
            fill_holes.
            repeat match goal with
                     | [ H : forall x : hlist _ _, _ , H' : _ |- _ ] =>
                       specialize (H H') || specialize (H Hnil)
                   end.
            erewrite H13.
            instantiate (1 := a0).
            simpl in *.
            specialize (H14 (hlist_app b Hnil) Hnil). simpl in *.
            rewrite H14; clear H14.
            specialize (H15 (hlist_app a0 (hlist_app b Hnil)) Hnil c).
            specialize (H13 (hlist_app b Hnil) a0). simpl in *.
            etransitivity. 2: symmetry; eapply H15. clear H15.
            rewrite H17; clear H17.
            auto. }
          destruct H11 as [ ? [ ? ? ] ].
          progress fill_holes.
          repeat match goal with
                 | H : _ , H' : hlist _ _ |- _ => specialize (H H')
               end.
          apply H12 in H16; clear H12.
          apply H14 in H16; clear H14. destruct H16.
          split; auto.
          intros. apply H15.
          simpl in H16.
          rewrite impls_sem in H16.
          eapply impls_sem. intros.
          eapply H15.
          eapply impls_sem. intro. eapply H16; eauto.
          constructor; auto.
          apply H13 in H14. clear - H12 H14.
          match goal with
            | H : _ = ?Y |- _ =>
              change (provable Y) ; rewrite <- H
          end.
          assumption. } } }
  Qed.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.
