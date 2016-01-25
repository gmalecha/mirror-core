Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.EProverI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Instantiate.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Set Printing Universes.
Set Printing All.
(** NOTE: This entire prover could be over an arbitrary logic if we change
 **       lemma to be over an arbitrary ILogic
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  Record Hints : Type :=
  { Apply : list (lemma typ expr expr)
  ; Extern : @EProver typ expr
  }.

  Let lemmaD :=
    @lemmaD _ _ _ Expr_expr expr (exprD'_typ0 (T:=Prop)) _.

  Let lemmaD' :=
    @lemmaD' _ _ _ Expr_expr expr (exprD'_typ0 (T:=Prop)) _.

  Record HintsOk (h : Hints) : Type :=
  { ApplyOk : Forall (lemmaD nil nil) h.(Apply)
  ; ExternOk : EProverOk h.(Extern)
  }.

  (** TODO: This is essentially [filter_map] **)
  (** TODO(gmalecha): building this lazily might be very helpful *)
  Section get_applicable.
    Variable subst : Type.
    Context {Subst_subst : Subst subst expr}.
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
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk subst typ expr}.
  Context {SU : SubstUpdate subst expr}.
  Context {SubstUpdateOk : SubstUpdateOk subst typ expr}.
  Context {SO : SubstOpen subst}.
  Context {SubstOpenOk : SubstOpenOk _ SO}.

  Variable hints : Hints.
  Hypothesis hintsOk : HintsOk hints.

  Variable exprUnify : unifier typ expr subst.

  Hypothesis exprUnify_sound : unify_sound exprUnify.

  Let eapplicable :=
    @eapplicable typ expr _ _ Typ0_Prop subst _ exprUnify.

  Definition auto_prove_rec
             (auto_prove : hints.(Extern).(Facts) -> tenv typ -> tenv typ -> expr -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus tvs : tenv typ) (g : expr) (s : subst) : option subst :=
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
                                 instantiate (fun x => subst_lookup x sub) 0
                                             (vars_to_uvars 0 len_tus h)
                             in
                             auto_prove facts (tus ++ lem.(vars)) tvs e sub)
                          lem.(premises)
                          sub
            with
              | None => None
              | Some sub => subst_pull len_tus from sub
            end
        in
        first_success check
                      (@get_applicable subst g (eapplicable s tus tvs) hints.(Apply))
    end.

  Fixpoint auto_prove (fuel : nat)
           (facts : hints.(Extern).(Facts))
           (tus tvs : tenv typ) (g : expr) (s : subst) : option subst :=
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
                                  (tus tvs : tenv typ) (g : expr)
                                  (s : subst), option subst)
  := forall facts tus tvs g s s' (Hok : HintsOk hints),
       auto_prove facts tus tvs g s = Some s' ->
       WellFormed_subst s ->
       WellFormed_subst s' /\
       forall fD sD gD,
         factsD Hok.(ExternOk) tus tvs facts = Some fD ->
         substD tus tvs s = Some sD ->
         exprD'_typ0 tus tvs g = Some gD ->
         exists sD',
           substD tus tvs s' = Some sD' /\
           forall us vs,
             fD us vs ->
             sD' us vs ->
             sD us vs /\ gD us vs.

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

  Lemma vars_to_uvars_sound_typ0
  : forall (tus0 : tenv typ) (e : expr) (tvs0 : list typ)
           (tvs' : list typ)
           (val : exprT tus0 (tvs0 ++ tvs') Prop),
      exprD'_typ0 tus0 (tvs0 ++ tvs') e = Some val ->
      exists val' : exprT (tus0 ++ tvs') tvs0 Prop,
        exprD'_typ0 (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
        = Some val' /\
        (forall (us : hlist typD tus0) (vs' : hlist typD tvs')
                (vs : hlist typD tvs0),
           val us (hlist_app vs vs') = val' (hlist_app us vs') vs).
  Proof.
    unfold exprD'_typ0; simpl; intros.
    specialize (@vars_to_uvars_sound typ expr _ _ _ _ _ ExprUVarOk_expr tus0 e tvs0 (typ0 (F:=Prop)) tvs').
    forward; inv_all; subst.
    specialize (H1 _ eq_refl).
    destruct H1 as [ ? [ ? ? ] ].
    rewrite H0.
    eexists; split; eauto.
    intros; autorewrite with eq_rw. rewrite H1.
    reflexivity.
  Qed.

(*
  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        lemmaD' nil nil l0 = Some lD ->
        substD tus tvs s = Some sD ->
        exprD'_typ0 tus tvs g = Some gD ->
        exists s1D gD',
          substD (tus ++ l0.(vars)) tvs s1 = Some s1D /\
          exprD'_typ0 tus (l0.(vars) ++ tvs) l0.(concl) = Some gD' /\
          forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            (gD us vs <-> gD' us (hlist_app us' vs)) /\ sD us vs.
  Proof.
    intros. unfold eapplicable in H.
    eapply eapplicable_sound in H;
      eauto with typeclass_instances.
    forward_reason. split; eauto.
    intros.
    eapply H1 in H3; eauto.
    forward_reason.
    do 2 eexists; split; eauto.
    split; eauto.
    clear - H6. intros.
    eapply H6 in H. clear - H.
    intuition.
  Qed.
*)
  Opaque Traversable.mapT impls.
(*
  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.
*)

  Lemma exprD'_instantiate_subst_Some
  : forall tus tvs sub e t eD sD,
      WellFormed_subst sub ->
      substD tus tvs sub = Some sD ->
      exprD' tus tvs e t = Some eD ->
      exists eD',
        exprD' tus tvs (instantiate (fun x => subst_lookup x sub) 0 e) t = Some eD' /\
        forall us vs,
          sD us vs ->
          eD us vs = eD' us vs.
  Proof.
    intros.
    edestruct (fun P HP => @instantiate_sound _ _ _ _ _ tus tvs (fun x => subst_lookup x sub) _ nil _ _ P HP H1).
    { simpl. clear - H H0.
      eapply sem_preserves_if_substD; eauto. }
    { forward_reason.
      eexists; split; [ eapply H2 | ].
      intros. specialize (H3 us vs Hnil).
      exact (H3 H4). }
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
      eapply (Prove_sound Hok.(ExternOk)) in H0.
      forward_reason.
      split; auto. }
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
      admit. (*
      eapply applicable_sound in H2; eauto.
      simpl in *; forward_reason.
      specialize (fun sD gD => H7 _ sD gD H5).
      unfold Lemma.lemmaD' in H5. forward. inv_all; subst.
      cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ vars l) tvs s0 = Some sD ->
              exprD'_typ0 tus (vars l ++ tvs) (concl l) = Some gD ->
              exists sD',
                substD (tus ++ vars l) tvs s1 = Some sD' /\
                (forall (us : hlist typD tus)
                        (vs : hlist typD tvs)
                        (vs' : hlist typD (vars l)),
                   fD us vs ->
                   sD' (hlist_app us vs') vs ->
                      sD (hlist_app us vs') vs
                   /\ (impls
                         (map (fun x => x Hnil (hlist_app vs' Hnil)) l0)
                         (gD us (hlist_app vs' vs)) ->
                       gD us (hlist_app vs' vs))))).
      { (** This is actually applying the lemma **)
        clear H3 H5 H recurse H0.
        intros.
        forward_reason.
        eapply pull_sound_sem in H4; eauto.
        forward_reason.
        split; auto. intros.
        fill_holes.
        autorewrite with eq_rw in H8.
        forward; inv_all; subst.
        eapply H14 in H16; clear H14.
        eapply H13 in H16; clear H13.
        forward_reason.
        eapply H12 in H13; clear H12.
        destruct H13. split; auto.
        eapply H12; clear H12.
        eapply H14; clear H14.
        rewrite foralls_sem in H6.
        simpl in H6.
        specialize (H6 (hlist_map (fun t (x : exprT tus tvs _) => x us vs) x3)).
        simpl in *.
        eapply impls_sem. intros.
        eapply impls_sem in H6; eauto.
        eapply exprD'_typ0_weaken with (tus' := tus) (tvs' := tvs) in H8; eauto.
        forward_reason.
        simpl in *.
        rewrite exprD'_typ0_conv with (pfu := eq_refl)
                                      (pfv := eq_sym (app_ass_trans l.(vars) nil tvs))
          in H8.
        simpl in H8.
        autorewrite with eq_rw in H8.
        rewrite H11 in H8.
        inv_all; subst.
        specialize (H14 Hnil (hlist_app (hlist_map (fun (t : typ) (x4 : exprT tus tvs (typD t)) => x4 us vs)
           x3) Hnil) us vs).
        change_rewrite H14 in H6.
        clear - H6. simpl in *.
        autorewrite with eq_rw in H6.
        rewrite hlist_app_assoc in H6.
        simpl in H6.
        revert H6.
        match goal with
          | |- _ _ match _ with eq_refl => match ?P with eq_refl => ?X end end ->
               _ _ ?Y =>
            change Y with X; generalize X ; destruct P
        end.
        simpl. auto. }
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
          specialize (IHl0 _ H7 H _ eq_refl).
          forward_reason. split; auto.
          intros.
          specialize (fun sD gD => H6 _ sD _ H9 gD H11).
          eapply factsD_weakenU with (tus' := vars l) in H9.
          forward_reason.
          specialize (fun gD => H3 _ _ gD H9 H10).
          assert (exists y,
                    exprD'_typ0 (tus ++ vars l) tvs
                           (instantiate (fun x => subst_lookup x s0) 0
                                        (vars_to_uvars 0 (length tus) a)) = Some y /\
                    forall a b c,
                      sD (hlist_app a b) c ->
                      y (hlist_app a b) c = e Hnil (hlist_app b Hnil)).
          { eapply exprD'_typ0_weakenU with (tus' := tus) in H0; eauto.
            destruct H0 as [ ? [ ? ? ] ].
            rewrite exprD'_typ0_conv with (pfu := eq_refl)
                                          (pfv := eq_sym (app_nil_r_trans l.(vars))) in H0.
            autorewrite with eq_rw in H0.
            forwardy.
            eapply vars_to_uvars_sound_typ0 with (tvs0 := nil) in H0; eauto.
            destruct H0 as [ ? [ ? ? ] ].
            eapply exprD'_typ0_weakenV with (tvs' := tvs) in H0; eauto.
            destruct H0 as [ ? [ ? ? ] ].
            simpl in *.
            unfold exprD'_typ0 in *.
            forwardy.
            edestruct (@exprD'_instantiate_subst_Some
                          (tus ++ vars l)
                          tvs
                          s0
                          (vars_to_uvars 0 (length tus) a)
                          tyProp) as [ ? [ ? ? ] ]; eauto.
            change_rewrite H20.
            eexists; split; eauto.
            intros.
            inv_all; subst.
            autorewrite with eq_rw.
            rewrite <- H21; clear H21; eauto.
            specialize (H16 (hlist_app a0 b) Hnil c).
            autorewrite with eq_rw in H16.
            simpl in *. rewrite <- H16; clear H16.
            clear - H15 H13.
            rewrite <- H15; clear H15.
            specialize (H13 Hnil a0 (hlist_app b Hnil)).
            simpl in *.
            rewrite H13.
            autorewrite with eq_rw.
            f_equal.
            rewrite hlist_app_nil_r.
            clear.
            match goal with
              | |- _ = match eq_sym ?X with eq_refl => match ?Y with _ => _ end end =>
                change Y with X; destruct X
            end. reflexivity. }
          forwardy.
          forward_reason.
          change_rewrite H13 in H3.
          specialize (H3 _ eq_refl).
          forward_reason.
          apply H6 in H3; clear H6.
          forward_reason.
          eexists; split; eauto.
          intros.
          specialize (H6 _ _ _ H16 H17).
          forward_reason.
          eapply H12 in H16; clear H12.
          specialize (H15 _ _ H16 H6).
          forward_reason; split; auto.
          intro. eapply H18.
          Transparent impls. simpl impls in H19.
          Opaque impls.
          eapply H19; clear H19.
          erewrite <- H14 by eassumption.
          assumption. } }  *) }
  Admitted.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.
