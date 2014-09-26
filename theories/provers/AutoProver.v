Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.EProverI.
Require Import MirrorCore.ExprProp.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.ListMapT.

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

  Let provable (P : typD tyProp) : Prop :=
    match typ0_cast (F:=Prop) in _ = T return T with
      | eq_refl => P
    end.

  Let lemmaD :=
    @lemmaD _ _ _ Expr_expr expr
            (ExprDAs.exprD'_typ0 Prop)
            tyProp
            provable.

  Let lemmaD' :=
    @lemmaD' _ _ _ Expr_expr expr
            (ExprDAs.exprD'_typ0 Prop)
            tyProp
            provable.

  Record HintsOk (h : Hints) : Type :=
  { ApplyOk : Forall (lemmaD nil nil) h.(Apply)
  ; ExternOk : EProverOk h.(Extern)
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

  Context {ExprUVar_expr : VariablesI.ExprUVar expr}.
  Context {ExprUVarOk_expr : VariablesI.ExprUVarOk ExprUVar_expr}.
  Context {NSO : NormalizedSubstOk ExprUVar_expr SubstOk_subst}.


  Variable hints : Hints.
  Hypothesis hintsOk : HintsOk hints.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv (ctyp typ) -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> expr -> expr.

  Hypothesis exprUnify_sound : unify_sound SubstOk_subst exprUnify.
(*  Hypothesis NormlizedSubst : @NormalizedSubstOk _ _ _ _ . *)

  Let eapplicable :=
    @eapplicable typ _ expr Typ0_Prop subst vars_to_uvars exprUnify.

  Definition auto_prove_rec
     (auto_prove : hints.(Extern).(Facts) -> tenv (ctyp typ) -> tenv typ -> expr -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus : tenv (ctyp typ)) (tvs : tenv typ) (g : expr) (s : subst) : option subst :=
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
                                 instantiate (fun x => lookup x sub)
                                             (vars_to_uvars 0 len_tus h)
                             in
                             auto_prove facts (tus ++ List.map (mkctyp tvs) lem.(vars)) tvs e sub)
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
           (tus : tenv (ctyp typ)) (tvs : tenv typ) (g : expr) (s : subst) : option subst :=
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
                                  (tus : tenv (ctyp typ)) (tvs : tenv typ) (g : expr)
                                  (s : subst), option subst)
  := forall facts tus tvs g s s' (Hok : HintsOk hints),
       auto_prove facts tus tvs g s = Some s' ->
       WellFormed_subst s ->
       WellFormed_subst s' /\
       forall fD sD gD,
         factsD Hok.(ExternOk) tus tvs facts = Some fD ->
         substD tus s = Some sD ->
         Provable tus tvs g = Some gD ->
         exists sD',
           substD tus s' = Some sD' /\
           forall us vs,
             fD us vs ->
             sD' us ->
             sD us /\ gD us vs.

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

(*
  Hypothesis vars_to_uvars_sound : forall (tus0 : tenv (ctyp typ)) (e : expr) (tvs0 : list typ)
     (t : typ) (tvs' : list typ)
     (val : exprT tus0 (tvs0 ++ tvs') (typD t)),
   exprD' tus0 (tvs0 ++ tvs') e t = Some val ->
   exists val' : exprT (tus0 ++ List.map (mkctyp  tvs0) tvs') tvs0 (typD t),
     exprD' (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
       t = Some val' /\
     (forall (us : hlist typD tus0) (vs' : hlist typD tvs')
        (vs : hlist typD tvs0),
      val us (hlist_app vs vs') = val' (hlist_app us vs') vs).
*)

  Fixpoint hlist_OpenT_const_to_hlist_ctx (tvs ts : list typ)
           (h : hlist (fun t => OpenT.OpenT typD tvs (typD t)) ts)
  : hlist ctxD (List.map (mkctyp tvs) ts) :=
    match h in hlist _ ts return hlist ctxD (List.map (mkctyp tvs) ts) with
      | Hnil => Hnil
      | Hcons _ _ x h =>
        Hcons (l:=mkctyp tvs _) x (hlist_OpenT_const_to_hlist_ctx h)
    end.

  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        lemmaD' nil nil l0 = Some lD ->
        substD tus s = Some sD ->
        exprD' tus tvs g (@typ0 _ _ Prop _) = Some gD ->
        exists s1D gD',
          let nus := List.map (mkctyp tvs) l0.(vars) in
          substD (tus ++ nus) s1 = Some s1D /\
          exprD' tus (l0.(vars) ++ tvs) l0.(concl) (@typ0 _ _ Prop _) = Some gD' /\
          forall (us : hlist _ tus)
                 (us' : hlist (fun x => OpenT.OpenT _ tvs (typD x)) l0.(vars))
                 (vs : hlist _ tvs),
            s1D (hlist_app us (hlist_OpenT_const_to_hlist_ctx us')) ->
            (gD us vs =
             gD' us (hlist_app (hlist_map
                                  (F:=fun t => OpenT.OpenT _ tvs (typD t)) (G:=typD)
                                  (fun t g => g vs) us') vs))
            /\ sD us.
  Proof.
    intros. unfold eapplicable in H.
    eapply eapplicable_sound in H;
      eauto with typeclass_instances.
    forward_reason. split; eauto.
  Qed.

  Opaque Traversable.mapT impls.

  Hypothesis exprD'_instantiate : exprD'_instantiate instantiate.

  Lemma exprD'_instantiate_subst_Some
  : forall tus tvs sub e t eD sD,
      WellFormed_subst sub ->
      substD tus sub = Some sD ->
      exprD' tus tvs e t = Some eD ->
      exists eD',
        exprD' tus tvs (instantiate (fun x => lookup x sub) e) t = Some eD' /\
        forall us vs,
          sD us ->
          eD us vs = eD' us vs.
  Proof.
    intros.
    generalize exprD'_instantiate. unfold InstantiateI.exprD'_instantiate.
    intro XXX; eapply XXX with (f := fun x => lookup x sub) in H1; eauto.
    { simpl. clear - H H0.
      eapply sem_preserves_if_substD; eauto. }
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
      eapply applicable_sound in H2; eauto.
      simpl in *; forward_reason.
      specialize (fun sD gD => H7 _ sD gD H5).
      eapply lemmaD'_weaken  with (tus' := tus) (tvs' := tvs) in H5; eauto.
      { simpl in *.
        destruct H5 as [ ? [ ? ? ] ].
        unfold Lemma.lemmaD' in H5; forwardy; inv_all; subst.
        cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ map (mkctyp tvs) l.(vars)) s0 = Some sD ->
              Provable tus (vars l ++ tvs) (concl l) = Some gD ->
              exists sD',
                substD (tus ++ map (mkctyp tvs) l.(vars)) s1 = Some sD' /\
                (forall (us : hlist ctxD tus)
                        (vs : hlist typD tvs)
                        (vs' : hlist (fun t => OpenT typD tvs (typD t)) (vars l)),
                   let vs'' := hlist_map (fun t (x : OpenT typD tvs (typD t)) => x vs) vs' in
                   fD us vs ->
                   sD' (hlist_app us (holes_convert _ vs')) ->
                      sD (hlist_app us (holes_convert _ vs'))
                   /\ (impls
                         (map (fun x => provable (x us (hlist_app vs'' vs))) y)
                         (gD us (hlist_app vs'' vs)) ->
                       gD us (hlist_app vs'' vs))))).
        { intros; forward_reason.
          eapply pull_sound in H4; eauto.
          forward_reason; split; eauto.
          intros.
          eapply H7 in H14; eauto.
          Focus 2.
          eapply substD_weaken with (tus' := map (mkctyp tvs) l.(vars)) in H14.
          forward_reason.
          specialize (fun H => H12 _ _ _ eq_refl H H14).

        
        
        
        

        }
      { intros.
        eapply ExprDAs.exprD'_typ0_weakenV in H8; eauto.
        revert H8. instantiate (1 := tvs').
        destruct 1 as [ ? [ ? ? ] ].
        eexists; split; eauto.
        intros; rewrite <- H9. reflexivity. } }
        















      unfold Lemma.lemmaD' in H5. forward. inv_all; subst.
      cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ map (mkctyp tvs) l.(vars)) s0 = Some sD ->
              Provable tus (vars l ++ tvs) (concl l) = Some gD ->
              exists sD',
                substD (tus ++ map (mkctyp tvs) l.(vars)) s1 = Some sD' /\
                (forall (us : hlist ctxD tus)
                        (vs : hlist typD tvs)
                        (vs' : hlist (fun t => OpenT typD tvs (typD t)) (vars l)),
                   fD us vs ->
                   sD' (hlist_app us (holes_convert _ vs')) ->
                      sD (hlist_app us (holes_convert _ vs'))
                   /\ (impls
                         (map (fun x => provable (x Hnil (hlist_app vs' Hnil))) l0)
                         (gD us (hlist_app vs' vs)) ->
                       gD us (hlist_app vs' vs))))).
      { (** This is actually applying the lemma **)
        clear H3 H5 H recurse H0.
        intros.
        forward_reason.
        eapply pull_sound in H4; eauto.
        forward_reason.
        split; auto. intros. (*
        specialize (fun tvs0 sD => H4 _ _ tvs0 sD eq_refl eq_refl).
        unfold Provable in H10.
        forwardy.
        specialize (H7 _ _ H9 H10).
        forward_reason.
        specialize (H0 _ _ _ H5 H7  *)
        progress fill_holes. (** NOTE: This is very inefficient **)
        assert (exists y,
                  Provable tus (vars l ++ tvs) (concl l) = Some y /\
                  forall a b c,
                    P0 Hnil (hlist_app a Hnil) <-> y b (hlist_app a c)).
        { unfold ResType in H8.
          rewrite eq_option_eq in H8.
          forwardy.
          eapply (@ExprI.exprD'_weaken _ _ _ Expr_expr)
          with (tus' := tus) (tvs' := tvs) in H8; eauto with typeclass_instances.
          simpl in H8. destruct H8 as [ ? [ ? ? ] ].
          generalize (@exprD'_conv _ _ _ Expr_expr tus tus (vars l ++ tvs) ((vars l ++ nil) ++ tvs) (concl l) tyProp eq_refl (app_ass_trans _ _ _)).
          rewrite H8.
          unfold Provable.
          intro XXX; change_rewrite XXX; clear XXX.
          unfold ResType. rewrite eq_option_eq.
          eexists; split; eauto. inv_all.
          subst.
          intros. repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          erewrite H12.
          instantiate (1 := c). instantiate (1 := b).
          simpl.
          rewrite hlist_app_assoc. simpl. reflexivity. }
        destruct H11 as [ ? [ ? ? ] ].
        unfold Provable, ResType in *. forwardy.
        specialize (H7 _ H10).
        forward_reason.
        rewrite eq_option_eq in H8.
        forwardy.
        rewrite H11 in *.
        specialize (H0 _ _ H7 eq_refl).
        forward_reason.
        specialize (H4 _ _ H0).
        forward_reason.
        eexists; split; eauto.
        intros.
        repeat match goal with
                 | H : _ |- _ => specialize (H us vs)
               end.
        eapply H22 in H24; clear H22.
        inv_all; subst.
        rewrite foralls_sem in H6.
        remember (hlist_map
                (fun (t : typ)
                   (x : hlist typD tus ->
                        hlist typD tvs -> typD t) =>
                 x us vs) x4).
        specialize (H6 h).
        specialize (H17 _ H23 H24).
        specialize (H12 h us vs).
        rewrite impls_sem in H6.
        rewrite H12 in H6; clear H12.
        rewrite <- impls_sem in H6.
        clear - Heqh H24 H6 H21 H17 H15 H11.
        forward_reason.
        eapply H15 in H; clear H15.
        forward_reason. split; eauto.
        unfold exprD in H.
        rewrite join_env_app in H.
        do 2 rewrite split_env_join_env in H.
        change_rewrite H11 in H.
        inv_all.
        autorewrite with eq_rw.
        rewrite <- H; clear H.
        autorewrite with eq_rw in H0.
        assumption. }
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
          unfold Provable in *.
          forwardy.
          forward_reason.
          change_rewrite H13 in H3.
          specialize (H3 _ eq_refl).
          forward_reason.
          apply H6 in H3; clear H6.
          forward_reason.
          eexists; split; eauto.
          intros.
          specialize (H6 _ _ _ H17 H18).
          forward_reason.
          eapply H12 in H17; clear H12.
          specialize (H16 _ _ H17 H6).
          forward_reason; split; auto.
          intro. apply H19.
          simpl in H20.
          Transparent impls. simpl impls in H20.
          Opaque impls.
          eapply H20; clear H20.
          erewrite <- H15 by eassumption.
          clear - H16.
          red.
          autorewrite with eq_rw in H16.
          assumption. } } *) admit. }
  Qed.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.
