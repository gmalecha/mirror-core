Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section apply.
    Context {Subst_subst : Subst subst expr}.
    Context {SU : SubstUpdate subst expr}.

    Let eapplicable :=
      @eapplicable typ _ expr _ subst vars_to_uvars
                   exprUnify.

    (** Think of this like:
     **   apply lem ; cont
     ** i.e. first apply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition APPLY
               (lem : lemma typ expr expr)
               (tacC : stac_cont typ expr subst)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun tus tvs sub hs e =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let len_uvars := length tus in
          match pull (expr := expr) (SU := SU) len_uvars len_vars sub' with
            | Some sub'' =>
              let premises :=
                  map (fun e => instantiate (fun u => lookup u sub') 0
                                            (vars_to_uvars 0 len_uvars e))
                      lem.(premises)
              in
              tacC tus tvs sub'' hs premises
            | None => @Fail _ _ _
          end
      end.
  End apply.

  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst}.
  Variable UnifySound_exprUnify : unify_sound exprUnify.
  Context {NormalizedSubst : NormalizedSubstOk Subst_subst}.

  Hypothesis vars_to_uvars_sound : forall (tus0 : tenv typ) (e : expr) (tvs0 : list typ)
     (t : typ) (tvs' : list typ)
     (val : hlist typD tus0 ->
            hlist typD (tvs0 ++ tvs') -> typD t),
   exprD' tus0 (tvs0 ++ tvs') e t = Some val ->
   exists
     val' : hlist typD (tus0 ++ tvs') ->
            hlist typD tvs0 -> typD t,
     exprD' (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
       t = Some val' /\
     (forall (us : hlist typD tus0) (vs' : hlist typD tvs')
        (vs : hlist typD tvs0),
      val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.

  Hypothesis instantiate_mentionsU : instantiate_mentionsU _ _ instantiate.

  Lemma lemmaD'_convert
  : forall tyProp concl lem F G H tus tvs P,
      (forall x y z, F x y z = G x y z) ->
      lemmaD' (tyProp := tyProp) (conclusion := concl) Expr_expr F H tus tvs lem = Some P ->
      lemmaD' Expr_expr G H tus tvs lem = Some P.
  Proof.
    clear.
    destruct lem. intros. revert H1. Opaque mapT.
    unfold lemmaD'. simpl.
    match goal with
      | |- match ?X with _ => _ end = _ -> match ?Y with _ => _ end = _ =>
        change Y with X ; generalize X
    end.
    destruct o; try congruence.
    rewrite H0.
    destruct (G tus (vars ++ tvs) concl0); try congruence.
  Qed.

  Theorem APPLY_sound
  : forall lem tacC,
      @lemmaD typ _ expr _ expr (@propD _ _ _ _ _ ) (@typ0 _ _ _ _)
              (fun P => match typ0_cast (F:=Prop) in _ = T return T
                        with
                          | eq_refl => P
                        end)
              nil nil lem ->
      stac_cont_sound tacC ->
      stac_sound (APPLY lem tacC).
  Proof.
    intros. apply stac_sound_stac_sound_old. red. intros.
    unfold APPLY.
    consider (eapplicable vars_to_uvars exprUnify s tus tvs lem g); auto; intros.
    eapply (@eapplicable_sound _ _ _ _ _ Typ0_Prop) in H2; eauto.
    forward_reason.
    red in H. simpl in H.
    consider (pull (length tus) (length (vars lem)) s0); auto; [ ].
    intros.
    match goal with
      | |- match tacC ?A ?B ?C ?D ?E with _ => _ end =>
        specialize (H0 A B C D E)
    end.
    eapply pull_for_instantiate_sound
      with (instantiate := instantiate) (tvs := tvs) in H4; eauto.
    forward_reason.
    { do 3 match goal with
             | |- context [ match ?X with Some _ => _ | None => True end ] =>
               consider X ; [ intros | solve [ intuition forward ] ]
           end.
      unfold propD in H6.
      forward.
      admit. (*
      eapply H8 in H6; clear H8; eauto.
      { forward_reason.
        eapply lemmaD'_weakenU with (tus' := tus) in H; eauto using propD_weakenU.
        specialize (H5 _ H6).
        forward_reason.
        rewrite H5 in *.
        unfold lemmaD' in H. forward.
        assert (exists ZZ,
                  mapT (T:=list) (F:=option) (propD tus tvs)
                       (map
                          (fun e : expr =>
                             instantiate (fun u : nat => lookup u s0) 0
                                         (vars_to_uvars 0 (length tus) e))
                          (premises lem)) = Some ZZ /\
                  forall us vs ls,
                    x (hlist_app us ls) vs ->
                    Forall2 (fun x y =>
                               match typ0_cast nil in _ = T return T with
                                 | eq_refl => x us (hlist_app ls Hnil)
                               end <-> y us vs) l0 ZZ).
        { clear H14 H15 H7.
          rewrite mapT_map.
          unfold propD.
          rewrite <- map_mapT.
          revert H. revert l0.
          induction (premises lem).
          { do 2 rewrite list_mapT_nil. simpl.
            intros. inv_all. subst. eexists; split; eauto. }
          { do 2 rewrite list_mapT_cons. intros.
            forward; inv_all; subst.
            specialize (IHl0 _ eq_refl). forward_reason.
            forward.
            eapply vars_to_uvars_sound with (tvs0 := nil) in H.
            forward_reason.
            assert (substD (tus ++ vars lem ++ nil) tvs s0 =
                    Some match eq_sym (app_nil_r_trans (vars lem)) in _ = T
                               return hlist _ (tus ++ T) -> hlist _ tvs -> Prop
                         with
                           | eq_refl => x
                         end).
            { revert H6. clear.
              destruct (eq_sym (app_nil_r_trans (vars lem))). auto. }
            eapply exprD'_weakenV with (tvs' := tvs) in H; eauto.
            forward_reason. simpl in H.
            pose (pfu := match app_nil_r_trans (vars lem) in _ = T
                               return tus ++ T = tus ++ vars lem ++ nil
                         with
                           | eq_refl => eq_refl
                         end).
            rewrite exprD'_conv with (pfv := eq_refl) (pfu := pfu) in H.
            subst pfu.
            unfold ResType in H. rewrite eq_option_eq in H.
            forward.
            eapply H12 in H.
            forward_reason.
            rewrite H.
            eexists; split; eauto.
            intros.
            simpl. constructor.
            { repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
              rewrite <- (H21 us vs ls); clear H21; auto.
              generalize (H16 us (hlist_app ls Hnil) Hnil); clear H16.
              generalize (H18 (hlist_app us (hlist_app ls Hnil)) Hnil vs); clear H18.
              inv_all. subst.
              clear. simpl.
              intros. rewrite H0; clear H0.
              change_rewrite H; clear H.
              match goal with
                | |- ?X <-> ?Y =>
                  cutrewrite (X = Y); [ reflexivity | ]
              end.
              eapply match_eq_match_eq with (F := fun x => x).
              repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
              f_equal.
              rewrite hlist_app_nil_r.
              clear. revert ls.
              generalize (app_nil_r_trans (vars lem)).
              destruct e. reflexivity. }
            { inv_all. subst. eauto. } } }
        { forward_reason.
          change_rewrite H16 in H7.
          unfold exprD in H8.
          consider (tacC tus tvs s1 hs
                         (map
                            (fun e : expr =>
                               instantiate (fun u : nat => lookup u s0) 0
                                           (vars_to_uvars 0 (length tus) e)) (premises lem))); auto.
          { intros. forward_reason; split; auto.
            forward.
            eapply H20 in H22; eauto. clear H20 H21.
            inv_all; subst.
            specialize (H13 us vs).
            forward_reason. rewrite H9 in H15; clear H9.
            generalize (H17 _ _ _ H15); clear H17.
            generalize(H8 _ _ _ H15); clear H8.
            rewrite join_env_app.
            do 2 rewrite split_env_join_env.
            intros; forward_reason; split; auto.
            forward. inv_all; subst.
            repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
            rewrite <- H20; clear H20.
            eapply H11 with (us' := us) in H10; clear H11.
            rewrite foralls_sem in H10.
            specialize (H10 x0).
            rewrite impls_sem in H10.
            rewrite Forall_map in H10.
            cut (P2 us (hlist_app x0 Hnil)).
            { revert H8 H14. simpl. clear - ExprOk_expr.
              unfold propD. intros; forward.
              inv_all; subst.
              eapply exprD'_weakenV with (tvs' := tvs) in H0; eauto.
              forward_reason.
              rewrite exprD'_conv
                 with (pfu := eq_refl)
                      (pfv := match app_nil_r_trans (vars lem) in _ = T return T ++ tvs = (vars lem ++ nil) ++ tvs
                              with
                                | eq_refl => eq_refl
                              end) in H0.
              unfold ResType in H0.
              specialize (H1 us (hlist_app x0 Hnil) vs).
              repeat first [ rewrite eq_Const_eq in *
                           | rewrite eq_option_eq in *
                           | rewrite eq_Arr_eq in * ].
              change_rewrite H8 in H0.
              inv_all; subst.
              repeat first [ rewrite eq_Const_eq in *
                           | rewrite eq_option_eq in *
                           | rewrite eq_Arr_eq in * ].
              rewrite H1 in H; clear H1.
              revert H; clear.
              rewrite hlist_app_nil_r.
              match goal with
                | |- ?X -> ?Y =>
                  cutrewrite (X = Y); auto
              end.
              eapply match_eq_match_eq with (F := fun x => x).
              f_equal.
              clear.
              generalize (app_nil_r_trans (vars lem)).
              generalize dependent (vars lem).
              intro. generalize dependent (l ++ nil).
              intros; subst. reflexivity. }
            { eapply H10.
              revert H9 H13. clear.
              induction 1.
              { constructor. }
              { inversion 1; subst.
                constructor; auto.
                eapply H. assumption. } } }
          { (** TODO(gmalecha): Abstract this proof **)
            intros. forward_reason; split; auto.
            forward.
            inv_all; subst.
            specialize (H13 us vs).
            eapply H22 in H24; eauto; clear H22 H23; [ ].
            specialize (H11 Hnil us Hnil).
            eapply H11 in H10; clear H11.
            forward_reason. rewrite H9 in H13; clear H9.
            generalize (H17 _ _ _ H13); clear H17.
            generalize(H8 _ _ _ H13); clear H8.
            rewrite join_env_app.
            do 2 rewrite split_env_join_env.
            intros; forward_reason; split; auto.
            forward. inv_all; subst.
            repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
            rewrite <- H17; clear H17.
            rewrite foralls_sem in H10.
            specialize (H10 x0).
            rewrite impls_sem in H10.
            rewrite Forall_map in H10.
            cut (P2 us (hlist_app x0 Hnil)).
            { (** TODO(gmalech): This is definitely abstractable **)
              revert H8 H14. simpl. clear - ExprOk_expr.
              unfold propD. intros; forward.
              inv_all; subst.
              eapply exprD'_weakenV with (tvs' := tvs) in H0; eauto.
              forward_reason.
              rewrite exprD'_conv
                 with (pfu := eq_refl)
                      (pfv := match app_nil_r_trans (vars lem) in _ = T return T ++ tvs = (vars lem ++ nil) ++ tvs
                              with
                                | eq_refl => eq_refl
                              end) in H0.
              unfold ResType in H0.
              specialize (H1 us (hlist_app x0 Hnil) vs).
              repeat first [ rewrite eq_Const_eq in *
                           | rewrite eq_option_eq in *
                           | rewrite eq_Arr_eq in * ].
              change_rewrite H8 in H0.
              inv_all; subst.
              repeat first [ rewrite eq_Const_eq in *
                           | rewrite eq_option_eq in *
                           | rewrite eq_Arr_eq in * ].
              rewrite H1 in H; clear H1.
              revert H; clear.
              rewrite hlist_app_nil_r.
              match goal with
                | |- ?X -> ?Y =>
                  cutrewrite (X = Y); auto
              end.
              eapply match_eq_match_eq with (F := fun x => x).
              f_equal.
              clear.
              generalize (app_nil_r_trans (vars lem)).
              generalize dependent (vars lem).
              intro. generalize dependent (l ++ nil).
              intros; subst. reflexivity. }
            { eapply H10.
              revert H9 H11. clear.
              induction 1.
              { constructor. }
              { inversion 1; subst.
                constructor; auto.
                eapply H. assumption. } } } } }
      { clear - H.
        eexists.
        eapply lemmaD'_convert; [ | eassumption ].
        unfold propD. simpl.
        intros; forward.
        inv_all; subst.
        unfold tyProp.
        destruct (exprD' x y z (typ0 (F:=Prop))).
        unfold ResType. rewrite eq_option_eq. reflexivity.
        unfold ResType. rewrite eq_option_eq. reflexivity. } *) }
  Qed.

End parameterized.