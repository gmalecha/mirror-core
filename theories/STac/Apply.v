Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.
  Variable EqDec_eq_typ : EqDec typ (@eq typ).

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.
  Variable mentionsU : nat -> expr -> bool.

  Section apply.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Let eapplicable :=
      @eapplicable typ expr tyProp subst vars_to_uvars
                   exprUnify.

    (** Think of this like:
     **   apply lem ; [ solve [ tac ] | solve [ tac ] | .. | try solve [ tac ] ]
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

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.
  Variable UnifySound_exprUnify : unify_sound _ exprUnify.

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

  Hypothesis exprD'_instantiate
  : forall tus tvs f e tvs' t eD P,
      @sem_preserves_if _ _ _ Expr_expr tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).

  Hypothesis exprD'_strengthen
  : forall tus tu (e : expr) tvs (t : typ) eD,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ tu :: nil) tvs e t = Some eD ->
      exists eD',
        exprD' tus tvs e t = Some eD' /\
        forall us u vs,
          eD (hlist_app us (Hcons u Hnil)) vs = eD' us vs.

  Hypothesis instantiate_mentionsU
  : forall f n e u,
      mentionsU u (instantiate f n e) = true <->
      (   (f u = None /\ mentionsU u e = true)
       \/ exists u' e',
            f u' = Some e' /\
            mentionsU u' e = true/\
            mentionsU u e' = true).

  Hypothesis NormalizedSubst : NormalizedSubstOk mentionsU SubstOk_subst.


  Lemma exprD'_instantiate_substD
  : forall s tus tvs e t P val,
      WellFormed_subst s ->
      substD tus tvs s = Some P ->
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' tus tvs (instantiate (fun u => lookup u s) 0 e) t = Some val' /\
        forall us vs,
          P us vs ->
          val us vs = val' us vs.
  Proof.
    intros.
    eapply exprD'_instantiate
      with (tvs' := nil) (f := fun u => lookup u s) (P:=P)
      in H1.
    { clear - H H0 H1. simpl in *.
      forward_reason. eexists; split; eauto.
      intros. specialize (H2 us vs Hnil).
      apply H2; auto. }
    { red. intros.
      eapply substD_lookup in H2; eauto.
      eapply nth_error_get_hlist_nth_Some in H3.
      simpl in *.
      forward_reason.
      assert (x = t0).
      { clear - x2 x1. rewrite <- x1 in x2.
        inv_all; auto. }
      subst.
      eexists; split; eauto.
      intros. eapply H4 in H5; clear H4.
      rewrite H3.
      rewrite H5.
      clear - EqDec_eq_typ.
      destruct x1.
      rewrite (UIP_refl x2). reflexivity. }
  Qed.

  Lemma mapT_map : forall T U V (f : U -> option V) (g : T -> U) ls,
                     mapT f (map g ls) = mapT (fun x => f (g x)) ls.
  Proof.
    clear. induction ls; try solve [ simpl; auto ].
    simpl map. do 2 rewrite list_mapT_cons.
    destruct (f (g a)); auto.
    rewrite IHls. reflexivity.
  Qed.

  Lemma map_mapT : forall T U V (f : T -> option U) (g : U -> V) ls,
                     match mapT f ls with
                       | None => None
                       | Some x => Some (map g x)
                     end = mapT (fun x => match f x with
                                            | None => None
                                            | Some x => Some (g x)
                                          end) ls.
  Proof.
    clear. induction ls; auto.
    do 2 rewrite list_mapT_cons.
    destruct (f a); auto.
    rewrite <- IHls.
    destruct (mapT f ls); auto.
  Qed.

  Lemma mapT_ext : forall T U (f g : T -> option U),
                     (forall x, f x = g x) ->
                     forall (ls : list T),
                       mapT f ls = mapT g ls.
  Proof.
    clear. induction ls; auto; intros.
    do 2 rewrite list_mapT_cons.
    rewrite H. rewrite IHls. destruct (g a); auto.
  Qed.

  Lemma join_env_app
  : forall ts a b (ax : hlist _ a) (bx : hlist _ b),
      join_env ax ++ join_env (ts := ts) bx = join_env (hlist_app ax bx).
  Proof.
    clear.
    induction ax; simpl; intros; auto.
    f_equal. auto.
  Qed.

  Lemma Forall_map
  : forall T U (f : T -> U) P ls,
      Forall P (List.map f ls) <-> Forall (fun x => P (f x)) ls.
  Proof.
    induction ls; simpl.
    { split; intros; constructor. }
    { split; inversion 1; intros; subst; constructor; auto.
      apply IHls. auto. apply IHls. auto. }
  Qed.

  Let provable P :=
    match typ0_cast nil in _ = T return T with
      | eq_refl => P
    end.

  Lemma lemmaD'_convert
  : forall tyProp concl lem F G H tus tvs P,
      (forall x y z, F x y z = G x y z) ->
      lemmaD' (tyProp := tyProp) (conclusion := concl) Expr_expr F H tus tvs lem = Some P ->
      lemmaD' Expr_expr G H tus tvs lem = Some P.
  Proof.
    clear.
    destruct lem. intros. revert H1. Opaque mapT.
    unfold lemmaD'. simpl.
    unfold goalD. unfold ResType.
    repeat rewrite eq_option_eq.
    match goal with
      | |- match ?X with _ => _ end = _ -> match ?Y with _ => _ end = _ =>
        change Y with X ; generalize X
    end.
    destruct o; try congruence.
    rewrite H0.
    destruct (G tus (vars ++ tvs) concl0); try congruence.
  Qed.

  Lemma goalD_weakenU
  : forall (tus0 tvs0 : tenv typ) (l0 : expr)
           (lD : hlist (typD nil) tus0 -> hlist (typD nil) tvs0 -> Prop),
      goalD tus0 tvs0 l0 = Some lD ->
      forall tus' : list typ,
      exists
        lD' : hlist (typD nil) (tus0 ++ tus') -> hlist (typD nil) tvs0 -> Prop,
        goalD (tus0 ++ tus') tvs0 l0 = Some lD' /\
        (forall (us : hlist (typD nil) tus0) (us' : hlist (typD nil) tus')
                (vs : hlist (typD nil) tvs0), lD us vs <-> lD' (hlist_app us us') vs).
  Proof.
    unfold goalD. clear - ExprOk_expr.
    intros. forward. inv_all; subst.
    eapply exprD'_weakenU with (tus' := tus') in H; eauto.
    forward_reason. rewrite H.
    eexists; split; eauto. intros.
    repeat first [ rewrite eq_Const_eq in *
                 | rewrite eq_option_eq in *
                 | rewrite eq_Arr_eq in * ].
    rewrite <- H0.
    reflexivity.
  Qed.

  Theorem APPLY_sound
  : forall lem tacC,
      @lemmaD typ _ expr _ expr (@goalD _ _ _ _ _ ) (@typ0 _ _ _ _)
              (fun P => match typ0_cast nil in _ = T return T
                        with
                          | eq_refl => P
                        end)
              nil nil lem ->
      stac_cont_sound tacC ->
      stac_sound (APPLY _ _ lem tacC).
  Proof.
    intros. red. intros.
    unfold APPLY.
    consider (eapplicable tyProp vars_to_uvars exprUnify s tus tvs lem g); auto; intros.
    eapply (@eapplicable_sound _ _ _ _ _ tyProp (@typ0_cast _ _ _ _)) in H2; eauto.
    forward_reason.
    red in H. simpl in H.
    consider (pull (length tus) (length (vars lem)) s0); auto; [ ].
    intros.
    match goal with
      | |- match tacC ?A ?B ?C ?D ?E with _ => _ end =>
        specialize (H0 A B C D E)
    end.
    eapply pull_for_instantiate_sound
      with (instantiate := instantiate) (mentionsU := mentionsU)
           (tvs := tvs) in H4; eauto.
    forward_reason.
    { do 3 match goal with
             | |- context [ match ?X with Some _ => _ | None => True end ] =>
               consider X ; [ intros | solve [ intuition forward ] ]
           end.
      unfold goalD in H6.
      forward.
      eapply H8 in H6; clear H8; eauto.
      { forward_reason.
        eapply lemmaD'_weakenU with (tus' := tus) in H; eauto using goalD_weakenU.
        specialize (H5 _ H6).
        forward_reason.
        rewrite H5 in *.
        unfold lemmaD' in H. forward.
        assert (exists ZZ,
                  mapT (T:=list) (F:=option) (goalD tus tvs)
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
          unfold goalD.
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
              unfold goalD. intros; forward.
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
              unfold goalD. intros; forward.
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
        eapply lemmaD'_convert; [ | eassumption ].
        unfold goalD. simpl.
        intros; forward.
        inv_all; subst.
        unfold tyProp.
        destruct (exprD' x y z (typ0 (F:=Prop))).
        unfold ResType. rewrite eq_option_eq. reflexivity.
        unfold ResType. rewrite eq_option_eq. reflexivity. } }
  Qed.

End parameterized.