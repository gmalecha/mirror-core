Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section solve_but_last.
    Variable Subst_subst : Subst subst expr.
    Variables tus tvs : list typ.
    Variable tac : stac typ expr subst.

    Fixpoint solve_all_but_last
             (es : list expr)
             (sub : subst) {struct es}
    : Result typ expr subst :=
      match es with
        | nil => @Solved _ _ _ nil nil sub
        | e :: es =>
          let e := instantiate (fun u => lookup u sub) 0 e in
          match tac tus tvs sub e with
            | Solved nil nil sub' =>
              solve_all_but_last es sub'
            | More tus tvs sub e =>
              match es with
                | nil => More tus tvs sub e
                | _ => @Fail _ _ _
              end
            | _ => @Fail _ _ _
          end
      end.

  End solve_but_last.

  Section eapply_other.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Definition fuel := 100.
    Let eapplicable :=
      @eapplicable typ expr tyProp subst vars_to_uvars
                   exprUnify.

    (** This of this like:
     **   eapply lem ; [ solve [ tac ] | solve [ tac ] | .. | try solve [ tac ] ]
     ** i.e. first eapply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition eapply_other
               (lem : lemma typ expr expr)
               (tac : stac typ expr subst)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun tus tvs sub e =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let len_uvars := length tus in
          let premises := map (vars_to_uvars 0 len_uvars) lem.(premises) in
          match
            solve_all_but_last _ (tus ++ lem.(vars)) tvs tac
                               premises sub'
          with
            | Fail => @Fail _ _ _
            | Solved tus' tvs' sub'' =>
              match pull (expr := expr) len_uvars len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => @Solved _ _ _ nil nil sub'''
              end
            | More tus tvs sub'' e =>
              (** TODO: In this case it is not necessary to pull everything
               ** I could leave unification variables in place
               **)
              match pull (expr := expr) len_uvars len_vars sub'' with
                | None => @Fail _ _ _
                | Some sub''' => More (firstn len_uvars tus) tvs sub''' e
              end
          end
      end.
  End eapply_other.

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
    intros. eapply exprD'_instantiate in H1; eauto.
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

  Theorem solve_all_but_last_sound
  : forall tus tvs (tac : stac typ expr subst) (prems : list expr) (sub : subst),
      stac_sound tac ->
      WellFormed_subst sub ->
      match solve_all_but_last _ tus tvs tac prems sub with
        | Fail => True
        | Solved tus' tvs' s' =>
          WellFormed_subst s' /\
          match mapT (F := option) (T := list) (goalD Expr_expr Typ0_Prop tus tvs) prems with
            | Some Gs =>
              match substD tus tvs sub with
                | Some sV =>
                  match substD (tus ++ tus') (tvs ++ tvs') s' with
                    | Some s'V =>
                      forall (us : hlist (typD nil) tus)
                             (vs : hlist (typD nil) tvs),
                        (exists
                            (us' : hlist (typD nil) tus')
                            (vs' : hlist (typD nil) tvs'),
                            s'V (hlist_app us us') (hlist_app vs vs')) ->
                        Forall (fun G => G us vs) Gs /\ sV us vs
                    | None => False
                  end
                | None => True
              end
            | None => True
          end
        | More tus' tvs' s' g' =>
          WellFormed_subst s' /\
          match mapT (F := option) (T := list) (goalD Expr_expr Typ0_Prop tus tvs) prems with
            | Some Gs =>
              match substD tus tvs sub with
                | Some sV =>
                  match goalD Expr_expr Typ0_Prop (tus ++ tus') (tvs ++ tvs') g' with
                    | Some G' =>
                      match substD (tus ++ tus') (tvs ++ tvs') s' with
                        | Some s'V =>
                          forall (us : hlist (typD nil) tus)
                                 (vs : hlist (typD nil) tvs),
                            (exists
                                (us' : hlist (typD nil) tus')
                                (vs' : hlist (typD nil) tvs'),
                                s'V (hlist_app us us') (hlist_app vs vs') /\
                                G' (hlist_app us us') (hlist_app vs vs')) ->
                            Forall (fun G => G us vs) Gs /\ sV us vs
                        | None => False
                      end
                    | None => False
                  end
                | None => True
              end
            | None => True
          end
      end.
  Proof.
    Opaque mapT.
    intros. generalize dependent sub.
    induction prems.
    { simpl. forward.
      rewrite list_mapT_nil in H0.
      split; auto.
      inv_all; subst.
      repeat match goal with
               | |- match ?X with _ => _ end =>
                 consider X; intros; auto
             end.
      { split. constructor.
        destruct H3 as [ ? [ ? ? ] ].
        rewrite (hlist_eta x) in *.
        rewrite (hlist_eta x0) in *.
        do 2 rewrite hlist_app_nil_r in H3.
        destruct (eq_sym (app_nil_r_trans tus)).
        destruct (eq_sym (app_nil_r_trans tvs)).
        rewrite H0 in H2. inv_all. subst. assumption. }
      { destruct (eq_sym (app_nil_r_trans tus)).
        destruct (eq_sym (app_nil_r_trans tvs)). congruence. } }
    { intros.
      simpl.
      specialize (H tus tvs sub (instantiate (fun u : nat => lookup u sub) 0 a)).
      destruct (tac tus tvs sub (instantiate (fun u : nat => lookup u sub) 0 a)); auto.
      { forward; subst.
        forward_reason.
        specialize (IHprems _ H).
        destruct (solve_all_but_last Subst_subst tus tvs tac prems s); auto.
        { forward_reason.
          split; auto.
          rewrite list_mapT_cons.
          unfold goalD in *.
          forward. inv_all; subst.
          eapply exprD'_instantiate_substD with (s := sub) in H4; eauto.
          { forward_reason.
            rewrite H4 in *.
            forward.
            consider (substD tus tvs s); intros.
            { forward.
              specialize (H9 us vs).
              destruct H9.
              { do 2 exists Hnil. revert H7.
                eapply H10 in H11.
                revert H5. destruct H11.
                revert H7.
                clear.
                do 2 rewrite hlist_app_nil_r.
                destruct (eq_sym (app_nil_r_trans tus)).
                destruct (eq_sym (app_nil_r_trans tvs)).
                intros. rewrite H5 in *. inv_all; subst; auto. }
              { split; auto.
                constructor.
                { repeat rewrite eq_Arr_eq in *. repeat rewrite eq_Const_eq in *.
                  rewrite H6; eauto. }
                { eapply H10 in H11. forward_reason. assumption. } } }
            { clear - H5 H7.
              exfalso.
              destruct (eq_sym (app_nil_r_trans tus)).
              destruct (eq_sym (app_nil_r_trans tvs)). congruence. } } }
        { rewrite list_mapT_cons.
          forward_reason.
          split; eauto.
          unfold goalD in *.
          forward.
          inv_all; subst.
          eapply exprD'_instantiate_substD with (s := sub) in H4; eauto.
          forward_reason.
          rewrite H4 in *.
          forward.
          consider (substD tus tvs s).
          { intros; forward.
            inv_all; subst.
            eapply H11 in H12; clear H11.
            specialize (H9 us vs).
            destruct H12.
            destruct H9.
            { do 2 exists Hnil.
              do 2 rewrite hlist_app_nil_r.
              destruct (eq_sym (app_nil_r_trans tus)).
              destruct (eq_sym (app_nil_r_trans tvs)).
              rewrite H7 in *. inv_all; subst. assumption. }
            { split; auto.
              constructor; auto.
              revert H9.
              repeat rewrite eq_Arr_eq.
              repeat rewrite eq_Const_eq.
              rewrite H6; auto. } }
          { intro; exfalso.
            revert H7 H5. clear.
            destruct (eq_sym (app_nil_r_trans tus)).
            destruct (eq_sym (app_nil_r_trans tvs)). congruence. } } }
      { destruct prems; auto.
        destruct H; auto.
        split; auto.
        rewrite list_mapT_cons. rewrite list_mapT_nil.
        clear IHprems.
        unfold goalD in *.
        forward.
        inv_all; subst.
        eapply exprD'_instantiate_substD with (s := sub) in H2; eauto.
        { forward_reason.
          rewrite H2 in *.
          forward. inv_all; subst.
          forward_reason.
          specialize (H6 us vs). destruct H6.
          { exists x0; exists x1.
            split; auto. }
          { split; auto.
            constructor; auto.
            revert H6.
            repeat rewrite eq_Arr_eq.
            repeat rewrite eq_Const_eq.
            rewrite H3; auto. } } } }
    Transparent mapT.
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

  Lemma join_env_app : forall ts a b (ax : hlist _ a) (bx : hlist _ b),
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

  Theorem APPLY_sound
  : forall lem tac,
      @lemmaD typ _ expr _ expr (@goalD _ _ _ _ _ ) (@typ0 _ _ _ _)
              (fun P => match typ0_cast nil in _ = T return T
                        with
                          | eq_refl => P
                        end)
              nil nil lem ->
      stac_sound tac ->
      stac_sound (eapply_other _ _ lem tac).
  Proof.
(*
    intros. red. intros.
    unfold eapply_other.
    consider (eapplicable tyProp vars_to_uvars exprUnify s tus tvs lem g); auto; intros.
    eapply (@eapplicable_sound _ _ _ _ _ tyProp (@typ0_cast _ _ _ _)) in H1; eauto.
    destruct H1.
    red in H. simpl in H. forward.
    generalize (@solve_all_but_last_sound (tus ++ vars lem) tvs tac
                                          (map (vars_to_uvars 0 (length tus)) (premises lem))
                                          s0 H0 H1).
    match goal with
      | |- match ?X with _ => _ end -> match match ?Y with _ => _ end with _ => _ end =>
        change Y with X; consider X; intros
    end; auto.
    { forward_reason. forward.
      eapply pull_sound in H8; eauto.
      forward_reason. split; auto.
      forward.
      assert (lemmaD' Expr_expr
                        (fun (tus0 tvs0 : tenv typ) (g0 : expr) =>
                           match typ0_cast nil in (_ = t) return (ResType tus0 tvs0 t) with
                             | eq_refl => exprD' tus0 tvs0 g0 tyProp
                           end)
                        (fun x : typD nil tyProp =>
                           match typ0_cast nil in (_ = t) return t with
                             | eq_refl => x
                           end) nil nil lem = Some P).
      { clear - H.
        unfold lemmaD', goalD in *.
        match goal with
          | H : match ?X with _ => _ end = _ |- match ?Y with _ => _ end = _ =>
            change Y with X; consider X; try congruence; intros
        end.
        unfold ResType.
        rewrite eq_option_eq.
        eauto. }
      unfold goalD in *. forward. inv_all; subst.
      eapply H11 in H12; clear H11; eauto.
      forward_reason.
      rewrite H11 in *.
      unfold lemmaD' in H. forward. inv_all; subst.
      specialize (fun Z Z' => H9 _ _ Z Z' eq_refl eq_refl).
      assert (exists ZZ,
        mapT
          (fun goal : expr =>
             match exprD' (Expr := Expr_expr) (tus ++ vars lem) tvs goal (typ0 (F:=Prop)) with
               | Some val =>
                 Some
                   match
                     typ0_cast nil in (_ = T)
                     return
                     (hlist (typD nil) (tus ++ vars lem) ->
                      hlist (typD nil) tvs -> T)
                   with
                     | eq_refl => val
                   end
               | None => None
             end) (map (vars_to_uvars 0 (length tus)) (premises lem)) = Some ZZ /\
        forall us vs ls,
          x (hlist_app us ls) vs ->
          Forall2 (fun x y =>
                     match typ0_cast nil in _ = T return T with
                       | eq_refl => x Hnil (hlist_app ls Hnil)
                     end <-> y (hlist_app us ls) vs) l1 ZZ).
      { admit. (*clear H7 H5 H9.
        generalize dependent l1.
        induction (premises lem).
        { simpl. intros. inv_all; subst.
          eexists; split; eauto. }
        { Opaque mapT. clear l.
          simpl. do 2 rewrite list_mapT_cons.
          intros. forward. inv_all; subst.
          specialize (IHl1 _ eq_refl).
          forward_reason.
          rewrite H6; clear H6.
          eapply exprD'_weakenU with (tus' := tus) in H; eauto. simpl in H.
          destruct H as [ ? [ ? ? ] ].
          eapply vars_to_uvars_sound with (tvs0 := nil) (tus0 := tus) in H.
          forward_reason.
          eapply exprD'_weakenV with (tvs' := tvs) in H; eauto. simpl in H.
          destruct H as [ ? [ ? ? ] ].
          consider (exprD' (tus ++ vars lem) tvs (vars_to_uvars 0 (length tus) a)
                           (typ0 (F:=Prop))).
          { intros. eexists; split; eauto.
            intros. admit. }
          { intros. exfalso.
            clear - H H15.
            assert (tus ++ vars lem ++ nil = tus ++ vars lem).
            { rewrite app_nil_r. reflexivity. }
            rewrite <- H0 in H15. congruence. } } *) }
      { destruct H14 as [ ? [ ? ? ] ].
        match goal with
          | H : ?X = _ , H' : match ?Y with _ => _ end |- _ =>
            change Y with X in H' ; rewrite H in H'
        end.
        forward.
        assert (l = nil /\ l0 = nil).
        { admit. }
        admit. } }
    { forward. forward_reason.
      eapply pull_sound in H7; eauto.
      forward_reason.
      split; auto. unfold goalD in *.
      forward. inv_all; subst.
      assert (lemmaD' Expr_expr
                        (fun (tus0 tvs0 : tenv typ) (g0 : expr) =>
                           match typ0_cast nil in (_ = t) return (ResType tus0 tvs0 t) with
                             | eq_refl => exprD' tus0 tvs0 g0 tyProp
                           end)
                        (fun x : typD nil tyProp =>
                           match typ0_cast nil in (_ = t) return t with
                             | eq_refl => x
                           end) nil nil lem = Some P).
      { clear - H.
        unfold lemmaD', goalD in *.
        match goal with
          | H : match ?X with _ => _ end = _ |- match ?Y with _ => _ end = _ =>
            change Y with X; consider X; try congruence; intros
        end.
        unfold ResType.
        rewrite eq_option_eq.
        eauto. }
      eapply H12 in H11; eauto; clear H12.
      forward_reason.
      rewrite H11 in *; clear H11.
      unfold lemmaD' in H. forward.
      inv_all; subst.
      assert (exists ZZ,
        mapT
          (fun goal : expr =>
             match exprD' (Expr := Expr_expr) (tus ++ vars lem) tvs goal (typ0 (F:=Prop)) with
               | Some val =>
                 Some
                   match
                     typ0_cast nil in (_ = T)
                     return
                     (hlist (typD nil) (tus ++ vars lem) ->
                      hlist (typD nil) tvs -> T)
                   with
                     | eq_refl => val
                   end
               | None => None
             end) (map (vars_to_uvars 0 (length tus)) (premises lem)) = Some ZZ /\
        forall us vs ls,
          x (hlist_app us ls) vs ->
          Forall2 (fun x y =>
                     match typ0_cast nil in _ = T return T with
                       | eq_refl => x Hnil (hlist_app ls Hnil)
                     end <-> y (hlist_app us ls) vs) l1 ZZ).
      { admit. }
      forward_reason.
      match goal with
        | H : ?X = _ , H' : match ?Y with _ => _ end |- _ =>
          change Y with X in H' ; rewrite H in H' ; clear H
      end.
      forward. inv_all; subst.

           
          
        
        
      
                
      



split; auto.
        red in H. simpl in H. forward.
        assert (lemmaD' Expr_expr
                        (fun (tus0 tvs0 : tenv typ) (g0 : expr) =>
                           match typ0_cast nil in (_ = t) return (ResType tus0 tvs0 t) with
                             | eq_refl => exprD' tus0 tvs0 g0 tyProp
                           end)
                        (fun x : typD nil tyProp =>
                           match typ0_cast nil in (_ = t) return t with
                             | eq_refl => x
                           end) nil nil lem = Some P).
        { clear - H.
          unfold lemmaD', goalD in *.
          match goal with
            | H : match ?X with _ => _ end = _ |- match ?Y with _ => _ end = _ =>
              change Y with X; consider X; try congruence; intros
          end.
          unfold ResType.
          rewrite eq_option_eq.
          eauto. }
        clear H.
        unfold goalD in *. forward.
        specialize (H11 _ _ _ H12 eq_refl H).
        forward_reason.
        inv_all; subst.
        unfold lemmaD' in H12. forward. inv_all; subst.
        specialize (@H5 _ _ _ _ eq_refl eq_refl H11).
        forward_reason.
        rewrite <- map_mapT in H8.
        rewrite mapT_map in H8.
        assert (exists zz,
                  mapT (T := list) (F := option)
                       (fun x : expr =>
                          exprD' tus tvs
                                 (instantiate (fun u : nat => lookup u s0) 0
                                              (vars_to_uvars 0 (length tus) x))
                                 (typ0 (F:=Prop))) (premises lem) = Some zz /\
                  forall us vs,
                    P1 us vs ->
                    Forall2 (fun a b =>
                       match typ0_cast (F := Prop) nil in _ = T return T with
                         | eq_refl =>
                           a Hnil (hlist_app (hlist_map (fun t (x : hlist _ tus -> hlist _ tvs -> typD nil t) => x us vs) x2) Hnil)
                       end <->
                       match typ0_cast nil in _ = T return T with
                         | eq_refl => b us vs
                       end) l1 zz).
          { clear H9 H8 H6.
            revert H10. revert l1.
            induction (premises lem).
            { simpl. eexists; split; eauto.
              simpl in H10. inv_all; subst. intros. constructor. }
            { intros.
              rewrite list_mapT_cons in H10.
              rewrite list_mapT_cons.
              forward. inv_all. subst.
              eapply exprD'_weakenU with (tus' := tus) in H6; eauto.
              simpl in H6.
              destruct H6 as [ ? [ ? ? ] ].
              eapply vars_to_uvars_sound with (tvs0 := nil) in H6.
              specialize (IHl1 _ eq_refl).
              forward_reason. rewrite H10.
              eapply exprD'_weakenV with (tvs' := tvs) in H6; eauto.
              forward_reason. simpl in *.
              assert (exists Z,
                        substD (tus ++ vars lem ++ nil) tvs s0 = Some Z /\
                        forall A B C,
                          Z (hlist_app A (hlist_app B Hnil)) C <-> x (hlist_app A B) C).
              { clear - H11.
                exists (match eq_sym (app_nil_r_trans (vars lem)) in _ = T return hlist _ (tus ++ T) -> _ with
                          | eq_refl => x
                        end).
                split.
                { destruct (eq_sym (app_nil_r_trans (vars lem))). auto. }
                { intros.
                  repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
                  rewrite hlist_app_nil_r.
                  generalize (app_nil_r_trans (vars lem)).
                  generalize dependent (vars lem).
                  intros. generalize dependent (l ++ nil). intros. subst.
                  reflexivity. } }
              destruct H19 as [ ? [ ? ? ] ].
              eapply exprD'_instantiate_substD with (s := s0) in H6; eauto.
              destruct H6 as [ ? [ ? ? ] ].
              



} }


        eapply lemmaD'_weaken with (tus' := tus) (tvs' := tvs) in H12; eauto.
        { simpl in H12.
          forward_reason.
          unfold lemmaD' in H10. forward. inv_all; subst.
          rewrite <- map_mapT in H8.
          rewrite mapT_map in H8.

          forward_reason.
          rewrite H5 in *.
          destruct H17 as [ ? [ ? ? ] ].
          rewrite H17 in *.
          forward.
          specialize (H19 _ _ H20).
          specialize (H16 us vs).
          specialize (H13 us (HList.hlist_map (fun t (x : hlist _ tus -> hlist _ tvs -> typD nil t) => x us vs) x2) vs).
          specialize (H12 Hnil us Hnil vs).
          specialize (H18 us vs).
          forward_reason.
          split; auto.
          revert H13 H14.
          unfold exprD.
          rewrite split_env_join_env.
          rewrite join_env_app. rewrite split_env_join_env.
          generalize (exprD' tus (vars lem ++ tvs) (concl lem) tyProp).
          intros; forward.
          subst.
          unfold ResType in H23. rewrite eq_option_eq in H23.
          inv_all; subst.
          do 2 rewrite eq_Arr_eq. do 2 rewrite eq_Const_eq.
          rewrite <- H14; clear H14.
          eapply H12 in H9; clear H12.
          rewrite foralls_sem in H9.
          specialize (H9 (HList.hlist_map (fun t (x : hlist _ tus -> hlist _ tvs -> typD nil t) => x us vs) x2)).
          eapply impls_sem in H9.
          { revert H9.
            do 2 rewrite eq_Arr_eq. do 2 rewrite eq_Const_eq.
            simpl. auto. }
          { revert H19.
            repeat rewrite Forall_map. simpl.
            revert H18. clear. induction 1.
            { intros. constructor. }
            { intros.
              inversion H0; subst.
              constructor; eauto.
              { revert H3. revert H.
                clear.
                repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
                match goal with
                  | |- (match ?X with eq_refl => ?T end <-> match ?Y with eq_refl => ?U end) -> 
                       match ?Z with eq_refl => ?V end ->
                       match ?A with eq_refl => ?W end =>
                    change Y with X ; change Z with X ; change A with X ; generalize X ;
                    change T with W ; generalize W ;
                    change U with V ; generalize V
                end.
                clear.
                match goal with
                  | |- forall (x : ?Z) (y : _) (pf : ?W = _), _ =>
                    change W with Z ; generalize Z
                end.
                intros; subst. intuition. } } } }
        { clear - ExprOk_expr.
          intros.
          unfold ResType in H. rewrite eq_option_eq in H. forward.
          inv_all. subst.
          destruct (@exprD'_weakenU _ _ _ _ ExprOk_expr tus tus' tvs l tyProp _ H).
          unfold ResType. rewrite eq_option_eq.
          destruct H0. rewrite H0. eexists; split; eauto.
          intros.
          repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          rewrite <- H1. reflexivity. }
        { clear - ExprOk_expr.
          intros.
          unfold ResType in H. rewrite eq_option_eq in H. forward.
          inv_all. subst.
          destruct (@exprD'_weakenV _ _ _ _ ExprOk_expr tus tvs tvs' l tyProp _ H).
          unfold ResType. rewrite eq_option_eq.
          destruct H0. rewrite H0. eexists; split; eauto.
          intros.
          repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          rewrite <- H1. reflexivity. } }
      { admit. (** Big **) } }
    { generalize (@solve_all_but_last_sound (tus ++ vars lem) tvs tac
                                            (map (vars_to_uvars 0 (length tus)) (premises lem))
                                            s0 H0 H1).
      match goal with
        | |- match ?X with _ => _ end -> match match ?Y with _ => _ end with _ => _ end =>
          change Y with X; consider X; intros
      end; auto.
      { admit. (** Big **) }
      { forward.
        destruct H6.
        eapply pull_sound in H7; eauto. destruct H7.
        split; auto.
        red in H. simpl in H.
        forward.
        unfold goalD in *. forward.
        inv_all. subst.
        subst tyProp.
        assert (lemmaD' Expr_expr
                        (fun (tus0 tvs0 : tenv typ) (g0 : expr) =>
                           match typ0_cast nil in (_ = t) return (ResType tus0 tvs0 t) with
                             | eq_refl => exprD' tus0 tvs0 g0 (typ0 (F:=Prop))
                           end)
                        (fun x : typD nil (typ0 (F:=Prop)) =>
                           match typ0_cast nil in (_ = t) return t with
                             | eq_refl => x
                           end) nil nil lem = Some P).
        { revert H. clear.
          unfold lemmaD'. forward.
          inv_all; subst.
          unfold ResType.
          rewrite eq_option_eq. reflexivity. }
        clear H.
        specialize (H12 _ _ _ H13 eq_refl H11).
        forward_reason.
        match goal with
          | H : match ?X with _ => _ end |- _ =>
            consider X; intros
        end.
        { admit. }
        { unfold lemmaD' in H13.
          exfalso.
          forward.
          admit. } } }
*)
  Abort.


End parameterized.