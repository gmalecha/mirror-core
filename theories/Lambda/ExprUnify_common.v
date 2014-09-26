Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Util.Forwardy.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable typ : Type.
  Variable func : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk_typ : RTypeOk.
  Variable Typ2_arr : Typ2 _ Fun.
  Variable Typ2Ok_arr : Typ2Ok Typ2_arr.
  Variable RSym_func : RSym func.
  Variable RSymOk_func : RSymOk RSym_func.
  Variable Subst_subst : Subst subst (expr typ func).
  Variable SubstUpdate_subst : SubstUpdate subst (expr typ func).
  Variable SubstOk_subst : SubstOk (Expr_expr) Subst_subst.
  Variable SubstUpdateOk_subst
  : @SubstUpdateOk _ _ _ _ Expr_expr _ SubstUpdate_subst _.
  Local Existing Instance Expr_expr. (* : Expr _ (expr typ func) := Expr_expr. *)
  Variable RelDec_eq_typ : RelDec (@eq typ).
  Variable RelDec_eq_func : RelDec (@eq func).
  Instance RelDec_eq_expr : RelDec (@eq (expr typ func)) := RelDec_eq_expr _ _.

  (** n is the number of binders that we have gone under **)
  Variable exprUnify : forall (tus : tenv (ctyp typ)) (tvs : tenv typ)
                                (l r : expr typ func), typ -> subst -> option subst.

  Fixpoint find (e : expr typ func) (acc : nat) (es : list (expr typ func)) : option nat :=
    match es with
      | nil => None
      | e' :: es' =>
        if e ?[ eq ] e' then Some acc
        else find e (S acc) es'
    end.

  Axiom instantiate : subst -> expr typ func -> expr typ func.

  Fixpoint patterns (es : list (expr typ func)) (s : subst)
           (e : expr typ func) {struct e}
  : option (expr typ func).
    refine
      match e with
        | Inj i => Some (Inj i)
        | UVar u es' =>
          match mapT_list (F:=option) (patterns es s) es' with
            | None => None (** I could do something here **)
            | Some es'' => Some (UVar u es'')
          end
        | App e1 e2 =>
          match patterns es s e1
                , patterns es s e2 with
            | Some e1' , Some e2' => Some (App e1' e2')
            | _ , _ => None
          end
        | _ =>
          (** This is the only case that I expect to happen **)
          match find e 0 es with
            | None => None
            | Some v' => Some (Var v')
          end
      end.
  Defined.

  Definition try_set
             (u : uvar) (args1 : list (expr typ func))
             (e2 : expr typ func)
             (s : subst) : option subst :=
    match patterns args1 s e2 with
      | None => None
      | Some e => set u e s
    end.

  Fixpoint fold_left3 {A B C} (f : C -> A -> A -> B -> option B) (t : list C)
           (x y : list A) (s : B)
  : option B :=
    match t , x , y with
      | nil , nil , nil => Some s
      | t :: ts , x :: xs , y :: ys =>
        match f t x y s with
          | None => None
          | Some s => fold_left3 f ts xs ys s
        end
      | _ , _ , _ => None
    end.



(*
  Lemma handle_set
  : forall (e0 : expr typ func) (u : uvar) (s s' : subst)
    (Hnot_found : lookup u s = None),
      set u e0 s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall (tu : tenv (ctyp typ)) (tv : list typ)
             (t : typ) (tv' : list typ),
        (forall
            (v1 : _)
            (v2 : hlist typD tu ->
                    hlist typD (tv' ++ tv) -> typD t)
            (sD : hlist typD tu -> hlist typD tv -> Prop),
            exprD' tu tv t e0 = Some v1 ->
            exprD' tu (tv' ++ tv) t (UVar u es) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist typD tu -> hlist typD tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist typD tu)
                      (vs : hlist typD tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist typD tv',
                    v1 us vs = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    eapply set_sound in H; eauto.
    forward_reason; split; eauto.
    intros.
    autorewrite with exprD_rw in *; eauto. simpl in *.
    forwardy.
    destruct y.
    specialize (H1 _ _ _ _ _ _ H4 H3 H2).
    forward_reason.
    eexists; split; eauto.
    intros.
    eapply H7 in H8; forward_reason; split; auto.
    intros. rewrite <- H9.
    inv_all; subst. reflexivity.
  Qed.

  Lemma handle_set_lower
  : forall (e0 : expr typ func) (u : uvar) (s s' : subst)
           (Hnot_found : lookup u s = None),
      set u e0 s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall (tu : tenv typ) (tv : list typ)
             (t : typ) (tv' : list typ) (e : expr typ func),
        lower 0 (length tv') e = Some e0 ->
        (forall
            (v1
               v2 : hlist typD tu ->
                    hlist typD (tv' ++ tv) -> typD t)
            (sD : hlist typD tu -> hlist typD tv -> Prop),
            exprD' tu (tv' ++ tv) t e = Some v1 ->
            exprD' tu (tv' ++ tv) t (UVar u) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist typD tu -> hlist typD tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist typD tu)
                      (vs : hlist typD tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist typD tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    eapply set_sound in H; eauto.
    forward_reason; split; eauto.
    intros.
    autorewrite with exprD_rw in *; simpl in *.
    forwardy.
    destruct y. inv_all; subst.
    eapply  (@exprD'_lower typ func _ _ RSym_func _ _ _ tu nil tv' tv) in H2; eauto.
    forward_reason.
    specialize (H1 _ _ _ _ _ _ H5 H4 H2).
    forward_reason.
    eexists; split; eauto.
    intros.
    eapply H8 in H9; clear H8.
    forward_reason; split; eauto.
    rewrite H9. intros. eapply (H7 us Hnil vs' vs).
  Qed.
*)

  Definition unify_sound_ind
    (unify : forall (us : tenv (ctyp typ)) (vs : tenv typ)
                    (l r : expr typ func)
                    (t : typ) (s : subst), option subst) : Prop :=
    forall tu tv e1 e2 s s' t tv',
      unify tu (tv' ++ tv) e1 e2 t s = Some s' ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) t e1 = Some v1 ->
        exprD' tu (tv' ++ tv) t e2 = Some v2 ->
        substD tu s = Some sD ->
        exists sD',
             substD (expr := expr typ func) tu s' = Some sD'
          /\ forall us vs,
               sD' us ->
               sD us /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs).

  Definition unify_sound := unify_sound_ind.
(*
  Lemma handle_uvar
  : forall
      (unify : tenv typ -> tenv typ ->
               nat -> subst -> expr typ func -> expr typ func -> typ -> option subst),
      unify_sound_ind unify ->
      forall (tu : tenv typ) (tv : list typ) e
             (u : uvar) (s s' : subst) (t : typ) (tv' : list typ),
        match lookup u s with
          | Some e2' =>
            unify tu (tv' ++ tv) (length tv') s e
                  (lift 0 (length tv') e2') t
          | None =>
            match lower 0 (length tv') e with
              | Some e1 => set u e1 s
              | None => None
            end
        end = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall
            (v1 v2 : hlist typD tu ->
                     hlist typD (tv' ++ tv) -> typD t)
            (sD : hlist typD tu -> hlist typD tv -> Prop),
            exprD' tu (tv' ++ tv) t e = Some v1 ->
            exprD' tu (tv' ++ tv) t (UVar u) = Some v2 ->
            substD tu tv s = Some sD ->
            exists
              sD' : hlist typD tu -> hlist typD tv -> Prop,
              substD tu tv s' = Some sD' /\
              (forall (us : hlist typD tu) (vs : hlist typD tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist typD tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H2.
      forward_reason.
      split; eauto; intros.
      assert (exists v2',
                exprD' tu (tv' ++ tv) t (lift 0 (length tv') e0) = Some v2'
                /\ forall us vs vs',
                     sD us vs ->
                     v2 us (hlist_app vs' vs) = v2' us (hlist_app vs' vs)).
      { eapply substD_lookup in H0; eauto.
        forward_reason.
        simpl in *.
        autorewrite with exprD_rw in H5; simpl in H5.
        forward. inv_all; subst.
(*        change_rewrite H5 in H9. inv_all; subst. *)
        eapply nth_error_get_hlist_nth_Some in H5.
        simpl in *. forward_reason.
        generalize (@exprD'_lift typ func _ _ _ _ _ _ tu e0 nil tv' tv x2).
        simpl. change_rewrite H7.
        intros; forwardy. destruct r.
        eexists; split; [ eassumption | ].
        intros.
        erewrite H8; try eassumption.
        specialize (H10 us Hnil vs' vs).
        simpl in H10.
        rewrite H10.
        reflexivity. }
      forward_reason.
      specialize (H3 _ _ _ H4 H7 H6).
      forward_reason.
      eexists; split; eauto.
      intros. specialize (H9 _ _ H10).
      forward_reason. split; intros; eauto.
      rewrite H11. rewrite H8; eauto. }
    { forward. eapply handle_set_lower in H3; intuition eauto. }
  Qed.

  Lemma handle_uvar'
  : forall
        unify : tenv typ -> tenv typ ->
                nat -> subst -> expr typ func -> expr typ func -> typ -> option subst,
        unify_sound_ind unify ->
        forall (tu : tenv typ) (tv : list typ) e
               (u : uvar) (s s' : subst) (t : typ) (tv' : list typ),
          match lookup u s with
            | Some e2' =>
              unify tu (tv' ++ tv) (length tv') s
                    (lift 0 (length tv') e2') e t
            | None =>
              match lower 0 (length tv') e with
                | Some e1 => set u e1 s
                | None => None
              end
          end = Some s' ->
          WellFormed_subst s ->
          WellFormed_subst s' /\
          (forall
              (v1 v2 : hlist typD tu ->
                       hlist typD (tv' ++ tv) -> typD t)
              (sD : hlist typD tu -> hlist typD tv -> Prop),
              exprD' tu (tv' ++ tv) t (UVar u) = Some v1 ->
              exprD' tu (tv' ++ tv) t e = Some v2 ->
              substD tu tv s = Some sD ->
              exists
                sD' : hlist typD tu -> hlist typD tv -> Prop,
                substD tu tv s' = Some sD' /\
                (forall (us : hlist typD tu)
                        (vs : hlist typD tv),
                   sD' us vs ->
                   sD us vs /\
                   (forall vs' : hlist typD tv',
                      v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)))).
  Proof.
    intros.
    consider (lookup u s); intros.
    { eapply H in H2.
      forward_reason.
      split; eauto; intros.
      assert (exists v2',
                exprD' tu (tv' ++ tv) t (lift 0 (length tv') e0) = Some v2'
                /\ forall us vs vs',
                     sD us vs ->
                     v1 us (hlist_app vs' vs) = v2' us (hlist_app vs' vs)).
      { eapply substD_lookup in H0; eauto.
        forward_reason.
        simpl in *.
        autorewrite with exprD_rw in H4; simpl in H4.
        forwardy. inv_all; subst.
        change_rewrite H0 in H4.
        inv_all; subst.
        generalize (@exprD'_lift typ func _ _ _ _ _ _ tu e0 nil tv' tv x).
        simpl. change_rewrite H7.
        intros; forwardy.
        destruct y.
        eexists; split; [ eassumption | ].
        intros.
        specialize (H10 us Hnil vs' vs).
        specialize (H8 us vs).
        simpl in *.
        etransitivity; [ clear H10 | exact H10 ].
        apply H8. assumption. }
      forward_reason.
      specialize (H3 _ _ _ H7 H5 H6).
      forward_reason.
      eexists; split; eauto.
      intros. specialize (H9 _ _ H10).
      forward_reason. split; intros; eauto.
      rewrite H8; eauto. }
    { forwardy. eapply handle_set_lower in H3; intuition eauto.
      specialize (H5 _ _ _ _ _ H2 _ _ _ H6 H3 H7).
      forward_reason. eexists; split; eauto.
      intros. specialize (H8 _ _ H9). forward_reason; split; eauto. }
  Qed.

  Lemma lookup_lift
  : forall u s e tu tv tv' t sD v1,
      lookup u s = Some e ->
      WellFormed_subst s ->
      substD tu tv s = Some sD ->
      exprD' tu (tv' ++ tv) t (UVar u) = Some v1 ->
      exists v1',
        exprD' tu (tv' ++ tv) t (lift 0 (length tv') e) = Some v1' /\
        forall us vs vs',
          sD us vs ->
          v1 us (hlist_app vs' vs) = v1' us (hlist_app vs' vs).
  Proof.
    intros.
    eapply substD_lookup in H; eauto.
    simpl in *. forward_reason.
    generalize (@exprD'_lift typ func RType_typ Typ2_arr _ _ _ _
                             tu e nil tv' tv x).
    simpl. change_rewrite H3.
    intros; forwardy.
    autorewrite with exprD_rw in H2. simpl in H2.
    change_rewrite H in H2.
    forwardy.
    inv_all. subst. destruct y0.
    eexists; split; [ eapply H5 | ].
    clear - H4 H6.
    intros.
    specialize (H6 us Hnil vs' vs).
    simpl in *.
    etransitivity; [ eapply H4 | eapply H6 ]; eauto.
  Qed.
*)
End typed.

Arguments try_set {_ _ _ _ _ _} _ _ _ _ : rename.