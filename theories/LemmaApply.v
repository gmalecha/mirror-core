Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.Lemma.

Set Implicit Arguments.
Set Strict Implicit.

Section lemma_apply.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable expr : Type.
  Variable Expr_expr : Expr _ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.
  Variable subst : Type.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : SubstOk _ Subst_subst.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable unify : tenv (ctyp typ) -> tenv  typ -> expr -> expr -> typ -> subst -> option subst.

  Definition unify_sound : Prop :=
    forall tu tv e1 e2 s s' t tv',
      unify tu (tv' ++ tv) e1 e2 t s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) e1 t = Some v1 ->
        exprD' tu (tv' ++ tv) e2 t = Some v2 ->
        substD tu s = Some sD ->
        exists sD',
             substD tu s' = Some sD'
          /\ forall us,
               sD' us ->
               sD us /\
               forall vs vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs).

  Hypothesis Hunify : unify_sound.

  Definition eapplicable (s : subst) tus (tvs : EnvI.tenv typ)
             (lem : lemma typ expr expr) (e : expr)
  : option subst :=
    let pattern := vars_to_uvars 0 (length tus) lem.(concl) in
    unify (tus ++ List.map (mkctyp tvs) lem.(vars)) tvs pattern e tyProp s.

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

  (** This function is really complex! **)
  Fixpoint typs_to_holes (ctx : tenv typ) {ls : tenv typ} (h : hlist typD ls)
  : hlist ctxD (List.map (mkctyp ctx) ls) :=
    match h in hlist _ ls return hlist ctxD (List.map (mkctyp ctx) ls) with
      | Hnil => Hnil
      | Hcons t _ l ls =>
        @Hcons _ ctxD {| cctx := ctx ; vtyp := t |} _ (fun _ => l)
               (typs_to_holes ctx ls)
    end.

  Fixpoint holes_convert (ctx : tenv typ) (ls : tenv typ)
           (h : hlist (fun t => OpenT.OpenT typD ctx (typD t)) ls)
  : hlist ctxD (List.map (mkctyp ctx) ls) :=
    match h in hlist _ ls return hlist ctxD (List.map (mkctyp ctx) ls) with
      | Hnil => Hnil
      | Hcons t _ l ls =>
        @Hcons _ ctxD {| cctx := ctx ; vtyp := t |} _ l (holes_convert ls)
    end.

  Hypothesis vars_to_uvars_exprD'
  : forall (tus : _) (e : expr) (tvs : list typ)
           (t : typ) (tvs' : list typ)
           (val : hlist ctxD tus ->
                  hlist typD (tvs ++ tvs') -> typD t),
      exprD' tus (tvs ++ tvs') e t = Some val ->
      exists
        val' : hlist ctxD (tus ++ List.map (mkctyp tvs) tvs') ->
               hlist typD tvs -> typD t,
        exprD' (tus ++ List.map (mkctyp tvs) tvs') tvs (vars_to_uvars (length tvs) (length tus) e)
               t = Some val' /\
        (forall (us : hlist ctxD tus)
                (vs' : hlist typD tvs') (vs : hlist typD tvs),
           val us (hlist_app vs vs') =
           val' (hlist_app (lr := List.map (mkctyp tvs) tvs')
                           us
                           (typs_to_holes tvs vs')) vs).

(*  Let propD tus tvs g := exprD'_typ0 tus tvs g. *)

  (** TODO: I need a place to put this **)
  Fixpoint hlist_OpenT_const_to_hlist_ctx (tvs ts : list typ)
           (h : hlist (fun t => OpenT.OpenT typD tvs (typD t)) ts)
  : hlist ctxD (List.map (mkctyp tvs) ts) :=
    match h in hlist _ ts return hlist ctxD (List.map (mkctyp tvs) ts) with
      | Hnil => Hnil
      | Hcons _ _ x h =>
        Hcons (l:=mkctyp tvs _) x (hlist_OpenT_const_to_hlist_ctx h)
    end.

  Lemma eapplicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall sD gD,
        (exists lD,
          @lemmaD' _ _ _ _ _ _
                   (exprD'_typ0 Prop)
                   nil nil l0 = Some lD) ->
        substD tus s = Some sD ->
        exprD' tus tvs g tyProp = Some gD ->
        exists s1D gD',
          substD (tus ++ List.map (mkctyp tvs) l0.(vars)) s1 = Some s1D /\
          exprD' tus (l0.(vars) ++ tvs) l0.(concl) tyProp = Some gD' /\
          forall (us : hlist ctxD tus)
                 (us' : hlist (fun t => OpenT.OpenT typD tvs (typD t)) l0.(vars))
                 (vs : hlist typD tvs),
            s1D (hlist_app us (hlist_OpenT_const_to_hlist_ctx us')) ->
               (gD us vs = gD' us (hlist_app (hlist_map (fun t (x : OpenT.OpenT typD tvs (typD t)) => x vs) us') vs))
            /\ sD us.
  Proof.
(*
    unfold eapplicable.
    intros.
    eapply (@Hunify (tus ++ vars l0) tvs _ _ _ _ _ nil) in H; auto.

    forward_reason.
    split; eauto. destruct 1. intros.
    simpl in *.
    unfold lemmaD' in H2. forward. inv_all; subst.
    eapply substD_weakenU with (tus' := vars l0) in H3.
    destruct H3 as [ ? [ ? ? ] ].
    generalize (@exprD'_conv _ _ _ Expr_expr nil nil _ _ (concl l0) tyProp eq_refl (eq_sym (app_nil_r (vars l0)))).
    simpl. intro. unfold propD in H5. rewrite H7 in H5; clear H7.
    clear l H2.
    assert (exprD' nil (vars l0) (concl l0) tyProp =
            Some match eq_sym (typ0_cast (F:=Prop)) in _ = t
                       return _ -> _ -> t
                 with
                   | eq_refl =>
                     match
                       app_nil_r (vars l0) in (_ = tvs')
                       return hlist _ nil -> hlist _ tvs' -> _
                     with
                       | eq_refl => P
                     end
                 end).
    { revert H5; clear. revert P.
      generalize (exprD' nil (vars l0) (concl l0) tyProp).
      destruct (app_nil_r (vars l0)).
      simpl in *. intros.
      match goal with
        | _ : match ?X with _ => _ end = _
        |- _ = Some match eq_sym ?Y with _ => _ end =>
          change Y with X; generalize dependent X
      end.
      intro.
      unfold ResType. rewrite eq_option_eq.
      forward. subst. inv_all; subst.
      clear. destruct e. reflexivity. }
    clear H5.
    change (vars l0) with (nil ++ vars l0) in H2.
    eapply (@exprD'_weakenU _ _ _ Expr_expr) with (tus' := tus) (t := tyProp) in H2; eauto with typeclass_instances.
    destruct H2 as [ ? [ ? ? ] ].
    generalize H2.
    simpl ExprI.exprD' in H2.
    eapply (@vars_to_uvars_exprD' tus (concl l0) nil tyProp) in H2.
    destruct H2 as [ ? [ ? ? ] ].
    eapply (@exprD'_weakenV _ _ _ Expr_expr) with (tvs' := tvs) (t := tyProp) in H2; eauto with typeclass_instances.
    destruct H2 as [ ? [ ? ? ] ].
    simpl in *.
    destruct (@exprD'_weakenU _ _ _ Expr_expr _ tus (vars l0) tvs _ tyProp _ H4) as [ ? [ ? ? ] ]; clear H4.
    progress fill_holes.
    unfold exprD. rewrite split_env_app. repeat rewrite split_env_join_env.
    simpl.
    eapply (@ExprI.exprD'_weakenV _ _ _ Expr_expr) with (t := tyProp) (tvs' := tvs) in H4; eauto with typeclass_instances.
    destruct H4 as [ ? [ ? ? ] ].
    simpl in *. rewrite H4.
    split.
    { f_equal. rewrite <- H14; clear H14.
      repeat match goal with
               | [ H : forall x, _ , H' : hlist _ _ |- _ ] =>
                 specialize (H H') || specialize (H Hnil)
             end.
      specialize (H8 (hlist_app us us') Hnil vs).
      simpl in *. rewrite H7; clear H7.
      etransitivity; [ eapply H8 | clear H8 ].
      rewrite H10; clear H10.
      eassumption. }
    { eapply H6. eapply H11. }
  Qed.
*)
  Admitted.

  Variable substitute_all : (nat -> option expr) -> nat -> expr -> expr.

  (** NOTE: Will I ever do partial evaluation? **)
  Definition apply_lemma (lem : lemma typ expr expr) (es : list expr)
  : option (list expr * expr) :=
    let subst := substitute_all (nth_error es) 0 in
    Some (map subst lem.(premises), subst lem.(concl)).

  Theorem apply_lemma_sound
  : forall (lem : lemma typ expr expr) (es : list expr) tus tvs l_prem l_conc lD,
      Forall2 (fun t e => exprD' tus tvs e t = None -> False) (lem.(vars)) es ->
      @lemmaD' _ _ _ _ _ _
               (exprD'_typ0 Prop) tus tvs lem = Some lD ->
      apply_lemma lem es = Some (l_prem, l_conc) ->
      exists lpD lcD,
        mapT (F:=option)(T:=list) (exprD'_typ0 Prop tus tvs) l_prem = Some lpD /\
        exprD'_typ0 Prop tus tvs l_conc = Some lcD /\
        forall us vs,
          lD us vs ->
          (   Forall (fun x => x us vs) lpD
           -> lcD us vs).
  Proof.
  Admitted.

End lemma_apply.

Arguments typs_to_holes {typ _} ctx {ls} _ : rename.