Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Ltac equivs :=
  repeat match goal with
           | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
         end; subst.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Inductive Ctx :=
  | CTop
  | CAll : Ctx -> typ -> Ctx
  | CExs : Ctx -> list typ -> Ctx
  | CHyp : Ctx -> expr -> Ctx.

  Fixpoint CEx (c : Ctx) (t : typ) : Ctx :=
    CExs c (t :: nil).

  Fixpoint CAlls (c : Ctx) (ls : list typ) : Ctx :=
    match ls with
      | nil => c
      | l :: ls => CAlls (CAll c l) ls
    end.

  (** Auxiliary Functions **)
  Fixpoint countVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CAll ctx' t => S (countVars ctx')
      | CExs ctx' _
      | CHyp ctx' _ => countVars ctx'
    end.

  Fixpoint countUVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CExs ctx' ts => length ts + countUVars ctx'
      | CAll ctx' _
      | CHyp ctx' _ => countUVars ctx'
    end.

  Fixpoint getUVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' _ => getUVars ctx'
      | CExs ctx' ts => getUVars ctx' ++ ts
      | CHyp ctx' _ => getUVars ctx'
    end.

  Fixpoint getVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' t => getVars ctx' ++ t :: nil
      | CExs ctx' _ => getVars ctx'
      | CHyp ctx' _ => getVars ctx'
    end.

  Lemma countVars_getVars : forall ctx, countVars ctx = length (getVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Lemma countUVars_getUVars : forall ctx, countUVars ctx = length (getUVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Fixpoint getEnvs' (ctx : Ctx) (tus tvs : tenv typ)
  : tenv typ * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CExs ctx' ts => getEnvs' ctx' (ts ++ tus) tvs (** TODO: Check **)
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv typ * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Fixpoint Ctx_append (c1 c2 : Ctx) : Ctx :=
    match c2 with
      | CTop => c1
      | CAll ctx' t => CAll (Ctx_append c1 ctx') t
      | CExs ctx' ts => CExs (Ctx_append c1 ctx') ts
      | CHyp ctx' h => CHyp (Ctx_append c1 ctx') h
    end.

  Theorem getUVars_append
  : forall c1 c2,
      getUVars (Ctx_append c1 c2) = getUVars c1 ++ getUVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.

  Theorem getVars_append
  : forall c1 c2,
      getVars (Ctx_append c1 c2) = getVars c1 ++ getVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.
  (** End: Auxiliary Functions **)

  Require Import MirrorCore.Subst.FMapSubst.

  Definition amap : Type := SUBST.raw expr.
  Definition amap_lookup : nat -> amap -> option expr :=
    @UVarMap.MAP.find _.
  Definition amap_check_set : nat -> expr -> amap -> option amap :=
    @SUBST.raw_set _ _ _ _ instantiate.

  Inductive ctx_subst : Ctx -> Type :=
  | TopSubst : ctx_subst CTop
  | AllSubst : forall {t c}, ctx_subst c -> ctx_subst (CAll c t)
  | HypSubst : forall {t c}, ctx_subst c -> ctx_subst (CHyp c t)
  | ExsSubst : forall {ts c}, ctx_subst c -> amap -> ctx_subst (CExs c ts).

  Definition only_in_range (min len : nat) (s : amap) : Prop :=
    forall u e, amap_lookup u s = Some e -> min <= u < min + len.

  (** [tus] and [tvs] are full environments! **)
  (** TODO: Maybe they should just be the bottom? **)
  Inductive WellFormed_ctx_subst
  : forall c, tenv typ -> tenv typ -> ctx_subst c -> Prop :=
  | WF_TopSubst : forall tus tvs, WellFormed_ctx_subst tus tvs TopSubst
  | WF_AllSubst : forall tus tvs t c s,
                    WellFormed_ctx_subst tus tvs s ->
                    WellFormed_ctx_subst tus (tvs ++ t :: nil) (@AllSubst t c s)
  | WF_HypSubst : forall tus tvs t c s,
                    WellFormed_ctx_subst tus tvs s ->
                    WellFormed_ctx_subst tus tvs (@HypSubst t c s)
  | WF_ExsSubst : forall tus tvs ts c s s',
                    SUBST.WellFormed s' ->
                    only_in_range (length tus + countUVars c) (length ts) s' ->
                    WellFormed_ctx_subst tus tvs s ->
                    WellFormed_ctx_subst (tus ++ ts) tvs (@ExsSubst ts c s s').

  Fixpoint ctx_lookup {c} (u : nat) (cs : ctx_subst c) : option expr :=
    match cs with
      | TopSubst => None
      | AllSubst _ _ c => ctx_lookup u c
      | HypSubst _ _ c => ctx_lookup u c
      | ExsSubst _ _ c s =>
        match amap_lookup u s with
          | None => ctx_lookup u c
          | Some e => Some e
        end
    end.

  Fixpoint ctx_domain {c} (cs : ctx_subst c) : list nat :=
    match cs with
      | TopSubst => nil
      | AllSubst _ _ c => ctx_domain c
      | HypSubst _ _ c => ctx_domain c
      | ExsSubst _ _ c s =>
        ctx_domain c ++ map fst (UVarMap.MAP.elements s)
    end.

  Fixpoint all_convertible (xs ys : tenv typ) : bool :=
    match xs , ys with
      | nil , nil => true
      | x :: xs , y :: ys =>
        match type_cast x y with
          | None => false
          | Some _ => all_convertible xs ys
        end
      | _ , _ => false
    end.

  Theorem all_convertible_sound
  : forall xs ys,
      all_convertible xs ys = true -> xs = ys.
  Proof.
    induction xs; destruct ys; simpl; intros; try congruence.
    destruct (type_cast a t).
    { destruct r. f_equal; eauto. }
    { congruence. }
  Qed.

  Definition drop_exact (tus ts : tenv typ)
  : option { ts' : tenv typ & hlist typD tus -> hlist typD ts' } :=
    let rem_len := length tus - length ts in
    let x := skipn rem_len tus in
    if all_convertible x ts then
      Some (@existT _ (fun ts' => hlist typD tus -> hlist typD ts')
                    (firstn rem_len tus)
                    (fun x =>
                       fst (hlist_split
                              (firstn rem_len tus)
                              (skipn rem_len tus)
                              match eq_sym (firstn_skipn _ _) in _ = l
                                    return hlist _ l with
                                | eq_refl => x
                              end)))
    else
      None.

  Fixpoint ctx_substD {c} tus tvs (cs : ctx_subst c) {struct cs}
  : option (exprT tus tvs Prop) :=
    match cs with
      | TopSubst => Some (fun _ _ => True)
      | HypSubst _ _ c => ctx_substD tus tvs c
      | AllSubst t _ c =>
        match drop_exact tvs (t :: nil) with
          | None => None
          | Some (existT tvs' get) =>
            match ctx_substD tus tvs' c with
              | None => None
              | Some sD => Some (fun us vs => sD us (get vs))
            end
        end
      | ExsSubst ts _ c s =>
        match drop_exact tus ts with
          | None => None
          | Some (existT tus' get) =>
            match SUBST.raw_substD tus tvs s
                , ctx_substD tus' tvs c
            with
              | Some sD' , Some sD =>
                Some (fun us vs => sD' us vs /\ sD (get us) vs)
              | None , _ => None
              | Some _ , None => None
            end
        end
    end.

  Section ctx_set'.
    Variables (u : nat) (e : expr) (min : nat) (nus : nat).

    Fixpoint ctx_set' {c T} (cs : ctx_subst c) {struct cs}
    : ((nat -> option expr) -> ctx_subst c -> option T) -> option T :=
      match cs in ctx_subst c
            return ((nat -> option expr) -> ctx_subst c -> option T) -> option T
      with
        | TopSubst => fun k => None
        | AllSubst _ _ c => fun k =>
          ctx_set' c (fun f c => k f (AllSubst c))
        | HypSubst _ _ c => fun k =>
          ctx_set' c (fun f c => k f (HypSubst c))
        | ExsSubst _ ctx c s => fun k =>
          if u ?[ ge ] (countUVars ctx + nus) then
            match amap_check_set u e s with
              | None => None
              | Some s' =>
                match amap_lookup u s with
                  | None => None
                  | Some e' =>
                    k (fun x => if x ?[ eq ] u then Some e' else None)
                      (ExsSubst c s')
                end
            end
          else
            ctx_set' c
                     (fun f c => k f (@ExsSubst _ ctx c
                                                (SUBST.raw_instantiate instantiate f s)))
      end.
  End ctx_set'.

  Definition ctx_set {c} (u : nat) (e : expr) (cs : ctx_subst c)
  : option (ctx_subst c) :=
    ctx_set' u e 0 cs (fun _ => @Some _).

  Fixpoint ctx_empty {c} : ctx_subst c :=
    match c with
      | CTop => TopSubst
      | CHyp c h => HypSubst ctx_empty
      | CAll c h => AllSubst ctx_empty
      | CExs c h => ExsSubst ctx_empty (UVarMap.MAP.empty _)
    end.

  Global Instance Subst_ctx_subst ctx : Subst (ctx_subst ctx) expr :=
  { subst_lookup := ctx_lookup
  ; subst_domain := ctx_domain
  }.

  Lemma drop_exact_sound
  : forall tus ts tus' cast,
      drop_exact tus ts = Some (@existT _ _ tus' cast) ->
      exists pf : tus' ++ ts = tus,
        forall a b, cast match pf in _ = tus return hlist _ tus with
                           | eq_refl => hlist_app a b
                         end = a.
  Proof.
    clear. unfold drop_exact. intros.
    forward; inv_all; subst.
    subst.
    eapply all_convertible_sound in H.
    exists (match H in _ = z return firstn _ tus ++ z = tus with
              | eq_refl => firstn_skipn _ _
            end).
    intros.
    generalize (firstn_skipn (length tus - length ts) tus).
    generalize dependent (skipn (length tus - length ts) tus).
    generalize dependent (firstn (length tus - length ts) tus).
    intros; subst. simpl. rewrite hlist_split_hlist_app.
    reflexivity.
  Qed.

  Global Instance Injective_WellFormed_ctx_subst tus tvs c t s
  : Injective (WellFormed_ctx_subst tus tvs (AllSubst (c:=c) (t:=t) s)) :=
    { result := exists tvs', tvs = tvs' ++ t :: nil /\
                             WellFormed_ctx_subst tus tvs' s }.
  Proof. admit. Defined.

  SearchAbout Injective.

  Global Instance Injective_app_cons {T} (a : list T) b c d
  : Injective (a ++ b :: nil = (c ++ d :: nil)) :=
    { result := a = c /\ b = d }.
  Proof. admit. Defined.

  Theorem ctx_substD_lookup ctx
  : forall (s : ctx_subst ctx) (uv : nat) (e : expr),
      ctx_lookup uv s = Some e ->
      forall (tus tvs : tenv typ),
        WellFormed_ctx_subst (tus ++ getUVars ctx) (tvs ++ getVars ctx)  s ->
        forall  (sD : exprT tus tvs Prop),
        ctx_substD tus tvs s = Some sD ->
        exists (t : typ) (val : exprT tus tvs (typD t))
               (get : hlist typD tus -> typD t),
          nth_error_get_hlist_nth typD tus uv =
          Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) /\
          exprD' tus tvs e t = Some val /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs),
             sD us vs -> get us = val us vs).
  Proof.
    induction s; simpl; intros.
    { congruence. }
    { forward; inv_all; subst.
      inv_all.
      eapply drop_exact_sound in H2.
      forward_reason.
      revert H1. subst.
      (*
      generalize x1. intro; inv_all; subst.
      specialize (IHs _ _ H _ _ H6 _ H3).
      forward_reason.
      eapply exprD'_weakenV with (tvs' := t :: nil) in H4; eauto.
      forward_reason.
      do 3 eexists; split; eauto. split; eauto.
      intros. revert H8.
      rewrite <- (hlist_app_hlist_split _ _ vs). intro.
      rewrite <- H7; clear H7.
      eapply H5.
      specialize (H0 (fst (hlist_split x0 (t :: nil) vs))
                     (snd (hlist_split x0 (t :: nil) vs))).
      generalize dependent (hlist_app (fst (hlist_split x0 (t :: nil) vs))
               (snd (hlist_split x0 (t :: nil) vs))). *)
      admit. }
    { admit. }
    { admit. (*forward; inv_all; subst.
      consider (UVarMap.MAP.find uv s'); intros; inv_all; subst.
      { eapply SUBST.substD_lookup in H2; eauto.
        forward_reason.
        do 3 eexists; split; eauto. split; eauto.
        intros. destruct H8. eauto. }
      { eapply IHWellFormed_ctx_subst in H3; eauto.
        forward_reason.
        eapply drop_exact_sound in H4.
        forward_reason.
        revert H4. subst tus; intros.
        exists x0.
        eapply nth_error_get_hlist_nth_weaken with (ls' := t) in H3.
        simpl in *. forward_reason.
        eapply exprD'_weakenU with (tus' := t) in H7; eauto.
        forward_reason.
        do 2 eexists; split; eauto; split; eauto.
        do 2 intro.
        rewrite <- (hlist_app_hlist_split _ _ us).
        rewrite <- H9; clear H9.
        rewrite <- H10; clear H10. destruct 1.
        eapply H8. rewrite H4 in H10. assumption. } *) }
  Qed.

  Lemma ctx_subst_domain ctx tus tvs
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst tus tvs s ->
      forall (ls : list nat),
      subst_domain s = ls ->
      forall n : nat, In n ls <-> subst_lookup n s <> None.
  Proof.
    induction 1; simpl; intros; eauto using WellFormed_domain.
    { subst. split; auto. congruence. }
    { subst. rewrite in_app_iff.
      split; intro.
      { forward.
        destruct H2.
        { eapply IHWellFormed_ctx_subst in H2; eauto. }
        { eapply SUBST.WellFormed_domain in H2; eauto. } }
      { rewrite IHWellFormed_ctx_subst; eauto.
        rewrite SUBST.WellFormed_domain; eauto.
        unfold SUBST.raw_lookup, amap_lookup in *.
        destruct (UVarMap.MAP.find n s'); eauto. } }
  Qed.

  Global Instance SubstOk_cxt_subst tus tvs ctx
  : @SubstOk (ctx_subst ctx) typ expr _ _ _ :=
  { WellFormed_subst := @WellFormed_ctx_subst ctx (tus ++ getUVars ctx) (tvs ++ getVars ctx)
  ; substD := @ctx_substD _
  }.
  { intros. eapply ctx_substD_lookup in H; eauto. eapply H0. auto. }
  { intros; eapply ctx_subst_domain; eauto. }
  { admit. }
  Defined.

  Global Instance SubstUpdate_ctx_subst ctx
  : SubstUpdate (ctx_subst ctx) expr :=
  { subst_set := ctx_set
  ; subst_empty := ctx_empty
  }.

  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Fixpoint pctxD (tus tvs : tenv typ) (ctx : Ctx) (s : ctx_subst ctx) {struct s}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match s in ctx_subst ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | TopSubst =>
        Some (fun k us vs => k (hlist_app us Hnil) (hlist_app vs Hnil))
      | AllSubst t ctx' s' =>
        match pctxD tus tvs s' with
          | Some cD =>
            Some (fun k : exprT _ _ Prop =>
                    cD (fun us vs =>
                          forall x : typD t,
                            k us
                              match
                                app_ass_trans tvs (getVars ctx') (t :: nil) in (_ = t0)
                                return (hlist typD t0)
                              with
                                | eq_refl => hlist_app vs (Hcons x Hnil)
                              end))
          | None => None
        end
      | ExsSubst ts ctx' s' sub =>
        match SUBST.raw_substD ((tus ++ getUVars ctx') ++ ts) (tvs ++ getVars ctx') sub
            , pctxD tus tvs s'
        with
          | Some sD , Some cD =>
            Some (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                    cD (fun us vs =>
                          _foralls typD ts (fun us' =>
                                             sD (hlist_app us us') vs ->
                                             k match
                                                 app_ass_trans tus _ ts in (_ = t0)
                                                 return (hlist typD t0)
                                               with
                                                 | eq_refl => hlist_app us us'
                                               end
                                               vs)))
          | _ , _ => None
        end
      | HypSubst h ctx' s' =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match pctxD tus tvs s' with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

  Definition RCtx {tus tvs tus' tvs'} :=
    (RexprT tus tvs Basics.impl ==> RexprT tus' tvs' Basics.impl)%signature.

  Local Existing Instance Transitive_Roption.
  Local Existing Instance Symmetric_Roption.
  Local Existing Instance Reflexive_Roption.
  Local Existing Instance Transitive_RexprT.
  Local Existing Instance Symmetric_RexprT.
  Local Existing Instance Reflexive_RexprT.

  Theorem Proper_pctxD_iff
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) iff ==>
                              (RexprT tus tvs iff)))%signature
             (@pctxD tus tvs c1 s).
  Proof.
    induction s; simpl; intros.
    { constructor.
      do 6 red; simpl; intros.
      eapply H; rewrite <- equiv_hlist_app; split; auto; constructor. }
    { red; simpl.
      destruct (pctxD tus tvs s); try constructor.
      inv_all.
      do 6 red. intros.
      eapply IHs; eauto.
      do 5 red; intros.
      eapply forall_iff. intros.
      eapply H; eauto.
      equivs. reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try constructor
             end.
      red; intros.
      inv_all. eapply IHs.
      do 5 red; intros.
      apply equiv_eq_eq in H0.
      apply equiv_eq_eq in H1. subst.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try solve [ constructor ]
             end.
      constructor.
      inv_all; do 6 red; intros.
      equivs.
      eapply IHs; try reflexivity.
      do 5 red; intros; equivs.
      eapply _forall_iff. intros.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
  Qed.

  Theorem Proper_pctxD_impl
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) Basics.impl ==>
                              (RexprT tus tvs Basics.impl)))%signature
             (@pctxD tus tvs c1 s).
  Proof.
    induction s; simpl; intros.
    { constructor.
      do 6 red; intros.
      eapply H; rewrite <- equiv_hlist_app; split; auto; constructor. }
    { red; simpl.
      destruct (pctxD tus tvs s); try constructor.
      inv_all.
      do 7 red. intros.
      eapply IHs; eauto.
      do 6 red; intros.
      equivs.
      eapply H; eauto; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try constructor
             end.
      red; intros.
      inv_all. eapply IHs.
      do 6 red; intros.
      equivs.
      eapply H; eauto; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try solve [ constructor ]
             end.
      constructor.
      inv_all.
      do 7 red; intros.
      eapply IHs; eauto.
      do 6 red; intros.
      equivs.
      eapply _forall_sem; intro.
      eapply _forall_sem with (x := x0) in H5.
      intros. eapply H; eauto; reflexivity. }
  Qed.

  Theorem Applicative_pctxD
  : forall tus tvs ctx s C,
      @pctxD tus tvs ctx s = Some C ->
      (forall us vs (P Q : exprT _ _ Prop),
         C (fun a b => P a b -> Q a b) us vs ->
         C P us vs ->
         C Q us vs) /\
      (forall us vs (Q : exprT _ _ Prop), (forall a b, Q a b) -> C Q us vs).
  Proof.
    clear. induction s; simpl; intros.
    { forward; inv_all; subst.
      forward_reason; split; eauto. }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H0; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto. }
      { intros us vs Q v.
        eapply Hpure. intros; eauto. } }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal; intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H1; [ | reflexivity | reflexivity | eapply f ].
        clear.
        do 6 red; intros; equivs.
        tauto. }
      { intros. eapply Hpure.
        intros. eauto. } }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { rename P into P0.
        intros us vs P Q f.
        eapply Hap.
        eapply H1; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto.
        eapply _forall_sem. intros.
        rewrite _forall_sem in H2.
        rewrite _forall_sem in H1.
        eauto. }
      { intros us vs Q v.
        eapply Hpure. intros.
        eapply _forall_sem; intros.
        eauto. } }
  Qed.

  Lemma Ap_pctxD
  : forall tus tvs (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop ->
                exprT tus tvs Prop),
      pctxD tus tvs s = Some C ->
      forall (us : hlist typD tus) (vs : hlist typD tvs)
             (P Q : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop),
        C (fun us vs => P us vs -> Q us vs) us vs -> C P us vs -> C Q us vs.
  Proof.
    intros. revert H1. revert H0. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H.
  Qed.

  Lemma Pure_pctxD
  : forall tus tvs (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop ->
                exprT tus tvs Prop),
      pctxD tus tvs s = Some C ->
      forall (P : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop),
        (forall us vs, P us vs) -> forall us vs, C P us vs.
  Proof.
    intros. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H1; eauto.
  Qed.

  Definition CtxMorphism {tus tvs tus' tvs'}
             (c1 c2 : exprT tus tvs Prop -> exprT tus' tvs' Prop) : Prop :=
    forall (P : exprT _ _ Prop) us vs, c1 P us vs -> c2 P us vs.

  Inductive SubstMorphism (tus tvs : tenv typ)
  : forall c : Ctx, ctx_subst c -> ctx_subst c -> Prop :=
  | SMall : forall c t s1 s2,
              @SubstMorphism tus tvs c s1 s2 ->
              @SubstMorphism tus tvs (CAll c t) (AllSubst s1) (AllSubst s2)
  | SMexs : forall c ts s1 s2 cs1 cs2,
              (match @pctxD tus tvs c cs1
                   , SUBST.raw_substD ((tus ++ getUVars c) ++ ts) (tvs ++ getVars c) s1
                   , @pctxD tus tvs c cs2
                   , SUBST.raw_substD ((tus ++ getUVars c) ++ ts) (tvs ++ getVars c) s2
               with
                 | None , _ , _ , _
                 | Some _ , None , _ , _ => True
                 | Some _ , Some _ , None , _
                 | Some _ , Some _ , Some _ , None => False
                 | Some c1D , Some s1D , Some c2D , Some s2D =>
                   forall us vs, c2D (fun us vs =>
                                       forall us',
                                         s2D (hlist_app us us') vs ->
                                         s1D (hlist_app us us') vs) us vs
               end) ->
              @SubstMorphism tus tvs c cs1 cs2 ->
              @SubstMorphism tus tvs (CExs c ts) (ExsSubst cs1 s1) (ExsSubst cs2 s2)
  | SMhyp : forall c h s1 s2,
              @SubstMorphism tus tvs c s1 s2 ->
              @SubstMorphism tus tvs (CHyp c h) (HypSubst s1) (HypSubst s2)
  | SMtop : @SubstMorphism tus tvs CTop TopSubst TopSubst.

  Lemma Fmap_pctxD_impl
  : forall tus tvs c s C,
      @pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ Basics.impl ==> RexprT tus tvs Basics.impl)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_impl tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma Fmap_pctxD_iff
  : forall tus tvs c s C,
      @pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ iff ==> RexprT tus tvs iff)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_iff tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma pctxD_SubstMorphism
  : forall tus tvs ctx s s',
      @SubstMorphism tus tvs ctx s s' ->
      forall C C',
      @pctxD tus tvs ctx s = Some C ->
      @pctxD tus tvs ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C P us vs -> C' P us vs.
  Proof.
    clear instantiate.
    induction 1; intros; simpl in *; forward; inv_all; subst; eauto.
    { eapply IHSubstMorphism; eauto. }
    { simpl in *.
      eapply (IHSubstMorphism _ _ eq_refl eq_refl) in H3.
      destruct (Applicative_pctxD _ H2) as [ Hap Hpure ].
      revert H3. eapply Hap.
      generalize (H7 us vs).
      eapply Hap.
      eapply Hpure.
      clear. intros.
      rewrite _forall_sem.
      rewrite _forall_sem in H0.
      intros; eauto. }
    { eapply IHSubstMorphism; eauto. }
  Qed.

  Definition fromAll {c t} (cs : ctx_subst (CAll c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CAll c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | AllSubst _ _ c => c
      | _ => tt
    end.

  Definition fromHyp {c t} (cs : ctx_subst (CHyp c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CHyp c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | HypSubst _ _ c => c
      | _ => tt
    end.

  Definition fromExs {c t} (cs : ctx_subst (CExs c t)) : subst * ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CExs c _ => subst * ctx_subst c
                   | _ => unit
                 end
    with
      | ExsSubst _ _ c s => (s,c)
      | _ => tt
    end.

  Global Instance Injective_SubstMorphism_AllSubst tus tvs t ctx s s'
  : Injective (@SubstMorphism tus tvs (CAll ctx t) (AllSubst s) s') :=
  { result := exists s'', s' = AllSubst s'' /\ @SubstMorphism tus tvs ctx s s'' }.
  intros.
  exists (fromAll s').
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | AllSubst t s c => fun s' =>
                                            s' = AllSubst (fromAll s') /\
                                            SubstMorphism tus tvs c (fromAll s')
                    | _ => fun _ => True
                  end Y
     with
       | SMall _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_HypSubst tus tvs t ctx s s'
  : Injective (@SubstMorphism tus tvs (CHyp ctx t) (HypSubst s) s') :=
  { result := exists s'', s' = HypSubst s'' /\ @SubstMorphism tus tvs ctx s s'' }.
  intros.
  exists (fromHyp s').
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | HypSubst t s c => fun s' =>
                                            s' = HypSubst (fromHyp s') /\
                                            SubstMorphism tus tvs c (fromHyp s')
                    | _ => fun _ => True
                  end Y
     with
       | SMhyp _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_TopSubst tus tvs s'
  : Injective (@SubstMorphism tus tvs CTop TopSubst s') :=
  { result := s' = TopSubst }.
  Proof.
    intros.
    refine
      (match H in @SubstMorphism _ _ C X Y
             return match X in ctx_subst C' return ctx_subst C' -> Prop with
                      | TopSubst => fun s' => s' = TopSubst
                      | _ => fun _ => True
                    end Y
       with
         | SMtop => eq_refl
         | _ => I
       end).
  Defined.

  Global Instance Injective_SubstMorphism_ExsSubst tus tvs ctx tes s s' sub
  : Injective (@SubstMorphism tus tvs (CExs ctx tes) (ExsSubst sub s) s') :=
  { result := exists s'' sub',
                s' = ExsSubst sub' s''
                /\ (match @pctxD tus tvs ctx sub
                        , SUBST.raw_substD ((tus ++ getUVars ctx) ++ tes) (tvs ++ getVars ctx) s
                        , @pctxD tus tvs ctx sub'
                        , SUBST.raw_substD ((tus ++ getUVars ctx) ++ tes) (tvs ++ getVars ctx) s''
                    with
                      | None , _ , _ , _
                      | Some _ , None , _ , _ => True
                      | Some _ , Some _ , None , _
                      | Some _ , Some _ , Some _ , None => False
                      | Some c1D , Some s1D , Some c2D , Some s2D =>
                        forall us vs, c2D (fun us vs =>
                                             forall us',
                                               s2D (hlist_app us us') vs ->
                                               s1D (hlist_app us us') vs) us vs
                    end)
                /\ SubstMorphism tus tvs sub sub'}.
  intros. exists (fst (fromExs s')). exists (snd (fromExs s')).
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | ExsSubst t s su c =>
                      fun s' =>
                        s' = ExsSubst (snd (fromExs s')) (fst (fromExs s')) /\
                        match pctxD tus tvs su with
                          | Some _ =>
                            match
                              SUBST.raw_substD ((tus ++ getUVars s) ++ t) (tvs ++ getVars s) c
                            with
                              | Some s1D =>
                                match pctxD tus tvs (snd (fromExs s')) with
                                  | Some c2D =>
                                    match
                                      SUBST.raw_substD ((tus ++ getUVars s) ++ t)
                                             (tvs ++ getVars s) (fst (fromExs s'))
                                    with
                                      | Some s2D =>
                                        forall us vs,
                                          c2D
                                            (fun us0 vs0 =>
                                               forall us' : hlist typD t,
                                                 s2D (hlist_app us0 us') vs0 ->
                                                 s1D (hlist_app us0 us') vs0) us vs
                                      | None => False
                                    end
                                  | None => False
                                end
                              | None => True
                            end
                          | None => True
                        end /\
                        SubstMorphism tus tvs su (snd (fromExs s'))
                    | _ => fun _ => True
                  end Y
     with
       | SMexs _ _ _ _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Reflexive_SubstMorphism tus tvs ctx
  : Reflexive (@SubstMorphism tus tvs ctx).
  Proof.
    red. induction x;
         simpl; intros; try constructor;
         forward; eauto.
    eapply Applicative_pctxD; eauto.
  Qed.

  Global Instance Transitive_SubstMorphism tus tvs ctx
  : Transitive (@SubstMorphism tus tvs ctx).
  Proof.
    red. intros x y z H; revert z.
    induction H.
    { intros; inv_all; subst.
      constructor; eauto. }
    { intros; inv_all; subst.
      forward. simpl in *.
      constructor.
      { forward. inv_all; subst.
        Cases.rewrite_all_goal.
        repeat match goal with
                 | H : ?X = _ , H' : ?X = _ |- _ =>
                   rewrite H in H'
               end; inv_all; subst.
        specialize (H8 us vs).
        specialize (H6 us vs).
        revert H8.
        eapply (Applicative_pctxD _ H5).
        eapply (pctxD_SubstMorphism H4 H1 H5 us vs).
        revert H6.
        eapply (Fmap_pctxD_impl _ H1); try reflexivity.
        clear.
        do 6 red. intros. equivs. firstorder. }
      { eapply IHSubstMorphism. eassumption. } }
    { intros; inv_all; subst. constructor; eauto. }
    { intros; inv_all; subst.
      constructor. }
  Qed.

End parameterized.

Arguments CTop {typ expr} : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.ExprDAs.
