Require Import Coq.Bool.Bool.
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

(** TODO: Move to Data.List **)
Global Instance Injective_app_cons {T} (a : list T) b c d
: Injective (a ++ b :: nil = (c ++ d :: nil)) :=
  { result := a = c /\ b = d }.
Proof. eapply app_inj_tail. Defined.

Ltac equivs :=
  repeat match goal with
           | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
         end; subst.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable RelDec_eq_typ : RelDec (@eq typ).
  Context {RelDecOk_eq_typ : RelDec_Correct RelDec_eq_typ}.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Inductive Ctx :=
  | CTop : tenv typ -> tenv typ -> Ctx
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
      | CTop _ tvs => length tvs
      | CAll ctx' t => S (countVars ctx')
      | CExs ctx' _
      | CHyp ctx' _ => countVars ctx'
    end.

  Fixpoint countUVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop tus _ => length tus
      | CExs ctx' ts => length ts + countUVars ctx'
      | CAll ctx' _
      | CHyp ctx' _ => countUVars ctx'
    end.

  Fixpoint getUVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop tus _ => tus
      | CAll ctx' _ => getUVars ctx'
      | CExs ctx' ts => getUVars ctx' ++ ts
      | CHyp ctx' _ => getUVars ctx'
    end.

  Fixpoint getVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop _ tvs => tvs
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
      | CTop tus' tvs' => (tus' ++ tus, tvs' ++ tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CExs ctx' ts => getEnvs' ctx' (ts ++ tus) tvs (** TODO: Check **)
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv typ * tenv typ :=
    getEnvs' ctx nil nil.

  Fixpoint countEnvs' (ctx : Ctx) (nus nvs : nat) : nat * nat :=
    match ctx with
      | CTop tus' tvs' => (length tus' + nus, length tvs' + nvs)
      | CAll ctx' t => countEnvs' ctx' nus (S nvs)
      | CExs ctx' ts => countEnvs' ctx' (length ts + nus) nvs
      | CHyp ctx' _ => countEnvs' ctx' nus nvs
    end.

  Definition countEnvs (ctx : Ctx) : nat * nat :=
    countEnvs' ctx 0 0.

  (** c2 goes on top! **)
  Fixpoint Ctx_append (c1 c2 : Ctx) : Ctx :=
    match c2 with
      | CTop _ _ => c1
      | CAll ctx' t => CAll (Ctx_append c1 ctx') t
      | CExs ctx' ts => CExs (Ctx_append c1 ctx') ts
      | CHyp ctx' h => CHyp (Ctx_append c1 ctx') h
    end.

  Fixpoint getAmbient (ctx : Ctx) : (tenv typ * tenv typ) :=
    match ctx with
      | CTop tus tvs => (tus,tvs)
      | CAll ctx' _ => getAmbient ctx'
      | CExs ctx' _ => getAmbient ctx'
      | CHyp ctx' _ => getAmbient ctx'
    end.

  Fixpoint getAmbientVars ctx : tenv typ :=
    match ctx with
      | CTop _ tvs => tvs
      | CAll ctx' _ => getAmbientVars ctx'
      | CExs ctx' _ => getAmbientVars ctx'
      | CHyp ctx' _ => getAmbientVars ctx'
    end.

  Fixpoint getAmbientUVars ctx : tenv typ :=
    match ctx with
      | CTop tus _ => tus
      | CAll ctx' _ => getAmbientUVars ctx'
      | CExs ctx' _ => getAmbientUVars ctx'
      | CHyp ctx' _ => getAmbientUVars ctx'
    end.

  Lemma getEnvs'_getUVars_getVars
  : forall c a b,
      getEnvs' c a b  = (getUVars c ++ a, getVars c ++ b).
  Proof.
    induction c; simpl; intros; auto.
    { rewrite IHc. f_equal. rewrite <- app_assoc. reflexivity. }
    { rewrite IHc. f_equal. rewrite <- app_assoc. reflexivity. }
  Qed.

  Lemma getEnvs_getUVars_getVars
  : forall c, getEnvs c = (getUVars c, getVars c).
  Proof.
    clear. unfold getEnvs. intros.
    rewrite getEnvs'_getUVars_getVars.
    f_equal; apply app_nil_r.
  Qed.

  Theorem getUVars_append
  : forall c1 c2,
      getAmbient c2 = getEnvs c1 ->
      getUVars (Ctx_append c1 c2) = getUVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    + rewrite getEnvs_getUVars_getVars. intros; inv_all; auto.
    + intro. rewrite IHc2; eauto.
  Defined.

  Theorem getVars_append
  : forall c1 c2,
      getAmbient c2 = getEnvs c1 ->
      getVars (Ctx_append c1 c2) = getVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    + rewrite getEnvs_getUVars_getVars. intros; inv_all; auto.
    + intro; rewrite IHc2; auto.
  Defined.
  (** End: Auxiliary Functions **)

  Require Import MirrorCore.Subst.FMapSubst.

  Definition amap : Type := SUBST.raw expr.
  Definition WellFormed_amap : amap -> Prop := @SUBST.WellFormed _ _ _ _.
  Definition amap_empty : amap := UVarMap.MAP.empty _.
  Definition amap_lookup : nat -> amap -> option expr :=
    @UVarMap.MAP.find _.
  Definition amap_check_set : nat -> expr -> amap -> option amap :=
    @SUBST.raw_set _ _ _ _ instantiate.
  Definition amap_instantiate (f : nat -> option expr) : amap -> amap :=
    UVarMap.MAP.map (fun e => instantiate f 0 e).

  Inductive ctx_subst : Ctx -> Type :=
  | TopSubst : forall tus tvs, ctx_subst (CTop tus tvs)
  | AllSubst : forall {t c}, ctx_subst c -> ctx_subst (CAll c t)
  | HypSubst : forall {t c}, ctx_subst c -> ctx_subst (CHyp c t)
  | ExsSubst : forall {ts c}, ctx_subst c -> amap -> ctx_subst (CExs c ts).

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

  Definition fromExs {c t} (cs : ctx_subst (CExs c t)) : amap * ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CExs c _ => amap * ctx_subst c
                   | _ => unit
                 end
    with
      | ExsSubst _ _ c s => (s,c)
      | _ => tt
    end.

  Definition only_in_range (min len : nat) (s : amap) : Prop :=
    forall u e, amap_lookup u s = Some e -> min <= u < min + len.

  (** [tus] and [tvs] are only the environments for Top! **)
  Inductive WellFormed_ctx_subst
  : forall c, ctx_subst c -> Prop :=
  | WF_TopSubst : forall tus tvs, WellFormed_ctx_subst (TopSubst tus tvs)
  | WF_AllSubst : forall t c s,
                    WellFormed_ctx_subst s ->
                    WellFormed_ctx_subst (@AllSubst t c s)
  | WF_HypSubst : forall t c s,
                    WellFormed_ctx_subst s ->
                    WellFormed_ctx_subst (@HypSubst t c s)
  | WF_ExsSubst : forall ts c s s',
                    SUBST.WellFormed s' ->
                    only_in_range (countUVars c) (length ts) s' ->
                    WellFormed_ctx_subst s ->
                    WellFormed_ctx_subst (@ExsSubst ts c s s').

  Fixpoint ctx_lookup {c} (u : nat) (cs : ctx_subst c) : option expr :=
    match cs with
      | TopSubst _ _ => None
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
      | TopSubst _ _ => nil
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
      | TopSubst tus' tvs' =>
        if (tus ?[ eq ] tus') && (tvs ?[ eq ] tvs') then
          Some (fun _ _ => True)
        else
          None
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

  Axiom mentionsAny : (nat -> bool) -> (nat -> bool) -> expr -> bool.

  Section ctx_set'.
    Variables (u : nat) (e : expr).

    Fixpoint ctx_set' {c T} (cs : ctx_subst c) {struct cs}
    : ((nat -> option expr) -> ctx_subst c -> option T) -> option T :=
      match cs in ctx_subst c
            return ((nat -> option expr) -> ctx_subst c -> option T) -> option T
      with
        | TopSubst _ _ => fun k => None
        | AllSubst _ _ c => fun k =>
          ctx_set' c (fun f c => k f (AllSubst c))
        | HypSubst _ _ c => fun k =>
          ctx_set' c (fun f c => k f (HypSubst c))
        | ExsSubst ts ctx c s => fun k =>
          let (nus,nvs) := countEnvs ctx in
          if u ?[ ge ] nus then
            let max_nus := length ts + nus in
            if mentionsAny (fun x => x ?[ ge ] max_nus)
                           (fun x => x ?[ gt ] nvs) e then
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
              None
          else
            ctx_set' c
                     (fun f c => k f (@ExsSubst _ ctx c
                                                (SUBST.raw_instantiate instantiate f s)))
      end.
  End ctx_set'.

  Definition ctx_set {c} (u : nat) (e : expr) (cs : ctx_subst c)
  : option (ctx_subst c) :=
    ctx_set' u e cs (fun _ => @Some _).

(*
  Fixpoint simple_ctx_set' {c} (u : uvar) (e : expr) (cs : ctx_subst c)
  : option (ctx_subst c * (nat -> option expr)).
  refine (
    match cs in ctx_subst c
          return option (ctx_subst c * (nat -> option expr))
    with
      | TopSubst _ _ => None
      | AllSubst t _ cs' => @simple_ctx_set' _ (CAll _ t) u e cs' (AllSubst rst)
      | HypSubst _ _ c => _
      | ExsSubst _ ctx c s => _
    end).
fun k =>
          if u ?[ ge ] (countUVars ctx) then
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
*)

  Fixpoint ctx_empty {c} : ctx_subst c :=
    match c with
      | CTop _ _ => TopSubst _ _
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

  Global Instance Injective_ExsSubst ts ctx a b c d
  : Injective (ExsSubst (ts:=ts)(c:=ctx) a b = ExsSubst c d) :=
    { result := a = c /\ b = d }.
  intro pf.
  refine (match pf in _ = X return
                match X with
                  | ExsSubst _ _ c d => fun a b => a = c /\ b = d
                  | _ => True
                end a b
          with
            | eq_refl => conj eq_refl eq_refl
          end).
  Defined.


  Global Instance Injective_WellFormed_ctx_subst_All c t s
  : Injective (WellFormed_ctx_subst (AllSubst (c:=c) (t:=t) s)) :=
  { result := WellFormed_ctx_subst s }.
  Proof.
    refine (fun x =>
              match x in WellFormed_ctx_subst z
                    return match z return Prop with
                             | AllSubst _ _ s => WellFormed_ctx_subst s
                             | _ => True
                           end
              with
                | WF_AllSubst _ _ _ pf => pf
                | _ => I
              end).
  Defined.

  Global Instance Injective_WellFormed_ctx_subst_Hyp c t s
  : Injective (WellFormed_ctx_subst (HypSubst (c:=c) (t:=t) s)) :=
  { result := WellFormed_ctx_subst s }.
  Proof.
    refine (fun x =>
              match x in WellFormed_ctx_subst z
                    return match z return Prop with
                             | HypSubst _ _ s => WellFormed_ctx_subst s
                             | _ => True
                           end
              with
                | WF_HypSubst _ _ _ pf => pf
                | _ => I
              end).
  Defined.

  Global Instance Injective_WellFormed_ctx_subst_Top tus tvs
  : Injective (WellFormed_ctx_subst (TopSubst tus tvs)) :=
  { result := True }.
  Proof. trivial. Defined.

  Global Instance Injective_WellFormed_ctx_subst_ExsSubst ctx ts c s
  : Injective (WellFormed_ctx_subst (c:=CExs ctx ts) (ExsSubst c s)) :=
  { result := WellFormed_ctx_subst c /\
              WellFormed_amap s /\
              only_in_range (countUVars ctx) (length ts) s }.
  intro.
  refine match H in @WellFormed_ctx_subst C S
               return match C as C return ctx_subst C -> Prop with
                        | CExs c0 ts => fun s' =>
                          let (s,c) := fromExs s' in
                          WellFormed_ctx_subst c /\
                          WellFormed_amap s /\
                          only_in_range (countUVars c0) (length ts) s
                        | _ => fun _ => True
                      end S
         with
           | WF_ExsSubst t c s s' pfs' pf'' pfs => conj pfs (conj pfs' pf'')
           | _ => I
         end.
  Defined.

  Theorem ctx_substD_lookup ctx
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
      forall (uv : nat) (e : expr),
      ctx_lookup uv s = Some e ->
      forall (tus tvs : tenv typ),
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
    induction 1; simpl; intros.
    { congruence. }
    { forward; inv_all; subst.
      eapply drop_exact_sound in H2.
      forward_reason.
      revert H1; subst.
      eapply IHWellFormed_ctx_subst in H3; eauto.
      forward_reason.
      eapply exprD'_weakenV with (tvs' := t :: nil) in H2; eauto.
      forward_reason.
      do 3 eexists; split; eauto. split; eauto.
      intros. revert H6.
      rewrite <- (hlist_app_hlist_split _ _ vs). intro.
      rewrite <- H4; clear H4.
      eapply H3.
      rewrite H5 in H6. assumption. }
    { eauto. }
    { forward; inv_all; subst.
      consider (amap_lookup uv s'); intros; inv_all; subst.
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
        eapply nth_error_get_hlist_nth_weaken with (ls' := ts) in H3.
        simpl in *. forward_reason.
        eapply exprD'_weakenU with (tus' := ts) in H7; eauto.
        forward_reason.
        do 2 eexists; split; eauto; split; eauto.
        do 2 intro.
        rewrite <- (hlist_app_hlist_split _ _ us).
        rewrite <- H9; clear H9.
        rewrite <- H10; clear H10. destruct 1.
        eapply H8. rewrite H4 in H10. assumption. } }
  Qed.

  Lemma ctx_subst_domain ctx
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
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

  Global Instance SubstOk_ctx_subst ctx
  : @SubstOk (ctx_subst ctx) typ expr _ _ _ :=
  { WellFormed_subst := @WellFormed_ctx_subst ctx
  ; substD := @ctx_substD ctx
  }.
  { clear instantiate. intros. eapply ctx_substD_lookup; eauto. }
  { clear instantiate. intros; eapply ctx_subst_domain; eauto. }
  { clear instantiate. admit. }
  Defined.

  Global Instance SubstUpdate_ctx_subst ctx
  : SubstUpdate (ctx_subst ctx) expr :=
  { subst_set := ctx_set }.

  Fixpoint ctx_subst_append (c1 c2 : Ctx)
           (s1 : ctx_subst c1) (s2 : ctx_subst c2)
  : ctx_subst (Ctx_append c1 c2) :=
    match s2 in ctx_subst c2
          return ctx_subst (Ctx_append c1 c2)
    with
      | TopSubst _ _ => s1
      | HypSubst _ _ cs => HypSubst (ctx_subst_append s1 cs)
      | AllSubst _ _ cs => AllSubst (ctx_subst_append s1 cs)
      | ExsSubst _ _ cs s => ExsSubst (ctx_subst_append s1 cs) s
    end.

  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Fixpoint pctxD (ctx : Ctx) (s : ctx_subst ctx) {struct s}
  : option (   exprT (getUVars ctx) (getVars ctx) Prop
            -> exprT (getAmbientUVars ctx) (getAmbientVars ctx) Prop) :=
    match s in ctx_subst ctx
          return option (   exprT (getUVars ctx) (getVars ctx) Prop
                         -> exprT (getAmbientUVars ctx) (getAmbientVars ctx) Prop)
    with
      | TopSubst _ _ =>
        Some (fun k us vs => k us vs)
      | AllSubst t ctx' s' =>
        match pctxD s' with
          | Some cD =>
            Some (fun k : exprT _ _ Prop =>
                    cD (fun us vs =>
                          forall x : typD t,
                            k us
                              match
                                app_ass_trans nil (getVars ctx') (t :: nil) in (_ = t0)
                                return (hlist typD t0)
                              with
                                | eq_refl => hlist_app vs (Hcons x Hnil)
                              end))
          | None => None
        end
      | ExsSubst ts ctx' s' sub =>
        match SUBST.raw_substD (getUVars ctx' ++ ts) (getVars ctx') sub
            , pctxD s'
        with
          | Some sD , Some cD =>
            Some (fun k : exprT (getUVars ctx' ++ ts) (getVars ctx') Prop =>
                    cD (fun us vs =>
                          _foralls typD ts (fun us' =>
                                             sD (hlist_app us us') vs ->
                                             k match
                                                 app_ass_trans nil _ ts in (_ = t0)
                                                 return (hlist typD t0)
                                               with
                                                 | eq_refl => hlist_app us us'
                                               end
                                               vs)))
          | _ , _ => None
        end
      | HypSubst h ctx' s' =>
        match propD (getUVars ctx') (getVars ctx') h with
          | None => None
          | Some pD => match pctxD s' with
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
  : forall c1 s,
      Proper (Roption (RexprT (getUVars c1) (getVars c1) iff ==>
                              (RexprT _ _ iff)))%signature
             (@pctxD c1 s).
  Proof.
    induction s; simpl; intros.
    { constructor.
      do 6 red; simpl; intros.
      eapply H; auto. }
    { red; simpl.
      destruct (pctxD s); try constructor.
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
  : forall c1 s,
      Proper (Roption (RexprT (getUVars c1) (getVars c1) Basics.impl ==>
                              (RexprT _ _ Basics.impl)))%signature
             (@pctxD c1 s).
  Proof.
    induction s; simpl; intros.
    { constructor.
      do 6 red; intros.
      eapply H; auto. }
    { red; simpl.
      destruct (pctxD s); try constructor.
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
  : forall ctx s C,
      @pctxD ctx s = Some C ->
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
      generalize (Proper_pctxD_impl s).
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
      generalize (Proper_pctxD_impl s).
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
      generalize (Proper_pctxD_impl s).
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
  : forall (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (getUVars ctx) (getVars ctx) Prop ->
                exprT _ _  Prop),
      pctxD s = Some C ->
      forall (us : hlist typD _) (vs : hlist typD _)
             (P Q : exprT (getUVars ctx) (getVars ctx) Prop),
        C (fun us vs => P us vs -> Q us vs) us vs -> C P us vs -> C Q us vs.
  Proof.
    clear.
    intros. revert H1. revert H0. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H.
  Qed.

  Lemma Pure_pctxD
  : forall (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (getUVars ctx) (getVars ctx) Prop ->
                exprT _ _ Prop),
      pctxD s = Some C ->
      forall (P : exprT (getUVars ctx) (getVars ctx) Prop),
        (forall us vs, P us vs) -> forall us vs, C P us vs.
  Proof.
    clear.
    intros. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H1; eauto.
  Qed.

  Definition CtxMorphism {tus tvs tus' tvs'}
             (c1 c2 : exprT tus tvs Prop -> exprT tus' tvs' Prop) : Prop :=
    forall (P : exprT _ _ Prop) us vs, c1 P us vs -> c2 P us vs.

  Inductive SubstMorphism
  : forall c : Ctx, ctx_subst c -> ctx_subst c -> Prop :=
  | SMall : forall c t s1 s2,
              @SubstMorphism c s1 s2 ->
              @SubstMorphism (CAll c t) (AllSubst s1) (AllSubst s2)
  | SMexs : forall c ts s1 s2 cs1 cs2,
              (match @pctxD c cs1
                   , SUBST.raw_substD ((getUVars c) ++ ts) (getVars c) s1
                   , @pctxD c cs2
                   , SUBST.raw_substD ((getUVars c) ++ ts) (getVars c) s2
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
              @SubstMorphism c cs1 cs2 ->
              @SubstMorphism (CExs c ts) (ExsSubst cs1 s1) (ExsSubst cs2 s2)
  | SMhyp : forall c h s1 s2,
              @SubstMorphism c s1 s2 ->
              @SubstMorphism (CHyp c h) (HypSubst s1) (HypSubst s2)
  | SMtop : forall tus tvs, @SubstMorphism (CTop tus tvs) (TopSubst _ _) (TopSubst _ _).

  Lemma Fmap_pctxD_impl
  : forall c s C,
      @pctxD c s = Some C ->
      Proper (RexprT _ _ Basics.impl ==> RexprT _ _ Basics.impl)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_impl c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma Fmap_pctxD_iff
  : forall c s C,
      @pctxD c s = Some C ->
      Proper (RexprT _ _ iff ==> RexprT _ _ iff)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_iff c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma pctxD_SubstMorphism
  : forall ctx s s',
      @SubstMorphism ctx s s' ->
      forall C C',
      @pctxD ctx s = Some C ->
      @pctxD ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C P us vs -> C' P us vs.
  Proof.
    clear RelDecOk_eq_typ RelDec_eq_typ instantiate.
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

  Global Instance Injective_SubstMorphism_AllSubst t ctx s s'
  : Injective (@SubstMorphism (CAll ctx t) (AllSubst s) s') :=
  { result := exists s'', s' = AllSubst s'' /\ @SubstMorphism ctx s s'' }.
  intros.
  exists (fromAll s').
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | AllSubst t s c => fun s' =>
                                            s' = AllSubst (fromAll s') /\
                                            SubstMorphism c (fromAll s')
                    | _ => fun _ => True
                  end Y
     with
       | SMall _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_HypSubst t ctx s s'
  : Injective (@SubstMorphism (CHyp ctx t) (HypSubst s) s') :=
  { result := exists s'', s' = HypSubst s'' /\ @SubstMorphism ctx s s'' }.
  intros.
  exists (fromHyp s').
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | HypSubst t s c => fun s' =>
                                            s' = HypSubst (fromHyp s') /\
                                            SubstMorphism c (fromHyp s')
                    | _ => fun _ => True
                  end Y
     with
       | SMhyp _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_TopSubst tus tvs s'
  : Injective (@SubstMorphism (CTop tus tvs) (TopSubst _ _) s') :=
  { result := s' = TopSubst tus tvs }.
  Proof.
    intros.
    refine
      (match H in @SubstMorphism C X Y
             return match X in ctx_subst C' return ctx_subst C' -> Prop with
                      | TopSubst _ _  => fun s' => s' = TopSubst _ _
                      | _ => fun _ => True
                    end Y
       with
         | SMtop _ _ => eq_refl
         | _ => I
       end).
  Defined.

  Global Instance Injective_SubstMorphism_ExsSubst ctx tes s s' sub
  : Injective (@SubstMorphism (CExs ctx tes) (ExsSubst sub s) s') :=
  { result := exists s'' sub',
                s' = ExsSubst sub' s''
                /\ (match @pctxD ctx sub
                        , SUBST.raw_substD ((getUVars ctx) ++ tes) (getVars ctx) s
                        , @pctxD ctx sub'
                        , SUBST.raw_substD ((getUVars ctx) ++ tes) (getVars ctx) s''
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
                /\ SubstMorphism sub sub'}.
  intros. exists (fst (fromExs s')). exists (snd (fromExs s')).
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | ExsSubst t s su c =>
                      fun s' =>
                        s' = ExsSubst (snd (fromExs s')) (fst (fromExs s')) /\
                        match pctxD su with
                          | Some _ =>
                            match
                              SUBST.raw_substD ((getUVars s) ++ t) (getVars s) c
                            with
                              | Some s1D =>
                                match pctxD (snd (fromExs s')) with
                                  | Some c2D =>
                                    match
                                      SUBST.raw_substD ((getUVars s) ++ t)
                                             (getVars s) (fst (fromExs s'))
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
                        SubstMorphism su (snd (fromExs s'))
                    | _ => fun _ => True
                  end Y
     with
       | SMexs _ _ _ _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Reflexive_SubstMorphism ctx
  : Reflexive (@SubstMorphism ctx).
  Proof.
    clear.
    red. induction x;
         simpl; intros; try constructor;
         forward; eauto.
    eapply Applicative_pctxD; eauto.
  Qed.

  Global Instance Transitive_SubstMorphism ctx
  : Transitive (@SubstMorphism ctx).
  Proof.
    clear.
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

  Lemma only_in_range_empty
  : forall x y, only_in_range x y amap_empty.
  Proof. clear. red; intros.
         exfalso. unfold amap_lookup, amap_empty in H.
         rewrite SUBST.FACTS.empty_o in H. congruence.
  Qed.

  (* Lemma WF_empty ctx : WellFormed_subst (@ctx_empty ctx). *)
  (* Proof. *)
  (*   induction ctx; simpl; intros; constructor; auto. *)
  (*   eapply SUBST.WellFormed_empty. *)
  (*   eapply only_in_range_empty. *)
  (* Qed. *)

  Lemma ctx_subst_eta ctx (s : ctx_subst ctx) :
    s = match ctx as ctx return ctx_subst ctx -> ctx_subst ctx with
          | CTop _ _ => fun _ => TopSubst _ _
          | CAll _ _ => fun s => AllSubst (fromAll s)
          | CHyp _ _ => fun s => HypSubst (fromHyp s)
          | CExs _ _ => fun s => ExsSubst (snd (fromExs s)) (fst (fromExs s))
        end s.
  Proof.
    clear. destruct s; reflexivity.
  Qed.

  Lemma AllSubst_fromAll ctx t (s : ctx_subst (CAll t ctx)) :
    AllSubst (fromAll s) = s.
  Proof.
    rewrite ctx_subst_eta. reflexivity.
  Qed.

(*
  Lemma ctx_substD_set' ctx
  : forall (uv : nat) (e : expr) (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
      forall ctx' s'
             (k : (nat -> option expr) -> ctx_subst ctx -> option (ctx_subst ctx'))
             f,
        (forall a b, k a b <> None) ->
        ctx_set' uv e s k = k f s' ->
        WellFormed_ctx_subst s' /\
        (ctx_lookup uv s = None ->
         forall (tus tvs : tenv typ) (t : typ) (val : exprT tus tvs (typD t))
                (get : hlist typD tus -> typD t) (sD : exprT tus tvs Prop) P,
           ctx_substD tus tvs s = Some sD ->
           nth_error_get_hlist_nth typD tus uv =
           Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) ->
           exprD' tus tvs e t = Some val ->
           exists (sD' : exprT tus tvs Prop) fD,
             InstantiateI.sem_preserves_if tus tvs fD f /\
             ctx_substD tus tvs s' = Some sD' /\
             SubstMorphism s s' /\
             (forall (us : hlist typD tus) (vs : hlist typD tvs),
                fD us vs ->
                ((P us vs /\ sD' us vs) <-> (P us vs /\ sD us vs /\ get us = val us vs)))).
  Proof.
    (* k takes input of a substitution and returns a substitution
     * The input substitution satisfies the property and the output
     * substitution must also satisfy the property
     *)
    (* if the input substitution satisfies the property then the output
     * substitution satisfies the "next" property
     *)
    (* k never fails *)
    (* i only know that the term is well-typed in the larger environment
     * the function checks when it tries to do the set
     *)

*)


  Lemma ctx_substD_set ctx
  : forall (uv : nat) (e : expr) (s s' : ctx_subst ctx),
      ctx_set uv e s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      (ctx_lookup uv s = None ->
       forall (tus tvs : tenv typ) (t : typ) (val : exprT tus tvs (typD t))
              (get : hlist typD tus -> typD t) (sD : exprT tus tvs Prop),
         ctx_substD tus tvs s = Some sD ->
         nth_error_get_hlist_nth typD tus uv =
         Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) ->
         exprD' tus tvs e t = Some val ->
         exists sD' : exprT tus tvs Prop,
           ctx_substD tus tvs s' = Some sD' /\
           SubstMorphism s s' /\
           (forall (us : hlist typD tus) (vs : hlist typD tvs),
              sD' us vs <-> sD us vs /\ get us = val us vs)).
  Proof.
    unfold ctx_set.
  Admitted.

  Global Instance SubstUpdateOk_ctx_subst ctx
  : SubstUpdateOk (SubstUpdate_ctx_subst ctx) (SubstOk_ctx_subst ctx) :=
  { substR := fun _ _ a b => SubstMorphism a b
  ; set_sound := _ }.
  Proof.
    intros. eapply ctx_substD_set; eauto.
  Defined.

  Require Import ExtLib.Data.ListFirstnSkipn.

  (** TODO: this seems to be the core problem!
   ** This proof relies on UIP (decidable) but there is probably a nicer
   ** formulation that doesn't.
   ** Granted, part of the problem is likely to be the fact that the
   ** all_convertible check is aweful.
   **)
  Lemma drop_exact_append_exact
  : forall ys xs,
    exists get,
      drop_exact (xs ++ ys) ys = Some (@existT _ _ xs get) /\
      forall a b, get (hlist_app a b) = a.
  Proof.
    clear - RTypeOk_typ. unfold drop_exact.
    intros. rewrite app_length.
    cutrewrite (length xs + length ys - length ys = length xs); [ | omega ].
    assert (length xs <= length xs) by omega.
    generalize (skipn_app_R _ (length xs) xs ys H).
    intro. replace (length xs - length xs) with 0 in H0; [ | omega ].
    simpl in *.
    cutrewrite (all_convertible (skipn (length xs) (xs ++ ys)) ys = true).
    { assert (firstn (length xs) (xs ++ ys) = xs).
      { rewrite firstn_app_L by omega.
        rewrite firstn_all; auto. }
      generalize dependent (length xs). intros.
      exists (match H1 in _ = Z return hlist _ _ -> hlist typD Z with
                | eq_refl => (fun x : hlist typD (xs ++ ys) =>
                                fst
                                  (hlist_split (firstn n (xs ++ ys)) (skipn n (xs ++ ys))
                                               match
                                                 eq_sym (firstn_skipn n (xs ++ ys)) in (_ = l)
                                                 return (hlist typD l)
                                               with
                                                 | eq_refl => x
                                               end))
              end).
      split.
      { destruct H1. reflexivity. }
      { intros. autorewrite with eq_rw.
        generalize dependent (firstn_skipn n (xs ++ ys)).
        generalize dependent (firstn n (xs ++ ys)).
        generalize dependent (skipn n (xs ++ ys)).
        intros; subst.
        admit. (** UIP **) } }
    { rewrite H0.
      clear - RTypeOk_typ. induction ys; auto; simpl; intros.
      rewrite type_cast_refl; eauto with typeclass_instances. }
  Qed.

  Lemma pctxD_substD
  : forall ctx (s : ctx_subst ctx) cD,
      WellFormed_subst s ->
      pctxD s = Some cD ->
      exists sD,
        substD (getUVars ctx) (getVars ctx) s = Some sD /\
        forall us vs, cD sD us vs.
  Proof.
    intros ctx s cD H; revert cD; induction H; simpl; intros.
    { inv_all; subst.
      rewrite rel_dec_eq_true; eauto with typeclass_instances.
      rewrite rel_dec_eq_true; eauto with typeclass_instances.
      simpl.
      eexists; split; eauto.
      simpl; auto. }
    { simpl in *. forward.
      specialize (IHWellFormed_ctx_subst _ eq_refl).
      inv_all. forward_reason. subst.
      destruct (drop_exact_append_exact (t :: nil) (getVars c)) as [ ? [ ? ? ] ].
      rewrite H1. rewrite H2.
      eexists; split; eauto.
      intros.
      generalize (H3 us vs); clear H3.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      do 6 red. intros.
      equivs; auto. rewrite H4. assumption. }
    { simpl in *; forward; inv_all; subst.
      specialize (IHWellFormed_ctx_subst _ eq_refl).
      inv_all. forward_reason. subst.
      eexists; split; eauto. intros.
      generalize (H3 us vs); clear H3.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      do 6 red. intros.
      equivs; auto. }
    { destruct (drop_exact_append_exact ts (getUVars c)) as [ ? [ ? ? ] ].
      rewrite H3.
      forward; inv_all; subst.
      specialize (IHWellFormed_ctx_subst _ eq_refl).
      forward_reason.
      change_rewrite H6.
      eexists; split; eauto.
      intros. generalize (H7 us vs); clear H7.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      do 6 red; intros. eapply _forall_sem. intros.
      split; auto. rewrite H4. equivs; assumption. }
  Qed.

End parameterized.

Arguments CTop {typ expr} _ _ : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.ExprDAs.
