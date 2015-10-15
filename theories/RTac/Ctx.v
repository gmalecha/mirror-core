Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.ListFirstnSkipn.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.BIMap.
Require Import MirrorCore.Instantiate.

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
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr typ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprVar_expr : ExprVar expr}.
  Context {ExprVarOk_expr : ExprVarOk _}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk _}.

  Local Instance RelDec_eq_typ : RelDec (@eq typ) :=
    RelDec_Rty _.
  Local Instance RelDecOk_eq_typ : RelDec_Correct RelDec_eq_typ :=
    @RelDec_Correct_Rty _ _ _.

  Inductive Ctx :=
  | CTop : tenv typ -> tenv typ -> Ctx
  | CAll : Ctx -> typ -> Ctx
  | CExs : Ctx -> tenv typ -> Ctx
  | CHyp : Ctx -> expr -> Ctx.

  Fixpoint CEx (c : Ctx) (t : typ) : Ctx :=
    CExs c (t :: nil).

  Fixpoint CAlls (c : Ctx) (ls : tenv typ) : Ctx :=
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
    clear. induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Lemma countUVars_getUVars : forall ctx, countUVars ctx = length (getUVars ctx).
    clear. induction ctx; simpl; auto.
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

  Fixpoint getExtensionUVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop tus _ => nil
      | CAll ctx' _ => getExtensionUVars ctx'
      | CExs ctx' ts => getExtensionUVars ctx' ++ ts
      | CHyp ctx' _ => getExtensionUVars ctx'
    end.

  Fixpoint getExtensionVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop tus _ => nil
      | CAll ctx' t => getExtensionVars ctx' ++ t :: nil
      | CExs ctx' _ => getExtensionVars ctx'
      | CHyp ctx' _ => getExtensionVars ctx'
    end.

  Theorem getUVars_split
  : forall ctx,
      getUVars ctx = getAmbientUVars ctx ++ getExtensionUVars ctx.
  Proof using.
    induction ctx; simpl; eauto.
    - symmetry. apply app_nil_r_trans.
    - rewrite <- app_ass_trans.
      f_equal; auto.
  Qed.

  Theorem getVars_split
  : forall ctx,
      getVars ctx = getAmbientVars ctx ++ getExtensionVars ctx.
  Proof using.
    induction ctx; simpl; eauto.
    - symmetry. apply app_nil_r_trans.
    - rewrite <- app_ass_trans.
      f_equal; auto.
  Qed.

  Lemma getEnvs'_getUVars_getVars
  : forall c a b,
      getEnvs' c a b  = (getUVars c ++ a, getVars c ++ b).
  Proof using.
    induction c; simpl; intros; auto.
    { rewrite IHc. f_equal. rewrite <- app_assoc. reflexivity. }
    { rewrite IHc. f_equal. rewrite <- app_assoc. reflexivity. }
  Qed.

  Lemma getEnvs_getUVars_getVars
  : forall c, getEnvs c = (getUVars c, getVars c).
  Proof using.
    unfold getEnvs. intros.
    rewrite getEnvs'_getUVars_getVars.
    change (list typ) with (tenv typ).
    f_equal; apply app_nil_r.
  Qed.

  Theorem getUVars_append
  : forall c1 c2,
      getAmbient c2 = getEnvs c1 ->
      getUVars (Ctx_append c1 c2) = getUVars c2.
  Proof using.
    induction c2; simpl; eauto.
    + rewrite getEnvs_getUVars_getVars. intros; inv_all; auto.
    + intro. rewrite IHc2; eauto.
  Defined.

  Theorem getVars_append
  : forall c1 c2,
      getAmbient c2 = getEnvs c1 ->
      getVars (Ctx_append c1 c2) = getVars c2.
  Proof using.
    induction c2; simpl; eauto.
    + rewrite getEnvs_getUVars_getVars. intros; inv_all; auto.
    + intro; rewrite IHc2; auto.
  Defined.
  (** End: Auxiliary Functions **)

  Inductive ctx_subst : Ctx -> Type :=
  | TopSubst : forall tus tvs, ctx_subst (CTop tus tvs)
  | AllSubst : forall {t c}, ctx_subst c -> ctx_subst (CAll c t)
  | HypSubst : forall {t c}, ctx_subst c -> ctx_subst (CHyp c t)
  | ExsSubst : forall {ts c}, ctx_subst c -> amap expr -> ctx_subst (CExs c ts).

  Definition fromAll {c t} (cs : ctx_subst (CAll c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CAll c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | @AllSubst _ _ c => c
      | _ => tt
    end.

  Definition fromHyp {c t} (cs : ctx_subst (CHyp c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CHyp c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | @HypSubst _ _ c => c
      | _ => tt
    end.

  Definition fromExs {c t} (cs : ctx_subst (CExs c t)) : amap expr * ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CExs c _ => amap expr * ctx_subst c
                   | _ => unit
                 end
    with
      | @ExsSubst _ _ c s => (s,c)
      | _ => tt
    end.

  Global Instance Injective_HypSubst h c s s'
  : Injective (@HypSubst h c s = @HypSubst h c s') :=
    { result := s = s' }.
  Proof. clear.
   refine (fun pf =>
             match pf in _ = Z
                   return match Z in ctx_subst c return ctx_subst c -> Prop with
                            | @HypSubst _ _ x => fun y => fromHyp y = x
                            | _ => fun _ => True
                          end (HypSubst s)
             with
               | eq_refl => eq_refl
             end).
  Defined.

  Global Instance Injective_AllSubst h c s s'
  : Injective (@AllSubst h c s = @AllSubst h c s') :=
    { result := s = s' }.
  Proof using.
   refine (fun pf =>
             match pf in _ = Z
                   return match Z in ctx_subst c return ctx_subst c -> Prop with
                            | @AllSubst _ _ x => fun y => fromAll y = x
                            | _ => fun _ => True
                          end (AllSubst s)
             with
               | eq_refl => eq_refl
             end).
  Defined.

(* TODO: These are redundant *)
  Lemma eta_ctx_subst_exs c ts (s : ctx_subst (CExs c ts))
  : exists y z, s = ExsSubst z y.
  Proof using.
    refine (match s in @ctx_subst X
                  return match X as X return @ctx_subst X -> Prop with
                           | CExs c ts => fun s =>
                             exists (y : _) (z : ctx_subst  c), s = ExsSubst z y
                           | _ => fun _ => True
                         end s
            with
              | @ExsSubst _ _ _ s => _
              | _ => I
            end).
    clear; eauto.
  Qed.

  Lemma eta_ctx_subst_hyp c ts (s : ctx_subst (CHyp c ts))
  : exists z, s = HypSubst z.
  Proof using.
    refine (match s in @ctx_subst X
                  return match X as X return @ctx_subst X -> Prop with
                           | CHyp c ts => fun s =>
                                            exists (z : ctx_subst  c), s = HypSubst z
                           | _ => fun _ => True
                         end s
            with
              | @HypSubst _ _ s => _
              | _ => I
            end).
    clear; eauto.
  Qed.

  Lemma eta_ctx_subst_all c ts (s : ctx_subst (CAll c ts))
  : exists z, s = AllSubst z.
  Proof using.
    refine (match s in @ctx_subst X
                  return match X as X return @ctx_subst X -> Prop with
                           | CAll c ts => fun s =>
                                            exists (z : ctx_subst  c), s = AllSubst z
                           | _ => fun _ => True
                         end s
            with
              | @AllSubst _ _ s => _
              | _ => I
            end).
    clear; eauto.
  Qed.

  Fixpoint ctx_lookup {c} (u : nat) (cs : ctx_subst c) : option expr :=
    match cs with
      | TopSubst _ _ => None
      | @AllSubst _ _ c => ctx_lookup u c
      | @HypSubst _ _ c => ctx_lookup u c
      | @ExsSubst _ _ c s =>
        match amap_lookup u s with
          | None => ctx_lookup u c
          | Some e => Some e
        end
    end.

  Definition valid_entry ctx (cs : ctx_subst ctx) (len : nat) (e : expr)
  : Prop :=
    mentionsAny (fun u' => if ctx_lookup u' cs then true
                           else u' ?[ ge ] (length (getUVars ctx) + len))
                (fun v' => v' ?[ ge ] (length (getVars ctx))) e = false.

  Definition WellFormed_entry ctx (cs : ctx_subst ctx) (len : nat) (m : amap expr)
  : Prop :=
    let min := length (getUVars ctx) in
    WellFormed_bimap min len (length (getVars ctx)) m /\
    (** instantiated with respect to bottom **)
    Forall_amap (fun k e => forall u'',
                              mentionsU u'' e = true ->
                              ctx_lookup u'' cs = None) m.

  Theorem WellFormed_entry_with_no_forward
  : forall ctx cs len m,
      @WellFormed_entry ctx cs len m ->
      let min := length (getUVars ctx) in
      WellFormed_bimap min len (length (getVars ctx)) m /\
      (** no forward pointers **)
      Forall_amap (fun _ e => valid_entry cs len e) m /\
      (** instantiated with respect to bottom **)
      Forall_amap (fun k e => forall u'',
                                mentionsU u'' e = true ->
                                ctx_lookup u'' cs = None) m.
  Proof using ExprOk_expr.
    destruct 1; simpl.
    split; auto. split; auto.
    destruct H as [ ? [ ? ? ] ]; auto.
    red. intros.
    specialize (H0 _ _ H3).
    specialize (H2 _ _ H3). simpl in *.
    red. red in H2.
    revert H2. eapply mentionsAny_weaken_strong; eauto.
    intros. rewrite H0. eauto.
    eauto.
  Qed.

  Lemma WellFormed_entry_amap_empty
  : forall ctx cs len,
      WellFormed_entry (ctx:=ctx) cs len (amap_empty expr).
  Proof using.
    red; intros.
    split.
    - eapply WellFormed_bimap_empty; eauto.
    - eapply Forall_amap_empty.
  Qed.

  Theorem WellFormed_entry_WellFormed_pre_entry
  : forall ctx cs ts s,
      @WellFormed_entry ctx cs ts s ->
      WellFormed_bimap (length (getUVars ctx)) ts (length (getVars ctx)) s.
  Proof using.
    unfold WellFormed_entry, WellFormed_bimap.
    intuition.
  Qed.

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
                    WellFormed_entry s (length ts) s' ->
                    WellFormed_ctx_subst s ->
                    WellFormed_ctx_subst (@ExsSubst ts c s s').

  Fixpoint ctx_domain {c} (cs : ctx_subst c) : list nat :=
    match cs with
      | TopSubst _ _ => nil
      | @AllSubst _ _ c => ctx_domain c
      | @HypSubst _ _ c => ctx_domain c
      | @ExsSubst _ _ c s =>
        ctx_domain c ++ amap_domain s
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
  Proof using.
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

  (** It is a bit annoying that these proofs require decidable equality on
   ** [typ] but the system requires that anyways
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
  Proof using RTypeOk_typ.
    unfold drop_exact.
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
        revert e. uip_all'. simpl.
        rewrite hlist_split_hlist_app. reflexivity. } }
    { rewrite H0.
      clear - RTypeOk_typ. induction ys; auto; simpl; intros.
      rewrite type_cast_refl; eauto with typeclass_instances. }
  Qed.

  Lemma drop_exact_sound
  : forall tus ts tus' cast,
      drop_exact tus ts = Some (@existT _ _ tus' cast) ->
      exists pf : tus' ++ ts = tus,
        forall a b, cast match pf in _ = tus return hlist _ tus with
                           | eq_refl => hlist_app a b
                         end = a.
  Proof using.
    unfold drop_exact. intros.
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

  Fixpoint ctx_substD {c} tus tvs (cs : ctx_subst c) {struct cs}
  : option (exprT tus tvs Prop) :=
    match cs with
      | TopSubst tus' tvs' =>
        if (tus ?[ eq ] tus') && (tvs ?[ eq ] tvs') then
          Some (fun _ _ => True)
        else
          None
      | @HypSubst _ _ c => ctx_substD tus tvs c
      | @AllSubst t _ c =>
        match drop_exact tvs (t :: nil) with
          | None => None
          | Some (existT _ tvs' get) =>
            match ctx_substD tus tvs' c with
              | None => None
              | Some sD => Some (fun us vs => sD us (get vs))
            end
        end
      | @ExsSubst ts _ c s =>
        match drop_exact tus ts with
          | None => None
          | Some (existT _ tus' get) =>
            match amap_substD tus tvs s
                , ctx_substD tus' tvs c
            with
              | Some sD' , Some sD =>
                Some (fun us vs => sD' us vs /\ sD (get us) vs)
              | None , _ => None
              | Some _ , None => None
            end
        end
    end.

  Section ctx_set_simple'.
    Variables (u : nat) (e : expr).

    Fixpoint ctx_set_simple' {c} (cs : ctx_subst c) {struct cs}
    : option (ctx_subst c * expr) :=
      match cs in ctx_subst c
            return option (ctx_subst c * expr)
      with
        | TopSubst _ _ => None
        | @AllSubst _ _ c =>
          match ctx_set_simple' c with
            | None => None
            | Some (c,e) => Some (AllSubst c, e)
          end
        | @HypSubst _ _ c =>
          match ctx_set_simple' c with
            | None => None
            | Some (c,e) => Some (HypSubst c, e)
          end
        | @ExsSubst ts ctx c s =>
          let (nus,nvs) := countEnvs ctx in
          if u ?[ ge ] nus then
            let max_nus := length ts + nus in
            if u ?[ lt ] max_nus then (** NOTE: this check is redundant **)
              if mentionsAny (fun x => x ?[ ge ] max_nus)
                             (fun x => x ?[ ge ] nvs) e then
                None
              else
                let e' := instantiate (fun u => ctx_lookup u cs) 0 e in
                (** NOTE: This actually instantiates the term twice **)
                match amap_check_set u e' s with
                  | None => None
                  | Some s' =>
                    match amap_lookup u s' with
                      | None => None
                      | Some e'' =>
                        Some (ExsSubst c s', e'')
                    end
                end
            else
              None
          else
            match ctx_set_simple' c with
              | None => None
              | Some (c,e) =>
                let inst := (fun u' => if u ?[ eq ] u' then Some e else None) in
                Some (@ExsSubst _ ctx c (amap_instantiate inst s), e)
            end
      end.
  End ctx_set_simple'.

  Definition ctx_set {c} (u : nat) (e : expr) (cs : ctx_subst c)
  : option (ctx_subst c) :=
    if u ?[ lt ] countUVars c then
      match ctx_set_simple' u e cs with
        | None => None
        | Some (s,_) => Some s
      end
    else
      None.

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

  Global Instance Injective_ExsSubst ts ctx a b c d
  : Injective (ExsSubst (ts:=ts)(c:=ctx) a b = ExsSubst c d) :=
    { result := a = c /\ b = d }.
  Proof using.
  intro pf.
  refine (match pf in _ = X return
                match X with
                  | @ExsSubst _ _ c d => fun a b => a = c /\ b = d
                  | _ => True
                end a b
          with
            | eq_refl => conj eq_refl eq_refl
          end).
  Defined.


  Global Instance Injective_WellFormed_ctx_subst_All c t s
  : Injective (WellFormed_ctx_subst (AllSubst (c:=c) (t:=t) s)) :=
  { result := WellFormed_ctx_subst s }.
  Proof using.
    refine (fun x =>
              match x in WellFormed_ctx_subst z
                    return match z return Prop with
                             | @AllSubst _ _ s => WellFormed_ctx_subst s
                             | _ => True
                           end
              with
                | @WF_AllSubst _ _ _ pf => pf
                | _ => I
              end).
  Defined.

  Global Instance Injective_WellFormed_ctx_subst_Hyp c t s
  : Injective (WellFormed_ctx_subst (HypSubst (c:=c) (t:=t) s)) :=
  { result := WellFormed_ctx_subst s }.
  Proof using.
    refine (fun x =>
              match x in WellFormed_ctx_subst z
                    return match z return Prop with
                             | @HypSubst _ _ s => WellFormed_ctx_subst s
                             | _ => True
                           end
              with
                | @WF_HypSubst _ _ _ pf => pf
                | _ => I
              end).
  Defined.

  Global Instance Injective_WellFormed_ctx_subst_Top tus tvs
  : Injective (WellFormed_ctx_subst (TopSubst tus tvs)) :=
  { result := True }.
  Proof using. trivial. Defined.

  Global Instance Injective_WellFormed_ctx_subst_ExsSubst ctx ts c s
  : Injective (WellFormed_ctx_subst (c:=CExs ctx ts) (ExsSubst c s)) :=
  { result := WellFormed_ctx_subst c /\
              WellFormed_entry c (length ts) s }.
  Proof using.
  intro.
  refine match H in @WellFormed_ctx_subst C s
               return match C as C return ctx_subst C -> Prop with
                        | CExs c0 ts => fun s' =>
                          let (s,c) := fromExs s' in
                          WellFormed_ctx_subst c /\
                          WellFormed_entry c (length ts) s
                        | _ => fun _ => True
                      end s
         with
           | @WF_ExsSubst t c s s' pfs' pfs => conj pfs pfs'
           | _ => I
         end.
  Defined.

  Lemma WellFormed_entry_WellFormed_amap
  : forall ctx (s : ctx_subst ctx) n s',
      WellFormed_entry s n s' ->
      WellFormed_amap s'.
  Proof using.
    destruct 1. eauto using WellFormed_bimap_WellFormed_amap.
  Qed.

  Theorem ctx_substD_lookup_gen ctx
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
      forall (uv : nat) (e : expr),
      ctx_lookup uv s = Some e ->
      forall (tus tvs : tenv typ) (sD : exprT tus tvs Prop)
             (C : exprT tus tvs Prop -> Prop)
             (App_C : CtxLogic.ExprTApplicative C),
        ctx_substD tus tvs s = Some sD ->
        exists (t : typ) (val : exprT tus tvs (typD t))
               (get : hlist typD tus -> typD t),
          nth_error_get_hlist_nth typD tus uv =
          Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) /\
          exprD' tus tvs e t = Some val /\
          (C (fun us vs =>
                sD us vs -> get us = val us vs)).
  Proof using RTypeOk_typ ExprOk_expr.
    induction 1; simpl; intros.
    { congruence. }
    { forward; inv_all; subst.
      eapply drop_exact_sound in H2.
      forward_reason.
      revert H1; subst.
      specialize (fun C Pure_C => @IHWellFormed_ctx_subst _ _ H0 _ _ _ C Pure_C H3).
      destruct (@IHWellFormed_ctx_subst (fun P => C (fun us vs => P us (fst (hlist_split _ _ vs))))); clear IHWellFormed_ctx_subst.
      { clear - App_C.
        constructor.
        { intros. eapply CtxLogic.exprTPure. eauto. }
        { intros P Q H. eapply CtxLogic.exprTAp. eauto. } }
      forward_reason.
      eapply exprD'_weakenV with (tvs' := t :: nil) in H2; eauto.
      forward_reason.
      do 3 eexists; split; eauto. split; eauto.
      intros. revert H4.
      eapply CtxLogic.exprTAp. eapply CtxLogic.exprTPure; intros.
      revert H7.
      rewrite <- (hlist_app_hlist_split _ _ vs).
      rewrite <- H5; clear H5.
      rewrite H6. assumption. }
    { eauto. }
    { forward; inv_all; subst.
      consider (amap_lookup uv s'); intros; inv_all; subst.
      { eapply amap_lookup_substD in H1; eauto.
        forward_reason.
        do 3 eexists; split; eauto. split; eauto.
        eapply CtxLogic.exprTPure. clear - H6.
        firstorder. }
      { eapply drop_exact_sound in H3.
        destruct H3. revert H3. subst.
        destruct (fun Pure_C => @IHWellFormed_ctx_subst _ _ H2 _ _ _ (fun P => C (fun us vs => P (fst (hlist_split _ _ us)) vs)) Pure_C H5).
        { clear - App_C. constructor.
          { intros. eapply CtxLogic.exprTPure. eauto. }
          { intros P Q H. eapply CtxLogic.exprTAp; eauto. } }
        forward_reason. intros.
        exists x0.
        eapply nth_error_get_hlist_nth_weaken with (ls' := ts) in H3.
        simpl in *. forward_reason.
        eapply exprD'_weakenU with (tus' := ts) in H6; eauto.
        forward_reason.
        do 2 eexists; split; eauto; split; eauto.
        revert H7.
        eapply CtxLogic.exprTAp. eapply CtxLogic.exprTPure. intros us vs ?.
        rewrite <- (hlist_app_hlist_split _ _ us).
        rewrite <- H10; clear H10.
        rewrite <- H9; clear H9. destruct 1.
        eapply H7. rewrite H8 in H10. assumption. } }
  Qed.

  Theorem ctx_substD_lookup ctx
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
      forall (uv : nat) (e : expr),
      ctx_lookup uv s = Some e ->
      forall (tus tvs : tenv typ) (sD : exprT tus tvs Prop),
        ctx_substD tus tvs s = Some sD ->
        exists (t : typ) (val : exprT tus tvs (typD t))
               (get : hlist typD tus -> typD t),
          nth_error_get_hlist_nth typD tus uv =
          Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) /\
          exprD' tus tvs e t = Some val /\
          (forall us vs,
             sD us vs -> get us = val us vs).
  Proof using RTypeOk_typ ExprOk_expr.
    intros.
    eapply ctx_substD_lookup_gen
      with (C := fun (P : exprT _ _ Prop) => forall us vs, P us vs); eauto.
    eapply CtxLogic.ExprTApplicative_foralls.
  Qed.

  Lemma ctx_subst_domain ctx
  : forall (s : ctx_subst ctx),
      WellFormed_ctx_subst s ->
      forall (ls : list nat),
        subst_domain s = ls ->
        forall n : nat, In n ls <-> subst_lookup n s <> None.
  Proof using.
    induction 1; simpl; intros; eauto using WellFormed_domain.
    { subst. split; auto. congruence. }
    { subst. rewrite in_app_iff.
      split; intro.
      { forward.
        destruct H1.
        { eapply IHWellFormed_ctx_subst in H1; eauto. }
        { eapply amap_domain_WellFormed in H1; eauto.
          eapply WellFormed_entry_WellFormed_amap; eauto. } }
      { rewrite IHWellFormed_ctx_subst; eauto.
        rewrite amap_domain_WellFormed; eauto.
        destruct (amap_lookup n s'); try solve [ right; congruence | left; assumption ].
        eapply WellFormed_entry_WellFormed_amap; eauto. } }
  Qed.

  Lemma ctx_lookup_mentions_range ctx
  : forall (s : ctx_subst ctx) (e : expr) (u : nat),
      WellFormed_ctx_subst s ->
      ctx_lookup u s = Some e ->
      mentionsAny (fun u' => u' ?[ ge ] length (getUVars ctx))
                  (fun v' => v' ?[ ge ] length (getVars ctx)) e = false.
  Proof using ExprOk_expr.
    induction 1; try solve [ simpl; intros; eauto; congruence ].
    { simpl. intros.
      eapply IHWellFormed_ctx_subst in H0; clear IHWellFormed_ctx_subst.
      revert H0. eapply mentionsAny_weaken.
      eassumption. eauto.
      clear. intros.
      consider (v ?[ ge ] length (getVars c ++ t :: nil)); auto.
      intros. rewrite rel_dec_eq_true in H; eauto with typeclass_instances.
      rewrite app_length in H0. omega. }
    { simpl. intros.
      consider (amap_lookup u s'); intros.
      { inv_all; subst.
        destruct H. destruct H as [ ? [ ? ? ] ].
        eapply H4 in H1. rewrite app_length. auto. }
      { eapply IHWellFormed_ctx_subst in H2.
        rewrite app_length.
        revert H2. eapply mentionsAny_weaken.
        eassumption.
        2: eauto.
        clear. intros.
        consider (u ?[ ge ] (length (getUVars c) + length ts)); auto.
        intros.
        rewrite rel_dec_eq_true in H; eauto with typeclass_instances. omega. } }
  Qed.

  Lemma WellFormed_amap'
  : forall m,
      WellFormed_amap m ->
      forall u u' e e',
        amap_lookup u' m = Some e' ->
        amap_lookup u m = Some e ->
        mentionsU u' e = false.
  Proof using.
    intros. red in H.
    red in H. red in H.
    consider (mentionsU u' e); auto.
    intro.
    eapply H in H2.
    - eapply FMapSubst.SUBST.PROPS.F.not_find_in_iff in H2.
      change_rewrite H2 in H0. congruence.
    - eapply FMapSubst.SUBST.FACTS.find_mapsto_iff. eassumption.
  Qed.

  Lemma ctx_lookup_normalized ctx
  : forall (s : ctx_subst ctx) (e : expr) (u : nat),
      WellFormed_ctx_subst s ->
      ctx_lookup u s = Some e ->
      forall (u' : nat) (e' : expr),
        ctx_lookup u' s = Some e' -> mentionsU u' e = false.
  Proof using ExprOk_expr.
    induction 1; try solve [ simpl; intros; try congruence; eauto ].
    { intro. simpl in H1.
      consider (amap_lookup u s').
      { do 3 intro. inv_all; subst.
        eapply WellFormed_entry_with_no_forward in H.
        destruct H as [ ? [ ? ? ] ]. clear H2.
        simpl. intros.
        consider (amap_lookup u' s').
        { intros; subst; inv_all; subst.
          eapply WellFormed_bimap_WellFormed_amap in H.
          eapply WellFormed_amap'; eauto. }
        { intro X; clear X.
          intro.
          eapply H3 in H1. specialize (H1 u').
          destruct (mentionsU u' e); try reflexivity.
          specialize (H1 eq_refl).
          congruence. } }
      { simpl. intros.
        forward_reason.
        consider (amap_lookup u' s'); [ | eauto ].
        intros; inv_all; subst.
        consider (mentionsU u' e); auto.
        intros; exfalso.
        generalize H2.
        eapply ctx_lookup_mentions_range in H2; eauto.
        intro.
        destruct H. clear H6. destruct H. destruct H6.
        eapply H6 in H3.
        eapply mentionsAny_false_mentionsU in H2; try eassumption.
        consider (u' ?[ ge ] length (getUVars c)); intros.
        congruence. omega. } }
  Qed.

  Global Instance SubstOk_ctx_subst ctx
  : @SubstOk (ctx_subst ctx) typ expr _ _ _ :=
  { WellFormed_subst := @WellFormed_ctx_subst ctx
  ; substD := @ctx_substD ctx
  }.
  { intros; eapply ctx_substD_lookup; eassumption. }
  { intros; eapply ctx_subst_domain; eassumption. }
  { intros; eapply ctx_lookup_normalized; eassumption. }
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
      | @HypSubst _ _ cs => HypSubst (ctx_subst_append s1 cs)
      | @AllSubst _ _ cs => AllSubst (ctx_subst_append s1 cs)
      | @ExsSubst _ _ cs s => ExsSubst (ctx_subst_append s1 cs) s
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
      | @AllSubst t ctx' s' =>
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
      | @ExsSubst ts ctx' s' sub =>
        match amap_substD (getUVars ctx' ++ ts) (getVars ctx') sub
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
      | @HypSubst h ctx' s' =>
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
  Proof using.
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
  Proof using.
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

  (** NOTE: This needs the generalized implementation of
   ** CtxLogic.ExprTApplicative
   **)
  Theorem Applicative_pctxD
  : forall ctx s C,
      @pctxD ctx s = Some C ->
      (forall us vs (P Q : exprT _ _ Prop),
         C (fun a b => P a b -> Q a b) us vs ->
         C P us vs ->
         C Q us vs) /\
      (forall us vs (Q : exprT _ _ Prop), (forall a b, Q a b) -> C Q us vs).
  Proof using.
    induction s; simpl; intros.
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
      { intros us vs P Q f.
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
  Proof using.
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
  Proof using.
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
                   , amap_substD ((getUVars c) ++ ts) (getVars c) s1
                   , @pctxD c cs2
                   , amap_substD ((getUVars c) ++ ts) (getVars c) s2
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
  Proof using.
    intros.
    generalize (@Proper_pctxD_impl c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma Fmap_pctxD_iff
  : forall c s C,
      @pctxD c s = Some C ->
      Proper (RexprT _ _ iff ==> RexprT _ _ iff)%signature C.
  Proof using.
    intros.
    generalize (@Proper_pctxD_iff c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Ltac gather_facts :=
    repeat match goal with
             | H : forall us vs, ?C _ us vs |- ?C _ ?us ?vs =>
               generalize (H us vs); clear H ;
               eapply Ap_pctxD; [ eassumption | ]
             | H : ?C _ ?us ?vs |- ?C _ ?us ?vs =>
               revert H; clear H ;
               eapply Ap_pctxD; [ eassumption | ]
           end.


  Lemma pctxD_SubstMorphism
  : forall ctx s s',
      @SubstMorphism ctx s s' ->
      forall C C',
      @pctxD ctx s = Some C ->
      @pctxD ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C P us vs -> C' P us vs.
  Proof using.
    induction 1; intros; simpl in *; forward; inv_all; subst; eauto.
    { eapply IHSubstMorphism; eauto. }
    { gather_facts.
      eapply IHSubstMorphism; try reflexivity.
      revert H3.
      eapply Ap_pctxD; eauto.
      eapply Pure_pctxD; eauto.
      intros.
      rewrite _forall_sem.
      rewrite _forall_sem in H3.
      intros; eauto. }
    { eapply IHSubstMorphism; eauto. }
  Qed.

  Global Instance Injective_SubstMorphism_AllSubst t ctx s s'
  : Injective (@SubstMorphism (CAll ctx t) (AllSubst s) s') :=
  { result := exists s'', s' = AllSubst s'' /\ @SubstMorphism ctx s s'' }.
  Proof using.
  intros.
  exists (fromAll s').
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | @AllSubst t s c => fun s' =>
                                            s' = AllSubst (fromAll s') /\
                                            SubstMorphism c (fromAll s')
                    | _ => fun _ => True
                  end Y
     with
       | @SMall _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_HypSubst t ctx s s'
  : Injective (@SubstMorphism (CHyp ctx t) (HypSubst s) s') :=
  { result := exists s'', s' = HypSubst s'' /\ @SubstMorphism ctx s s'' }.
  clear. intros.
  exists (fromHyp s').
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | @HypSubst t s c => fun s' =>
                                            s' = HypSubst (fromHyp s') /\
                                            SubstMorphism c (fromHyp s')
                    | _ => fun _ => True
                  end Y
     with
       | @SMhyp _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_TopSubst tus tvs s'
  : Injective (@SubstMorphism (CTop tus tvs) (TopSubst _ _) s') :=
  { result := s' = TopSubst tus tvs }.
  Proof using.
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
                        , amap_substD ((getUVars ctx) ++ tes) (getVars ctx) s
                        , @pctxD ctx sub'
                        , amap_substD ((getUVars ctx) ++ tes) (getVars ctx) s''
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
  Proof using.
  intros. exists (fst (fromExs s')). exists (snd (fromExs s')).
  refine
    (match H in @SubstMorphism C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | @ExsSubst t s su c =>
                      fun s' =>
                        s' = ExsSubst (snd (fromExs s')) (fst (fromExs s')) /\
                        match pctxD su with
                          | Some _ =>
                            match
                              amap_substD ((getUVars s) ++ t) (getVars s) c
                            with
                              | Some s1D =>
                                match pctxD (snd (fromExs s')) with
                                  | Some c2D =>
                                    match
                                      amap_substD ((getUVars s) ++ t)
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
       | @SMexs _ _ _ _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Reflexive_SubstMorphism ctx
  : Reflexive (@SubstMorphism ctx).
  Proof using.
    red. induction x;
         simpl; intros; try constructor;
         forward; eauto.
    eapply Applicative_pctxD; eauto.
  Qed.

  Global Instance Transitive_SubstMorphism ctx
  : Transitive (@SubstMorphism ctx).
  Proof using.
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

  Lemma ctx_subst_eta ctx (s : ctx_subst ctx) :
    s = match ctx as ctx return ctx_subst ctx -> ctx_subst ctx with
          | CTop _ _ => fun _ => TopSubst _ _
          | CAll _ _ => fun s => AllSubst (fromAll s)
          | CHyp _ _ => fun s => HypSubst (fromHyp s)
          | CExs _ _ => fun s => ExsSubst (snd (fromExs s)) (fst (fromExs s))
        end s.
  Proof using.
    destruct s; reflexivity.
  Qed.

  Lemma AllSubst_fromAll ctx t (s : ctx_subst (CAll t ctx)) :
    AllSubst (fromAll s) = s.
  Proof using.
    rewrite ctx_subst_eta. reflexivity.
  Qed.

  Lemma ctx_substD_envs
  : forall c (cs : ctx_subst c) tus tvs csD,
      ctx_substD tus tvs cs = Some csD ->
      (tus,tvs) = (getUVars c, getVars c).
  Proof using RTypeOk_typ.
    induction cs; simpl; intros; simpl; eauto.
    { consider (tus0 ?[ eq ] tus && tvs0 ?[ eq ] tvs); intros; try congruence.
      destruct H; subst; reflexivity. }
    { forward; subst.
      eapply drop_exact_sound in H0. destruct H0.
      clear H; subst tvs. eapply IHcs in H1. clear - H1.
      inv_all; subst; auto. }
    { forward; subst.
      eapply drop_exact_sound in H0. destruct H0.
      clear H; subst tus. eapply IHcs in H2. clear - H2.
      inv_all; subst; auto. }
  Qed.

  Lemma countEnvs'_spec
  : forall c a b,
      countEnvs' c a b = (length (getUVars c) + a, length (getVars c) + b).
  Proof using.
    induction c; simpl; intros; auto;
    rewrite IHc; rewrite app_length; f_equal; auto; simpl; omega.
  Qed.

  Lemma countEnvs_spec
  : forall c, countEnvs c = (length (getUVars c), length (getVars c)).
  Proof using.
    intros. unfold countEnvs. rewrite countEnvs'_spec.
    f_equal; omega.
  Qed.

  Lemma pctxD_substD
  : forall ctx (s : ctx_subst ctx) cD,
      WellFormed_subst s ->
      pctxD s = Some cD ->
      exists sD,
        ctx_substD (getUVars ctx) (getVars ctx) s = Some sD /\
        forall us vs, cD sD us vs.
  Proof using.
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
      rewrite H2.
      forward; inv_all; subst.
      specialize (IHWellFormed_ctx_subst _ eq_refl).
      forward_reason.
      change_rewrite H5.
      eexists; split; eauto.
      intros. generalize (H6 us vs); clear H6.
      eapply Fmap_pctxD_impl; eauto; try reflexivity.
      do 6 red; intros. eapply _forall_sem. intros.
      split; auto. rewrite H3. equivs; assumption. }
  Qed.

  Lemma WellFormed_entry_check_set
  : forall uv e s c (cs : ctx_subst c) nts s',
      amap_check_set uv e s = Some s' ->
      valid_entry cs nts e ->
      length (getUVars c) <= uv < length (getUVars c) + nts ->
      WellFormed_ctx_subst cs ->
      WellFormed_entry cs nts s ->
      WellFormed_entry cs nts s'.
  Proof using RTypeOk_typ ExprOk_expr.
    intros.
    eapply syn_check_set in H; eauto using WellFormed_entry_WellFormed_amap.
    red; intros.
    forward_reason.
    split. red. split; try eassumption.
    split.
    { red. intros. rewrite H6 in H7.
      consider (uv ?[ eq ] u); intros; subst.
      { auto. }
      { forward.
        destruct H3.
        destruct H3 as [ ? [ ? ? ] ].
        eapply H11. eauto. } }
    { red; intros.
      rewrite H6 in H7. clear H6.
      consider (uv ?[ eq ] u); intros; subst.
      { inv_all. subst.
        red in H0. red.
        eapply mentionsAny_complete_false in H0; try eassumption. destruct H0.
        eapply mentionsAny_complete_false; try eassumption.
        split.
        { intros.
          eapply mentionsU_instantiate in H7. destruct H7.
          { forward_reason.
            eapply H0 in H8. forward. }
          { forward_reason.
            eapply WellFormed_entry_WellFormed_pre_entry in H3.
            destruct H3 as [ ? [ ? ? ] ].
            eapply H11 in H7.
            red in H7.
            eapply mentionsAny_false_mentionsU in H7; eassumption. } }
        { intros.
          eapply mentionsV_instantiate_0 in H7; try eassumption. destruct H7.
          { eauto. }
          { destruct H7.
            forward_reason.
            eapply WellFormed_entry_WellFormed_pre_entry in H3.
            destruct H3 as [ ? [ ? ? ] ].
            eapply H11 in H8. red in H8.
            eapply mentionsAny_false_mentionsV in H8; eassumption. } } }
      { forward. inv_all; subst.
        red. eapply mentionsAny_complete_false; try eassumption.
        split.
        { intros. eapply mentionsU_instantiate in H8.
          destruct H8.
          { forward_reason. forward.
            eapply WellFormed_entry_WellFormed_pre_entry in H3.
            red in H3. destruct H3 as [ ? [ ? ? ] ].
            eapply H12 in H7. red in H7.
            eapply mentionsAny_false_mentionsU in H7; try eassumption. }
          { forward_reason. forward. inv_all; subst.
            eapply mentionsU_instantiate in H10. destruct H10; forward_reason.
            { red in H0.
              eapply mentionsAny_false_mentionsU in H0; try eassumption.
              forward. }
            { eapply WellFormed_entry_WellFormed_pre_entry in H3.
              destruct H3 as [ ? [ ? ? ] ].
              eapply H13 in H8. red in H8.
              eapply mentionsAny_false_mentionsU in H8; eassumption. } } }
        { intros. eapply mentionsV_instantiate_0 in H8; try eassumption.
          destruct H8.
          { eapply WellFormed_entry_WellFormed_pre_entry in H3.
            destruct H3 as [ ? [ ? ? ] ].
            eapply H10 in H7. red in H7.
            eapply mentionsAny_false_mentionsV in H7; eassumption. }
          { forward_reason. forward. inv_all; subst.
            eapply mentionsV_instantiate_0 in H10; try eassumption;
            destruct H10; forward_reason.
            { eapply mentionsAny_false_mentionsV in H0; eassumption. }
            { eapply WellFormed_entry_WellFormed_pre_entry in H3.
              destruct H3 as [ ? [ ? ? ] ].
              eapply H13 in H10.
              eapply mentionsAny_false_mentionsV in H10; eassumption. } } } } }
    { red. intros. rewrite H6 in H7; clear H6.
      consider (uv ?[ eq ] u); intros; subst.
      { inv_all; subst.
        eapply mentionsU_instantiate in H8.
        destruct H8; forward_reason.
        { red in H0.
          eapply mentionsAny_false_mentionsU in H0;
            [ | eassumption | eassumption ].
          forward. }
        { destruct H3. eapply H9 in H6. eauto. } }
      { forward. inv_all; subst.
        eapply mentionsU_instantiate in H8. destruct H8; forward_reason.
        { forward. destruct H3. eapply H11 in H7. eauto. }
        { forward. inv_all; subst.
          red in H0.
          eapply mentionsU_instantiate in H10; destruct H10; forward_reason.
          { eapply mentionsAny_false_mentionsU in H0; try eassumption.
            forward. }
          { destruct H3.
            eapply H12 in H8. eauto. } } } }
  Qed.

  Lemma sem_preserves_if_ho_ctx_lookup
  : forall ctx (s : ctx_subst ctx) cD,
      WellFormed_subst s ->
      pctxD s = Some cD ->
      sem_preserves_if_ho
        (fun P => forall us vs, cD P us vs)
        (fun u => subst_lookup u s).
  Proof using.
    intros.
    destruct (pctxD_substD H H0) as [ ? [ ? ? ] ].
    red. intros.
    eapply substD_lookup in H3; eauto.
    forward_reason.
    rewrite H4 in H3. inv_all. subst.
    eexists; split; eauto.
    intros. gather_facts.
    eapply Pure_pctxD; eauto.
  Qed.

  Lemma sem_preserves_if_ctx_lookup
  : forall ctx (s : ctx_subst ctx) cD,
      WellFormed_subst s ->
      ctx_substD (getUVars ctx) (getVars ctx) s = Some cD ->
      sem_preserves_if cD (fun u => subst_lookup u s).
  Proof using.
    intros. red. red. intros.
    eapply substD_lookup in H1; eauto.
    forward_reason.
    rewrite H2 in H1. inv_all; subst.
    eexists; split; eauto.
  Qed.

  Lemma WellFormed_entry_instantiate
  : forall s c f (cs : ctx_subst c) nts s',
      amap_instantiate f s = s' ->
      (forall u e,
         f u = Some e ->
         bimap_max (length (getUVars c)) (length (getVars c)) e /\
         forall u',
           mentionsU u' e = true ->
           ctx_lookup u' cs = None) ->
      WellFormed_ctx_subst cs ->
      WellFormed_entry cs nts s ->
      WellFormed_entry cs nts s'.
  Proof using ExprOk_expr.
    intros. split.
    { eapply WellFormed_bimap_instantiate; eauto.
      - clear - H0. intros.
        eapply H0 in H. destruct H.
        clear - H. red in H. eauto.
      - destruct H2. auto. }
    { eapply WellFormed_entry_with_no_forward in H2.
      destruct H2 as [ ? [ ? ? ] ].
      red; intros. subst.
      rewrite amap_lookup_amap_instantiate in H5.
      forwardy. inv_all; subst.
      eapply mentionsU_instantiate in H6. destruct H6.
      - destruct H5. eapply H4; eauto.
      - forward_reason.
        eapply H0 in H5; eauto. destruct H5.
        eauto. }
  Qed.

  Definition WellFormed_ctx_subst_sem c (cs : ctx_subst c) : Prop :=
    forall u e,
      ctx_lookup u cs = Some e ->
      (length (getAmbientUVars c) <= u < length (getUVars c)) /\
      mentionsAny (fun u' => if ctx_lookup u' cs then true
                             else u' ?[ ge ] (length (getUVars c)))
                  (fun v' => v' ?[ ge ] (length (getVars c))) e = false.

  Lemma getUVars_ge_getAmbientUVars
  : forall ctx, length (getAmbientUVars ctx) <= length (getUVars ctx).
  Proof using.
    induction ctx; simpl; intros; eauto.
    rewrite app_length. omega.
  Qed.

  Theorem WellFormed_ctx_subst_WellFormed_ctx_subst_sem
  : forall c cs,
      @WellFormed_ctx_subst c cs ->
      @WellFormed_ctx_subst_sem c cs.
  Proof using ExprOk_expr.
    induction 1; intros; red; simpl; intros; try congruence; eauto.
    { rename IHWellFormed_ctx_subst into IH.
      eapply IH in H0; clear IH.
      forward_reason. split; auto.
      revert H1. eapply mentionsAny_weaken; try eassumption. eauto.
      intro. rewrite app_length. simpl.
      consider (v ?[ ge ] (length (getVars c) + 1)); auto.
      intros. rewrite rel_dec_eq_true in H3; eauto with typeclass_instances.
      omega. }
    { consider (amap_lookup u s'); intros.
      { inv_all; subst.
        destruct H. destruct H. forward_reason.
        split.
        { eapply H3 in H1.
          generalize (getUVars_ge_getAmbientUVars c).
          rewrite app_length. omega. }
        generalize H1. eapply H4 in H1.
        intros.
        eapply mentionsAny_complete_false; try eassumption.
        split.
        { rewrite app_length.
          intros. specialize (H2 _ _ H5). simpl in H2.
          rewrite H2; try eassumption.
          do 2 red in H.
          red in H1.
          eapply mentionsAny_false_mentionsU in H1;
            [ | eassumption | eassumption ].
          rewrite H1.
          eapply H in H6.
          { eapply FMapSubst.SUBST.FACTS.not_find_in_iff in H6.
            change_rewrite H6. reflexivity. }
          { eapply FMapSubst.SUBST.FACTS.find_mapsto_iff.
            eapply H5. } }
        { intros.
          eapply mentionsAny_false_mentionsV in H1; eassumption. } }
      { clear H1.
        generalize (IHWellFormed_ctx_subst _ _ H2).
        rewrite app_length. split; try omega.
        forward_reason.
        revert H3.
        eapply mentionsAny_weaken_strong; [ eassumption | | trivial ].
        intros.
        forward.
        cutrewrite (amap_lookup u0 s' = None).
        { clear - H6.
          consider (u0 ?[ ge ] (length (getUVars c) + length ts)); auto.
          intro. rewrite rel_dec_eq_true in H6; eauto with typeclass_instances.
          omega. }
        clear H5 H6 H4 H1.
        eapply IHWellFormed_ctx_subst in H2.
        destruct H2.
        eapply mentionsAny_false_mentionsU in H2; try eassumption.
        forward.
        destruct H. consider (amap_lookup u0 s'); auto.
        intros.
        destruct H as [ ? [ ? ? ] ].
        eapply H7 in H6.
        exfalso.
        consider (u0 ?[ ge ] length (getUVars c)); try congruence.
        intros. omega. } }
  Qed.

  Lemma pctxD_SubstMorphism_progress
  : forall c (cs cs' : ctx_subst c),
      SubstMorphism cs cs' ->
      forall cD,
        pctxD cs = Some cD ->
        exists cD',
          pctxD cs' = Some cD'.
  Proof using.
    induction 1; simpl; intros; forward; inv_all; subst; eauto;
    rename IHSubstMorphism into IH;
    specialize (IH _ eq_refl);
    forward_reason; Cases.rewrite_all_goal; eauto.
  Qed.

  Lemma pctxD_substD' ctx (s : ctx_subst ctx) cD sD :
    WellFormed_ctx_subst s ->
    pctxD s = Some cD ->
    ctx_substD (getUVars ctx) (getVars ctx) s = Some sD ->
    forall us vs, cD sD us vs.
  Proof using RTypeOk_typ ExprOk_expr.
    intros. destruct (pctxD_substD H H0) as [ ? [ ? ? ] ].
    rewrite H1 in H2. inv_all; subst. auto.
  Qed.

  Lemma mentionsAny_only_lookup
  : forall c (cs : ctx_subst c) e,
      mentionsAny (fun x : uvar => if ctx_lookup x cs then true else false)
                  (fun _ : var => false) e = false ->
      forall u, mentionsU u e = true ->
                ctx_lookup u cs = None.
  Proof using ExprOk_expr.
    intros.
    eapply mentionsAny_complete_false in H; eauto.
    forward_reason.
    consider (ctx_lookup u cs); auto; intros.
    apply H in H0. rewrite H2 in H0. congruence.
  Qed.

  Lemma WellFormed_bimap_lookup_lt
  : forall a b c u m,
      WellFormed_bimap a b c m ->
      u < a ->
      amap_lookup u m = None.
  Proof using.
    intros. destruct H.
    consider (amap_lookup u m); auto; intros.
    destruct H1. apply H1 in H2. exfalso. omega.
  Qed.

  Lemma mentionsAny_conj_false
    : forall fv gv fu gu e,
      (mentionsAny fu fv e = false /\
       mentionsAny gu gv e = false) <->
      (mentionsAny (fun x => fu x || gu x) (fun x => fv x || gv x) e = false).
  Proof using ExprOk_expr.
    intros.
    repeat rewrite mentionsAny_complete_false by eauto.
    clear. intuition;
           repeat match goal with
                    | H : _ |- _ =>
                      erewrite H by eauto
                  end; auto.
    eapply H0 in H. eapply orb_false_iff in H. tauto.
    eapply H1 in H. eapply orb_false_iff in H. tauto.
    eapply H0 in H. eapply orb_false_iff in H. tauto.
    eapply H1 in H. eapply orb_false_iff in H. tauto.
  Qed.

  Lemma ctx_substD_set_simple' ctx
  : forall (uv : nat) (Huv : uv < length (getUVars ctx)) (e : expr)
           (s : ctx_subst ctx),
      WellFormed_subst s ->
      forall e' s',
      ctx_set_simple' uv e s = Some (s',e') ->
      uv < length (getUVars ctx) /\
      mentionsAny (fun x => x ?[ ge ] length (getUVars ctx))
                  (fun x => x ?[ ge ] length (getVars ctx)) e = false /\
      mentionsAny (fun x => x ?[ ge ] length (getUVars ctx))
                  (fun x => x ?[ ge ] length (getVars ctx)) e' = false /\
      mentionsAny (fun x => if ctx_lookup x s' then true else false)
                  (fun x => false) e' = false /\
      (** NOTE: This phrasing that requires equality is not very convenient.
       ** semantic equality might be better, ultimately ctx_subst is not very
       ** efficient
       **)
      (forall x, ctx_lookup x s' =
                 if x ?[ eq ] uv then Some e'
                 else match ctx_lookup x s with
                        | None => None
                        | Some e =>
                          Some (instantiate (fun u => if u ?[ eq ] uv then Some e' else None) 0 e)
                      end) /\
      WellFormed_subst s' /\
      (ctx_lookup uv s = None ->
       forall (tus tvs : tenv typ) (t : typ) (val : exprT tus tvs (typD t))
              (get : hlist typD tus -> typD t) (sD : exprT tus tvs Prop),
         ctx_substD tus tvs s = Some sD ->
         nth_error_get_hlist_nth typD tus uv =
         Some (existT (fun t0 : typ => hlist typD tus -> typD t0) t get) ->
         exprD' tus tvs e t = Some val ->
         exists (sD' : exprT tus tvs Prop) eD',
           ctx_substD tus tvs s' = Some sD' /\
           exprD' tus tvs e' t = Some eD' /\
           SubstMorphism s s' /\
           (forall us vs,
              sD' us vs -> val us vs = eD' us vs) /\
           (forall (us : hlist typD tus) (vs : hlist typD tvs),
              sD' us vs <-> sD us vs /\ get us = val us vs)).
  Proof using RTypeOk_typ ExprOk_expr.
    induction 2; simpl; intros; try congruence;
    try rename IHWellFormed_ctx_subst into IH.
    { (* All *)
      forwardy; inv_all; subst.
      eapply IH in H0; clear IH; forward_reason; try exact Huv.
      split; eauto.
      split.
      { rewrite app_length; simpl.
        clear - H1 ExprOk_expr.
        eapply mentionsAny_weaken; try eassumption.
        auto.
        simpl. clear.
        intros.
        eapply neg_rel_dec_correct in H.
        eapply neg_rel_dec_correct. omega. }
      split.
      { rewrite app_length; simpl.
        clear - H2 ExprOk_expr.
        eapply mentionsAny_weaken; try eassumption.
        auto.
        simpl. clear.
        intros.
        eapply neg_rel_dec_correct in H.
        eapply neg_rel_dec_correct. omega. }
      rename H2 into H1'.
      rename H3 into H2.
      rename H4 into H3.
      split; eauto.
      split.
      { simpl; auto. }
      split.
      { constructor. auto. }
      clear H2 H3.
      rename H5 into H2.
      rename H6 into H4.
      intros. forwardy; inv_all; subst.
      destruct (drop_exact_sound _ H5). revert H9. subst.
      intros.
      assert (exists val',
                exprD' tus x e t0 = Some val' /\
                forall us vs vs',
                  val us (hlist_app vs vs') = val' us vs).
      { eapply ctx_substD_envs in H8. inv_all; subst.
        cut (mentionsV (length (getVars c)) e = false).
        { intro.
          eapply exprD'_strengthenV_single in H7; eauto.
          forward_reason; eexists; split; eauto.
          intros.
          rewrite (hlist_eta vs').
          rewrite (hlist_eta (hlist_tl _)). eauto. }
        erewrite mentionsAny_mentionsV; eauto.
        eapply mentionsAny_weaken; [ eassumption | | | eauto ].
        reflexivity.
        simpl. clear.
        intros.
        eapply neg_rel_dec_correct in H.
        eapply neg_rel_dec_correct. omega. }
      forward_reason.
      eapply H4 in H8; eauto.
      forward_reason.
      simpl. rewrite H5. rewrite H8.
      eapply exprD'_weakenV with (tvs' := t :: nil) in H12; eauto.
      forward_reason.
      do 2 eexists; split; eauto.
      split; eauto.
      split.
      { constructor. eauto. }
      split.
      { intros. revert H17.
        rewrite <- (hlist_app_hlist_split _ _ vs).
        rewrite H9. intros.
        rewrite H11. rewrite H14; eauto. }
      { intros.
        rewrite <- (hlist_app_hlist_split _ _ vs).
        rewrite H9; clear H9.
        rewrite H11; clear H11.
        rewrite <- H15; clear H15.
        tauto. } }
    { (* Hyp *)
      forwardy; inv_all; subst.
      eapply IH in H0; clear IH; forward_reason; try exact Huv.
      split; eauto.
      split.
      { clear - H1 ExprOk_expr.
        eapply mentionsAny_weaken; try eassumption.
        auto.
        simpl. clear.
        intros.
        eapply neg_rel_dec_correct in H.
        eapply neg_rel_dec_correct. omega. }
      split.
      { clear - H2 ExprOk_expr.
        eapply mentionsAny_weaken; try eassumption.
        auto.
        simpl. clear.
        intros.
        eapply neg_rel_dec_correct in H.
        eapply neg_rel_dec_correct. omega. }
      rename H2 into H1'.
      rename H3 into H2.
      rename H4 into H3.
      split; eauto.
      split.
      { simpl; auto. }
      split.
      { constructor. auto. }
      clear H2 H3.
      rename H5 into H2.
      rename H6 into H4.
      intros. forwardy; inv_all; subst.
      forward_reason.
      eapply H4 in H5; eauto.
      forward_reason.
      do 2 eexists.
      split; eauto.
      split; eauto.
      split. constructor; auto.
      auto. }
    { (* Exs *)
      forward.
      consider (uv ?[ ge ] n).
      { clear IH.
        rewrite countEnvs_spec in H1.
        inv_all; subst; intros.
        forward; inv_all; subst.
        split; auto.
        split.
        { rewrite app_length.
          rewrite Plus.plus_comm. assumption. }
        rewrite and_assoc.
        assert (Hve : valid_entry s (length ts)
                                  (instantiate
                                     (fun u : uvar =>
                                        match amap_lookup u s' with
                                          | Some e0 => Some e0
                                          | None => ctx_lookup u s
                                        end) 0 e)).
        { (** VALID ENTRY **)
          red. clear H4.
          eapply mentionsAny_complete_false.
          eassumption.
          split.
          { intros.
            eapply mentionsU_instantiate in H4. destruct H4.
            { forward_reason. forward.
              eapply mentionsAny_false_mentionsU in H6;
                [ | eassumption | eassumption ].
              rewrite Plus.plus_comm. eapply H6. }
            { forward_reason.
              consider (amap_lookup x s'); intros.
              { inv_all; subst.
                eapply WellFormed_entry_with_no_forward in H.
                forward_reason.
                eapply H8 in H4. red in H4.
                eapply mentionsAny_false_mentionsU in H4;
                  [ | eassumption | eassumption ]. eauto. }
              { eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
                eapply H0 in H8. destruct H8.
                eapply mentionsAny_false_mentionsU in H9;
                  [ | eassumption | eassumption ].
                destruct (ctx_lookup u s); auto.
                consider (u ?[ ge ] (length (getUVars c) + length ts)); auto.
                intros.
                rewrite rel_dec_eq_true in H9; eauto with typeclass_instances.
                omega. } } }
          { intros.
            eapply mentionsV_instantiate_0 in H4; try eassumption. destruct H4.
            { eapply mentionsAny_false_mentionsV in H3;
              eassumption. }
            { forward_reason.
              consider (amap_lookup x s'); intros.
              { inv_all; subst.
                eapply WellFormed_entry_with_no_forward in H.
                forward_reason.
                eapply H8 in H6. red in H6.
                eapply mentionsAny_false_mentionsV in H6; eassumption. }
              { eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
                eapply H0 in H8.
                destruct H8.
                eapply mentionsAny_false_mentionsV in H9; eauto. } } } }
        split.
        { generalize H. intro SAVE_WF.
          eapply WellFormed_entry_check_set in H; eauto.
          { 
            apply and_comm.
            eapply mentionsAny_conj_false. simpl.
            eapply mentionsAny_complete_false; eauto.
            eapply WellFormed_entry_with_no_forward in H.
            forward_reason.
            split.
            { intros.
              consider (amap_lookup u a); simpl; intros.
              { exfalso.
                red in H. forward_reason.
                red in H.
                specialize (H uv e'). red in H.
                eapply H in H8.
                { apply H8. red. exists e0.
                  eapply FMapSubst.SUBST.FACTS.find_mapsto_iff.
                  apply H9. }
                { eapply FMapSubst.SUBST.FACTS.find_mapsto_iff. eauto. } }
              { consider (ctx_lookup u s); simpl; intros.
                { exfalso.
                  eapply H7 in H5.
                  eapply H5 in H8. congruence. }
                { eapply H6 in H5.
                  red in H5.
                  eapply mentionsAny_false_mentionsU in H5; [ | eauto | eauto ].
                  rewrite H10 in H5.
                  rewrite app_length. assumption. } } }
            { (* what do I know about variables? *)
              clear H6 H7.
              eapply syn_check_set in H4;
                [ | eassumption
                | eauto using WellFormed_entry_WellFormed_amap ].
              forward_reason.
              rewrite H7 in H5; clear H7.
              rewrite rel_dec_eq_true in H5 by eauto with typeclass_instances.
              inv_all. subst.
              intros.
              eapply mentionsV_instantiate_0 in H5; [ | eauto ].
              destruct H5.
              { eapply mentionsV_instantiate_0 in H5; [ | eauto ].
                destruct H5.
                { eapply mentionsAny_complete_false in H3; [ | eauto ].
                  destruct H3. eauto. }
                { destruct H5. forward_reason.
                  consider (amap_lookup x s'); intros; inv_all; subst.
                  { eapply WellFormed_entry_with_no_forward in SAVE_WF.
                    destruct SAVE_WF as [ ? [ ? ? ] ].
                    eapply H10 in H7. red in H7.
                    eapply mentionsAny_false_mentionsV in H7. eapply H7.
                    assumption. assumption. }
                  { eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
                    red in H0. eapply H0 in H9.
                    destruct H9.
                    eapply mentionsAny_false_mentionsV in H8.
                    3: eassumption. eapply H8. eassumption. } } }
              { destruct H. clear H.
                forward_reason.
                eapply WellFormed_entry_with_no_forward in SAVE_WF.
                destruct SAVE_WF as [ ? [ ? ? ] ].
                eapply H11 in H5.
                red in H5.
                eapply mentionsAny_false_mentionsV in H5.
                3: eassumption. eassumption. assumption. } } }
          { omega. } }
        generalize H4; intro SAVED.
        split.
        { simpl. intros.
          eapply syn_check_set in SAVED;
          eauto using WellFormed_entry_WellFormed_amap.
          forward_reason.
          rewrite H8.
          consider (uv ?[ eq ] x); intros; subst.
          { rewrite rel_dec_eq_true; eauto with typeclass_instances.
            rewrite H8 in H5. clear H8.
            rewrite rel_dec_eq_true in H5; eauto with typeclass_instances. }
          { rewrite rel_dec_neq_false; eauto with typeclass_instances.
            consider (amap_lookup x s').
            { intros.
              f_equal. f_equal.
              (** TODO: Should prove this extensional **)
              eapply FunctionalExtensionality.functional_extensionality.
              intros. rewrite H8 in H5.
              rewrite rel_dec_eq_true in H5; eauto with typeclass_instances.
              inv_all; subst.
              rewrite rel_dec_sym; eauto with typeclass_instances. }
            { intros.
              consider (ctx_lookup x s); auto; intros.
              clear H8.
              eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
              eapply H0 in H11. f_equal.
              forward_reason.
              rewrite instantiate_noop; auto.
              intros. consider (u ?[ eq ] uv); intros; subst; auto.
              eapply mentionsAny_false_mentionsU in H11;
                [ | eassumption | eassumption ].
              forward. consider (uv ?[ ge ] length (getUVars c)); try congruence. } } }
        assert (SAVED_WF : WellFormed_ctx_subst (ExsSubst (ts:=ts) s a)).
        { constructor; eauto.
          eapply WellFormed_entry_check_set in H; eauto. omega. }
        split; try eassumption.
        intros.
        Definition hide (T : Prop) : Prop := T.
        change (WellFormed_ctx_subst (ExsSubst s a))
        with   (hide (WellFormed_ctx_subst (ExsSubst (ts:=ts) s a))) in SAVED_WF.
        Opaque hide.
        forward; inv_all; subst.
        apply drop_exact_sound in H10; forward_reason.
        revert H7. subst. intros.
        generalize (ctx_substD_envs _ H12); intros; inv_all; subst.
        destruct (drop_exact_append_exact ts (getUVars c)) as [ ? [ ? ? ] ].
        simpl. Cases.rewrite_all_goal.
        (** STOPPED HERE **)
        eapply (@instantiate_sound_ho typ expr _ _ _
                       (getUVars c ++ ts) (getVars c)
                       (fun u : uvar =>
                          match amap_lookup u s' with
                            | Some e0 => Some e0
                            | None => ctx_lookup u s
                          end) e nil t) in H9;
          [ | | eapply (@sem_preserves_if_substD)
                  with (Subst_subst:=Subst_ctx_subst _)
                       (s:=ExsSubst (ts:=ts) s s') ].
        forward_reason.
        Focus 4. simpl. rewrite H10. rewrite H11.
        rewrite H12. reflexivity.
        3: constructor; eauto.
        forward_reason.
        unfold amap_check_set in H4.
        eapply FMapSubst.SUBST.substD_set in H4; try eassumption.
        { forward_reason.
          generalize H11; intros SAVED'.
          eapply H16 in H11; eauto.
          forward_reason. change_rewrite H11.
          eapply FMapSubst.SUBST.substD_lookup in H5; eauto.
          forward_reason.
          rewrite H5 in H8. inv_all. subst.
          Cases.rewrite_all_goal.
          do 2 eexists; split; eauto; split; eauto.
          split.
          { constructor; try reflexivity.
            forward.
            eapply H16 in H20; eauto.
            forward_reason.
            change_rewrite H20.
            eapply Pure_pctxD; eauto.
            intros. eapply H21 in H22. tauto. }
          { clear - H15 H17 H19 H7 H13.
            split; intros. 
            { intuition. rewrite <- H19; auto.
              eapply H17 in H0.
              destruct H0. rewrite H0; clear H0.
              eapply (H15 us vs (conj H H1) Hnil). }
            { rewrite H17.
              specialize (H13 (fst (hlist_split _ _ us)) (snd (hlist_split _ _ us))).
              specialize (H7 (fst (hlist_split _ _ us)) (snd (hlist_split _ _ us))).
              do 2 rewrite <- and_assoc.
              eapply and_cancel.
              intro. rewrite and_comm.
              rewrite hlist_app_hlist_split in H7.
              rewrite hlist_app_hlist_split in H13.
              rewrite H7 ; rewrite H13.
              eapply and_cancel. intros.
              rewrite <- H13 in H0.
              specialize (H15 us vs (conj H H0) Hnil).
              simpl in H15. rewrite H15. reflexivity. } } }
        { eapply WellFormed_entry_WellFormed_amap; eauto. }
        { eapply CtxLogic.ExprTApplicative_foralls_impl. } }
      { (** Use the inductive hypothesis **)
        rewrite countEnvs_spec in H1. inv_all; subst; auto; intros.
        forwardy; inv_all; subst.
        eapply IH in H1; clear IH.
        2: omega.
        forward_reason.
        rewrite app_length.
        split.
        { omega. }
        split.
        { clear - H3 ExprOk_expr.
          eapply mentionsAny_weaken; try eassumption.
          simpl. clear.
          intros.
          eapply neg_rel_dec_correct in H.
          eapply neg_rel_dec_correct. omega.
          simpl. auto. }
        split.
        { clear - H4 ExprOk_expr.
          eapply mentionsAny_weaken; try eassumption.
          simpl. clear.
          intros.
          eapply neg_rel_dec_correct in H.
          eapply neg_rel_dec_correct. omega.
          simpl. auto. }
        split.
        { rewrite Proper_mentionsAny. 2: eauto.
          4: reflexivity.
          3: instantiate (1 := fun x => (fun _ => false) x || (fun _ => false) x); reflexivity.
          Focus 2.
          instantiate (1 := fun u =>
                              (fun u => if amap_lookup u s' then true else false) u
                           || (fun u => if ctx_lookup u c0 then true else false) u).
          clear. red; simpl; intros. subst.
          rewrite amap_lookup_amap_instantiate.
          destruct (amap_lookup y s'); auto.
          erewrite mentionsAny_factor; eauto.
          change_rewrite H5.
          rewrite orb_false_r.
          eapply mentionsAny_complete_false; eauto.
          eapply mentionsAny_complete_false in H5; eauto.
          clear H8. forward_reason.
          split; auto.
          intros.
          clear H2.
          erewrite WellFormed_bimap_lookup_lt. reflexivity.
          destruct H. eassumption.
          eapply mentionsAny_complete_false in H4; eauto.
          destruct H4.
          eapply H2 in H9.
          consider (u ?[ ge ] length (getUVars c)); auto.
          intros; congruence.
          intros. omega. }
        split.
        { clear H8. simpl; intros.
          specialize (H6 x).
          rewrite H6; clear H6.
          rewrite amap_lookup_amap_instantiate.
          consider (x ?[ eq ] uv); intros; subst.
          { erewrite WellFormed_bimap_lookup_lt; eauto.
            destruct H. eassumption. }
          { destruct (amap_lookup x s').
            * f_equal. eapply Proper_instantiate; eauto.
              red. intros. subst.
              rewrite rel_dec_sym; eauto with typeclass_instances.
            * reflexivity. } }
        split.
        { constructor; auto.
          clear H8.
          destruct H; split; auto.
          { eapply WellFormed_bimap_instantiate; try eassumption.
            reflexivity.
            simpl. intros; forward. }
          { eapply Forall_amap_instantiate.
            2: eapply H8.
            simpl. intros.
            eapply mentionsU_instantiate in H10. destruct H10; forward_reason.
            { forward.
              rewrite H6. rewrite H9; eauto.
              rewrite rel_dec_neq_false; eauto with typeclass_instances. }
            { forward. inv_all; subst.
              eapply mentionsAny_false_mentionsU in H5; try eassumption.
              forward. } } }
        clear H5.
        intros; inv_all; subst.
        forward. inv_all; subst.
        simpl.
        rewrite H12.
        eapply drop_exact_sound in H12; destruct H12.
        revert H9. subst.
        assert (exists val',
                exprD' x tvs e t = Some val' /\
                forall us us' vs,
                  val (hlist_app us us') vs = val' us vs).
        { eapply ctx_substD_envs in H14; inv_all; subst.
          cut (forall u : nat,
                 u < length ts -> mentionsU (length (getUVars c) + u) e = false).
          { intro.
            eapply exprD'_strengthenU_multi in H9; eauto.
            forward_reason; eexists; split; eauto. }
          intros.
          erewrite mentionsAny_mentionsU; [ | eauto ].
          eapply mentionsAny_weaken; [ eassumption | | | eauto ].
          2: reflexivity.
          simpl. clear.
          intros.
          eapply neg_rel_dec_correct in H.
          eapply neg_rel_dec_correct. omega. }
        forward_reason.
        assert (uv < length (getUVars c)) by omega.
        generalize (ctx_substD_envs _ H14); intros; inv_all; subst.
        destruct (@nth_error_get_hlist_nth_appL _ typD ts _ _ H15) as [ ? [ ? ? ] ].
        rewrite H17 in H10.
        forward_reason; inv_all; subst; simpl in *.
        eapply H8 in H19; eauto; clear H8.
        forward_reason.
        change_rewrite H8.
        clear H3 H4 H6.
        eapply exprD'_weakenU with (tus' := ts) in H10; eauto.
        forward_reason.

        generalize H13; intro SAVED.
        eapply amap_instantiates_substD
          with (f := fun u' : nat => if uv ?[ eq ] u' then Some e' else None)
          in H13.
        2: eauto. 3: destruct H; eauto.
        Focus 3.
        instantiate (1 := fun P =>
                            forall us vs,
                              x1 us = x2 us vs ->
                              forall us', P (hlist_app us us') vs).
        red. intros. forward.
        inv_all; subst.
        rewrite H10 in H17. inv_all; subst.
        eexists; split; eauto.
        intros. rewrite H20. rewrite <- H4. assumption.
        Focus 2.
        clear. constructor. intros. eauto.
        intros. eauto.

        forward_reason.
        rewrite H3.
        rewrite H6.
        do 2 eexists; split; [ eauto | split; eauto ].
        split.
        { constructor; eauto.
          rewrite SAVED.
          forward; inv_all; subst.
          destruct (@pctxD_SubstMorphism_progress _ _ _ H19 _ H13).
          rewrite H23.
          intros.
          generalize (pctxD_substD' H7 H23 H8); intro.
          gather_facts.
          eapply Pure_pctxD; eauto.
          intros.
          specialize (H21 _ _ H24).
          specialize (H10 us0 vs0).
          eapply H22 in H24.
          destruct H24.
          rewrite <- H21 in *; clear H21.
          eapply H10; eauto. }
        split.
        { intros.
          destruct H13. specialize (H10 (h us) vs).
          specialize (H21 _ _ H23).
          revert H10 H23 H21.
          rewrite <- (hlist_app_hlist_split _ _ us).
          rewrite H18; clear H18. rewrite <- H4; clear H4.
          rewrite H22; clear H22.
          intros. rewrite H12. auto. }
        { intros. rewrite H22.
          rewrite and_comm. symmetry.
          repeat rewrite <- and_assoc.
          rewrite and_comm.
          repeat rewrite <- and_assoc.
          eapply and_iff. reflexivity.
          rewrite <- (hlist_app_hlist_split _ _ us).
          rewrite H18; clear H18.
          rewrite H20; clear H20. intro.
          rewrite H12; clear H12.
          eapply and_iff. reflexivity.
          intro.
          eapply H10.
          rewrite <- H21. assumption.
          apply H22. tauto. } } }
  Qed.

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
    intros. forward; inv_all; subst.
    rewrite countUVars_getUVars in H.
    eapply ctx_substD_set_simple' in H2; eauto.
    forward_reason.
    split; eauto. intros.
    eapply H7 in H8; eauto.
    forward_reason. eexists; split; eauto.
  Qed.

  Global Instance SubstUpdateOk_ctx_subst ctx
  : SubstUpdateOk (ctx_subst ctx) typ expr :=
  { substR := fun _ _ a b => SubstMorphism a b
  ; set_sound := _ }.
  Proof.
    intros. eapply ctx_substD_set; eauto.
  Defined.

  Lemma substD_pctxD
  : forall ctx (s s' : ctx_subst ctx) sD s'D,
      WellFormed_subst s ->
      pctxD s' = Some s'D ->
      (** Maybe it is nicer to have the substitution include the propositions *)
      ctx_substD (getUVars ctx) (getVars ctx) s = Some sD ->
      exists cD,
        pctxD s = Some cD /\
        forall us vs, cD sD us vs.
  Proof using RTypeOk_typ.
    intros ctx s s' cD c'D H; revert cD s' c'D; induction H; simpl; intros.
    { rewrite rel_dec_eq_true in * by eauto with typeclass_instances.
      rewrite rel_dec_eq_true in * by eauto with typeclass_instances.
      simpl in *.
      eexists; split; eauto.
      inv_all; subst; simpl; auto. }
    { destruct (eta_ctx_subst_all s'); subst.
      simpl in *. forward.
      inv_all; subst.
      eapply drop_exact_sound in H3.
      forward_reason.
      generalize x1. intros; inv_all; subst.
      specialize (@IHWellFormed_ctx_subst _ _ _ H0 H4).
      forward_reason.
      Cases.rewrite_all_goal.
      eexists; split; eauto.
      simpl; intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros.
      specialize (H1 vs0 (Hcons x2 Hnil)).
      revert H3.
      generalize dependent (hlist_app vs0 (Hcons x2 Hnil)).
      generalize dependent (getVars c ++ t :: nil).
      intros; subst.
      revert H3. uip_all'. tauto. }
    { destruct (eta_ctx_subst_hyp s'); subst.
      simpl in *. forward; inv_all; subst.
      eapply IHWellFormed_ctx_subst in H1; clear IHWellFormed_ctx_subst; eauto.
      forward_reason.
      Cases.rewrite_all_goal.
      eexists; split; eauto.
      simpl; intros; gather_facts.
      eapply Pure_pctxD; eauto. }
    { destruct (eta_ctx_subst_exs s'0) as [ ? [ ? ? ] ]; subst.
      simpl in *. forward; inv_all; subst.
      eapply drop_exact_sound in H5.
      destruct H5. generalize x2; intros; inv_all; subst.
      eapply IHWellFormed_ctx_subst in H3; eauto.
      forward_reason.
      change_rewrite H3.
      eexists; split; eauto.
      simpl.
      intros. gather_facts.
      eapply Pure_pctxD; eauto.
      intros. eapply _forall_sem; intros.
      split; auto. revert H4. revert H2. clear - RTypeOk_typ.
      uip_all'.
      intro X; rewrite X. assumption. }
  Qed.

  Definition remembers (ctx : Ctx) (cs : ctx_subst ctx)
             (ts : tenv typ) (m : amap expr)
  : ctx_subst (CExs ctx ts) :=
    @ExsSubst ts ctx cs (amap_instantiate (fun u => ctx_lookup u cs) m).

  Theorem remembers_sound
  : forall ctx (cs : ctx_subst ctx) ts m cs',
      @remembers ctx cs ts m = cs' ->
      WellFormed_ctx_subst cs ->
      WellFormed_bimap (length (getUVars ctx)) (length ts) (length (getVars ctx)) m ->
      WellFormed_ctx_subst cs' /\
      forall tus tvs csD mD,
        ctx_substD tus tvs cs = Some csD ->
        amap_substD (tus ++ ts) tvs m = Some mD ->
        exists cs'D,
          ctx_substD (tus ++ ts) tvs cs' = Some cs'D /\
          (forall us us' vs,
             (csD us vs /\ mD (hlist_app us us') vs) <-> cs'D (hlist_app us us') vs).
  Proof using ExprOk_expr RTypeOk_typ.
    unfold remembers. simpl; intros; subst.
    split.
    { constructor; eauto.
      red. generalize H1. red in H1.
      intro SAVED.
      split.
      { eapply WellFormed_bimap_instantiate; eauto.
        simpl. intros.
        eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
        red in H0.
        eapply H0 in H. forward_reason.
        revert H2. eapply mentionsAny_weaken; try eassumption.
        intros. forward. auto. }
      { red. intros.
        rewrite amap_lookup_amap_instantiate in H.
        forward. inv_all; subst.
        eapply mentionsU_instantiate in H2. destruct H2.
        - tauto.
        - forward_reason.
          eapply WellFormed_ctx_subst_WellFormed_ctx_subst_sem in H0.
          red in H0.
          eapply H0 in H2.
          forward_reason.
          specialize (H0 u'').
          consider (ctx_lookup u'' cs); auto; intros.
          specialize (H9 _ eq_refl).
          exfalso. eapply mentionsAny_false_mentionsU in H4; try eassumption.
          simpl in H4. rewrite H0 in H4. congruence. } }
    { simpl; intros.
      destruct (drop_exact_append_exact ts tus) as [ ? [ ? ? ] ].
      change_rewrite H3.
      rewrite H.
      generalize (ctx_substD_envs _ H). intro.
      inv_all; subst.
      change (getUVars ctx ++ ts) with (getUVars (CExs ctx ts)) in H2.
      change (getVars ctx) with (getVars (CExs ctx ts)) in H2.
      eapply amap_instantiates_substD with (f:=fun u : nat => ctx_lookup u cs) in H2.
      2: eassumption.
      2: eapply CtxLogic.ExprTApplicative_foralls_impl.
      2: solve [ eauto ].
      2: instantiate (1 := fun us vs => csD (x us) vs).
      { forward_reason.
        change_rewrite H2.
        eexists; split; eauto.
        simpl.
        intros.
        rewrite H4. symmetry. rewrite and_comm.
        eapply and_iff. reflexivity.
        intros. symmetry. eapply H5.
        rewrite H4. assumption. }
      { red. intros.
        eapply ctx_substD_lookup in H5; eauto.
        forward_reason. simpl.
        eapply exprD'_weakenU with (tus' := ts) in H7; eauto.
        forward_reason.
        simpl in *.
        eapply nth_error_get_hlist_nth_weaken with (ls' := ts) in H5.
        simpl in *. forward_reason.
        rewrite H6 in *. inv_all; subst.
        eexists; split; eauto.
        intros.
        clear - H4 H5 H10 H9 H8.
        specialize (H8 (fst (hlist_split _ _ us)) vs).
        specialize (H10 (fst (hlist_split _ _ us)) (snd (hlist_split _ _ us))).
        specialize (H9 (fst (hlist_split _ _ us)) vs (snd (hlist_split _ _ us))).
        revert H5.
        rewrite <- (hlist_app_hlist_split _ _ us).
        rewrite H4. intro X; specialize (H8 X).
        rewrite (hlist_app_hlist_split _ _ us) in *.
        congruence. } }
  Qed.

  Lemma Ctx_append_assoc : forall (c1 c2 c3 : Ctx),
                             Ctx_append c1 (Ctx_append c2 c3) =
                             Ctx_append (Ctx_append c1 c2) c3.
  Proof using.
    induction c3; simpl; auto; rewrite IHc3; auto.
  Qed.

  Lemma getUVars_Ctx_append
  : forall c1 c2,
      getUVars (Ctx_append c1 c2) = getUVars c1 ++ getExtensionUVars c2.
  Proof using.
    induction c2; simpl; intros; auto.
    symmetry. apply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.

  Lemma getVars_Ctx_append
  : forall c1 c2,
      getVars (Ctx_append c1 c2) = getVars c1 ++ getExtensionVars c2.
  Proof using.
    induction c2; simpl; intros; auto.
    symmetry. apply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.

  Definition hlist_getUVars_Ctx_append (c1 c2 : Ctx)
  : hlist typD (getUVars (Ctx_append c1 c2)) ->
    hlist typD (getUVars c1) :=
    fun hs =>
      fst (hlist_split _ _
                       match getUVars_Ctx_append c1 c2 in _ = Z
                             return hlist _ Z with
                         | eq_refl => hs
                       end).

  Definition hlist_getVars_Ctx_append (c1 c2 : Ctx)
  : hlist typD (getVars (Ctx_append c1 c2)) ->
    hlist typD (getVars c1) :=
    fun hs =>
      fst (hlist_split _ _
                       match getVars_Ctx_append c1 c2 in _ = Z
                             return hlist _ Z with
                         | eq_refl => hs
                       end).


  Fixpoint hlist_getAmbientUVars (c2 : Ctx) {struct c2}
  : hlist typD (getUVars c2) -> hlist typD (getAmbientUVars c2) :=
    match c2 as c2
          return hlist typD (getUVars c2) -> hlist typD (getAmbientUVars c2)
    with
      | CTop _ _ => fun x => x
      | CAll c2 _ => hlist_getAmbientUVars c2
      | CExs _ _ => fun us => hlist_getAmbientUVars _ (fst (hlist_split _ _ us))
      | CHyp c2 _ => hlist_getAmbientUVars c2
    end.

  Fixpoint hlist_getExtensionUVars (c2 : Ctx) {struct c2}
  : hlist typD (getUVars c2) -> hlist typD (getExtensionUVars c2) :=
    match c2 as c2
          return hlist typD (getUVars c2) -> hlist typD (getExtensionUVars c2)
    with
      | CTop _ _ => fun x => Hnil
      | CAll c2 _ => hlist_getExtensionUVars c2
      | CExs c2 _ => fun us => hlist_app (hlist_getExtensionUVars c2 (fst (hlist_split _ _ us))) (snd (hlist_split _ _ us))
      | CHyp c2 _ => hlist_getExtensionUVars c2
    end.

  Fixpoint hlist_getAmbientVars (c2 : Ctx) {struct c2}
  : hlist typD (getVars c2) -> hlist typD (getAmbientVars c2) :=
    match c2 as c2
          return hlist typD (getVars c2) -> hlist typD (getAmbientVars c2)
    with
      | CTop _ _ => fun x => x
      | CExs c2 _ => hlist_getAmbientVars c2
      | CAll _ _ => fun us => hlist_getAmbientVars _ (fst (hlist_split _ _ us))
      | CHyp c2 _ => hlist_getAmbientVars c2
    end.

  Fixpoint hlist_getExtensionVars (c2 : Ctx) {struct c2}
  : hlist typD (getVars c2) -> hlist typD (getExtensionVars c2) :=
    match c2 as c2
          return hlist typD (getVars c2) -> hlist typD (getExtensionVars c2)
    with
      | CTop _ _ => fun x => Hnil
      | CExs c2 _ => hlist_getExtensionVars c2
      | CAll c2 _ => fun us => hlist_app (hlist_getExtensionVars c2 (fst (hlist_split _ _ us))) (snd (hlist_split _ _ us))
      | CHyp c2 _ => hlist_getExtensionVars c2
    end.


  Lemma pctxD_get_hyp
  : forall (ctx ctx' : Ctx) e
           (s : ctx_subst (Ctx_append (CHyp ctx e) ctx')) sD,
      WellFormed_subst s ->
      pctxD s = Some sD ->
      exists eD,
        propD (getUVars ctx) (getVars ctx) e = Some eD /\
        forall us vs,
          sD (fun us vs => eD (hlist_getUVars_Ctx_append _ _ us)
                              (hlist_getVars_Ctx_append _ _ vs)) us vs.
  Proof using.
    induction ctx'; simpl.
    { intros e s; rewrite (ctx_subst_eta s).
      simpl. intros; forward; inv_all; subst; eauto.
      eexists; split; eauto. intros.
      eapply Pure_pctxD; eauto.
      unfold hlist_getUVars_Ctx_append, hlist_getVars_Ctx_append. simpl.
      clear.
      intros.
      do 2 rewrite <- hlist_app_nil_r.
      do 2 rewrite hlist_split_hlist_app.
      assumption. }
    { intros e s; rewrite (ctx_subst_eta s).
      simpl. intros; forward; inv_all; subst; eauto.
      generalize H0; eapply IHctx' in H0; clear IHctx'; eauto.
      forward_reason. intros.
      eexists; split; eauto.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      clear.
      unfold hlist_getUVars_Ctx_append, hlist_getVars_Ctx_append. simpl.
      unfold eq_ind_r, eq_ind, eq_rect.
      intros.
      match goal with
        | H : ?X _ ?Y |- ?X _ ?Z =>
          cutrewrite (Z = Y); auto
      end.
      clear.
      generalize dependent (getVars_Ctx_append (CHyp ctx e) ctx').
      generalize dependent (getVars (Ctx_append (CHyp ctx e) ctx')).
      intros; subst. simpl.
      generalize (hlist_app_hlist_split _ _ vs).
      intro H. rewrite <- H. rewrite H at 2.
      rewrite hlist_app_assoc.
      simpl.
      generalize dependent (app_ass_trans (getVars ctx) (getExtensionVars ctx') (t :: nil)).
      generalize dependent (hlist_app
                     (snd
                        (hlist_split (getVars ctx) (getExtensionVars ctx') vs))
                     (Hcons x0 Hnil)).
      clear. simpl in *.
      generalize dependent ((getVars ctx ++ getExtensionVars ctx') ++ t :: nil).
      intros; subst. simpl.
      rewrite hlist_split_hlist_app. reflexivity. }
    { intros e s; rewrite (ctx_subst_eta s).
      simpl; intros; forward; inv_all; subst; eauto.
      generalize H1.
      eapply IHctx' in H1; eauto.
      forward_reason.
      intro. eexists; split; eauto.
      intros. gather_facts.
      eapply Pure_pctxD; eauto.
      intros.
      eapply _forall_sem. intros.
      revert H1. clear.
      unfold hlist_getUVars_Ctx_append, hlist_getVars_Ctx_append.
      simpl in *. unfold eq_ind_r, eq_ind, eq_rect, eq_rec.
      match goal with
        | |- _ ?X _ -> _ ?Y _ => cutrewrite (X = Y); auto
      end.
      generalize (getUVars_Ctx_append (CHyp ctx e) ctx').
      intro.
      generalize dependent (getUVars (Ctx_append (CHyp ctx e) ctx')).
      intros; subst. simpl.
      rewrite <- (hlist_app_hlist_split _ _ us0).
      rewrite hlist_app_assoc.
      rewrite Eq.match_eq_sym_eq.
      do 2 rewrite hlist_split_hlist_app.
      reflexivity. }
    { intros e0 s; rewrite (ctx_subst_eta s).
      simpl; intros; forward; inv_all; subst; eauto.
      generalize H1.
      eapply IHctx' in H1; eauto.
      forward_reason.
      intro. eexists; split; eauto.
      intros. gather_facts.
      eapply Pure_pctxD; eauto. }
  Qed.

  Lemma getEnvs'_getAmbient
  : forall (ctx : Ctx) a b,
    exists tus' tvs',
      getEnvs' ctx a b = (fst (getAmbient ctx) ++ tus' ++ a,
                          snd (getAmbient ctx) ++ tvs' ++ b).
  Proof using.
    induction ctx; simpl; intros; eauto.
    { exists nil. exists nil. reflexivity. }
    { destruct (IHctx a (t :: b)) as [ ? [ ? ? ] ].
      rewrite H.
      exists x. exists (x0 ++ t :: nil).
      f_equal. f_equal. rewrite app_ass. reflexivity. }
    { destruct (IHctx (t ++ a) b) as [ ? [ ? ? ] ].
      rewrite H.
      exists (x ++ t). exists x0.
      f_equal. f_equal. rewrite app_ass; reflexivity. }
  Qed.

  Lemma getEnvs_getAmbient
  : forall (ctx : Ctx),
    exists tus' tvs',
      getEnvs ctx = (fst (getAmbient ctx) ++ tus',
                     snd (getAmbient ctx) ++ tvs').
  Proof using.
    unfold getEnvs. intros.
    generalize (getEnvs'_getAmbient ctx nil nil).
    eapply exists_impl; intro.
    eapply exists_impl; intro.
    etransitivity. eassumption.
    do 2 rewrite app_nil_r_trans.
    reflexivity.
  Qed.

  Lemma propD_weaken_by_Ctx_append
  : forall ctx ctx' p pD,
      getAmbient ctx' = getEnvs ctx ->
      propD (getUVars ctx) (getVars ctx) p = Some pD ->
      exists p'D,
        propD (getUVars (Ctx_append ctx ctx')) (getVars (Ctx_append ctx ctx')) p = Some p'D /\
        forall us vs,
          pD (hlist_getUVars_Ctx_append _ _ us)
             (hlist_getVars_Ctx_append _ _ vs) <-> p'D us vs.
  Proof using ExprOk_expr.
    intros ctx ctx' p pD H.
    unfold hlist_getUVars_Ctx_append, hlist_getVars_Ctx_append.
    generalize (getUVars_Ctx_append ctx ctx').
    generalize (getVars_Ctx_append ctx ctx').
    generalize (getVars (Ctx_append ctx ctx')).
    generalize (getUVars (Ctx_append ctx ctx')).
    intros; subst.
    unfold propD in *.
    eapply exprD'_typ0_weaken with (tus' := getExtensionUVars ctx')
                                   (tvs' := getExtensionVars ctx') in H0.
    destruct H0 as [ ? [ ? ? ] ].
    eexists; split; eauto.
    intros.
    rewrite <- (hlist_app_hlist_split _ _ vs).
    rewrite <- (hlist_app_hlist_split _ _ us).
    rewrite <- H1.
    do 2 rewrite hlist_app_hlist_split. reflexivity.
  Qed.

  Lemma getAmbient_Ctx_append
  : forall (ctx ctx' : Ctx),
      getAmbient (Ctx_append ctx ctx') = getAmbient ctx.
  Proof using.
    induction ctx'; eauto.
  Qed.

  Lemma only_in_range_0_empty
  : forall a am, only_in_range a 0 am ->
                 UVarMap.MAP.Equal am (@amap_empty expr).
  Proof using.
    unfold only_in_range. red.
    intros.
    specialize (H y). unfold amap_lookup in *.
    rewrite FMapSubst.SUBST.FACTS.empty_o.
    destruct (UVarMap.MAP.find y am); auto.
    exfalso. specialize (H _ eq_refl). omega.
  Qed.

  Lemma only_in_range_0_WellFormed_pre_entry
  : forall a c am, only_in_range a 0 am -> WellFormed_bimap a 0 c am.
  Proof using.
    unfold only_in_range. red.
    intros.
    eapply only_in_range_0_empty in H.
    split.
    { red. intros.
      exfalso. rewrite H in H0.
      eapply FMapSubst.SUBST.FACTS.empty_mapsto_iff in H0.
      assumption. }
    split.
    { eapply Forall_amap_Proper. 2: eauto.
      instantiate (1 := fun (k : uvar) (_ : expr) => a <= k < a + 0).
      reflexivity.
      eapply Forall_amap_empty. }
    { eapply Forall_amap_Proper. 2: eauto.
      eapply Reflexive_pointwise. eauto with typeclass_instances.
      eapply Forall_amap_empty. }
  Qed.

  Lemma only_in_range_0_substD
  : forall tus tvs a am,
      only_in_range a 0 am ->
      exists sD,
        amap_substD tus tvs am = Some sD /\
        forall us vs, sD us vs.
  Proof using.
    intros.
    generalize (FMapSubst.SUBST.Proper_amap_substD tus tvs (only_in_range_0_empty H)).
    destruct (FMapSubst.SUBST.substD_empty tus tvs) as [ ? [ ? ? ] ].
    unfold amap_substD.
    destruct (FMapSubst.SUBST.raw_substD tus tvs am).
    { simpl. eexists; split; eauto.
      intros. eapply H2. trivial. }
    { simpl. destruct 1. }
  Qed.

End parameterized.

Ltac gather_facts :=
  repeat match goal with
           | H : forall us vs, ?C _ us vs |- ?C _ ?us ?vs =>
             generalize (H us vs); clear H ;
             eapply Ap_pctxD; [ eassumption | ]
           | H : ?C _ ?us ?vs |- ?C _ ?us ?vs =>
             revert H; clear H ;
             eapply Ap_pctxD; [ eassumption | ]
         end.

Arguments CTop {typ expr} _ _ : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.ExprDAs.
Export MirrorCore.VariablesI.
Export MirrorCore.RTac.BIMap.