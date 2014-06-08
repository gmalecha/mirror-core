Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Structures.Functor.
Require Import MirrorCore.Poly.TypeI.
Require Import MirrorCore.Poly.Ctx.
Require Import MirrorCore.Poly.ML.

Set Implicit Arguments.
Set Strict Implicit.

Module Ext : MLExt.
  Definition ext : Type := unit.
  Definition kindof_ext (e : ext) : option kind0 :=
    Some kTy0.
  Definition extD (e : ext) : match kindof_ext e with
                                | Some k => kind0D' k
                                | None => unit
                              end :=
    match e with
      | tt => nat
    end.
  Definition ext_eq (a b : ext) : option (a = b) :=
    Some (match a as a , b as b return a = b with
            | tt , tt => eq_refl
          end).
End Ext.

Module MLtypes := ML Ext (* ContextHList *).

(** NOTE: This precludes any environments! **)
Record SymVal : Type :=
{ Typ : MLtypes.typ1
; Value : match MLtypes.typD1 nil Typ kTy1 with
            | None => Empty_set
            | Some T => MLtypes.Ctx.eval_Ctx T (MLtypes.Ctx.Env_nil _)
          end
}.

(** Definition of expression extensions **)
Module Type ExprExt.

  Parameter ext : Type.
  Parameter typeof_ext : ext -> option MLtypes.typ1.
  Parameter extD : forall e : ext,
                     match typeof_ext e with
                       | Some T =>
                         match MLtypes.typD1 nil T kTy1 with
                           | None => Empty_set
                           | Some T => MLtypes.Ctx.eval_Ctx T (MLtypes.Ctx.Env_nil _)
                         end
                       | None => unit
                     end.
End ExprExt.


Module Expr (EExt : ExprExt).
  Import MLtypes.

  Inductive expr : Type :=
  | eApp  : expr -> expr -> expr
  | eAbs  : typ0 -> expr -> expr
  | eVar  : nat -> expr
  | eTApp : expr -> typ0 -> expr
  | eExt  : EExt.ext -> expr.

  Section typeof_expr.
    Variable ks : list kind0.

    Fixpoint typeof_expr  (tvs : list typ0) (e : expr) : option typ1.
      refine
        match e with
          | eApp f x =>
            match typeof_expr tvs f
                , typeof_expr tvs x
            with
              | Some (tLift (tArr d r)) , Some (tLift d') =>
                if typ0_eq d d' then Some (tLift r) else None
              | _ , _ => None
            end
          | eAbs t e =>
            match typeof_expr (cons t tvs) e with
              | Some (tLift r) => Some (tLift (tArr t r))
              | _ => None
            end
          | eVar v => fmap tLift (List.nth_error tvs v)
          | eTApp e t =>
            match typeof_expr tvs e with
              | Some t'' =>
                match t'' with
                  | tPi k t' =>
                    match kindof_typ0 ks t with
                      | Some k'' =>
                        match k'' with
                          | kTy0 => Some (typ1_sub t' 0 t)
                          | _ => None
                        end
                      | None => None
                    end
                  | _ => None
                end
              | _ => None
            end
          | eExt e =>
            match EExt.typeof_ext e with
              | Some ty => Some ty
              | None => None
            end
        end.
    Defined.
  End typeof_expr.

  Module Env <: ContextP.
    Definition iT := typ0.
  End Env.

  Definition typD1' (ks : list kind0) (ctxK : Ctx.Env kind0D' ks) (t : typ1)
  : U1 :=
    match @typD1 ks t kTy1 return U1 with
      | None => Empty_set
      | Some T => Ctx.eval_Ctx T ctxK
    end.

  Definition typD0' (ks : list kind0) (ctxK : Ctx.Env kind0D' ks) (t : typ0)
  : U0 :=
    match @typD0 ks t kTy0 return U0 with
      | None => Empty_set
      | Some T => Ctx.eval_Ctx T ctxK
    end.


  Module CtxT := ContextHList Env.
  Existing Instance CtxT.Applicative_Ctx.
  Existing Instance CtxT.Functor_Ctx.

  Section exprD.
    Variable ks : list kind0.

    (** These have a good phase split, but it seems useful to have
     ** the context immediately to avoid the need to repeatedly destruct the
     ** types.
     **)
    Definition TCtx (ts : list typ0) (T : Ctx.Env kind0D' ks -> Type) : Type :=
      @Ctx.DCtx kind0D' ks (fun kenv => CtxT.Ctx (typD0' kenv) ts (T kenv)).

    Definition TCtxT1 (ts : list typ0) (T : typ1) :=
      TCtx ts (fun ctx => typD1' ctx T).

    Definition TCtxT0 (ts : list typ0) (T : typ0) :=
      TCtx ts (fun ctx => typD0' ctx T).


    Definition Inj_TCtxT {ts t} (val : typD1' (Ctx.Env_nil _) t)
    : TCtxT1 ts t.
      red. eapply Ctx.dpure; intro.
      eapply Applicative.pure.
      generalize (typD1_weaken nil ks t); simpl.
      revert val.
      unfold typD1'.
      refine (match typD1 nil t kTy1 as X
                    return match X with
                             | Some T => Ctx.eval_Ctx T (Ctx.Env_nil kind0D')
                             | None => Empty_set
                           end ->
                           match X with
                             | Some T =>
                               match typD1 ks t kTy1 with
                                 | Some T' =>
                                   Ctx.DCtx
                                     (fun env : Ctx.Env kind0D' nil =>
                                        Ctx.eval_Ctx T env ->
                                        Ctx.DCtx
                                          (fun env' : Ctx.Env kind0D' ks =>
                                             Ctx.eval_Ctx T' (hlist_app env env')))
                                 | None => Empty_set
                               end
                             | None => unit
                           end ->
                           match typD1 ks t kTy1 with
                             | Some T => Ctx.eval_Ctx T x
                             | None => Empty_set
                           end
              with
                | Some c => fun X =>
                              match typD1 ks t kTy1 as Y
                                    return match Y with
                                             | Some T' =>
                                               Ctx.DCtx
                                                 (fun env : Ctx.Env kind0D' nil =>
                                                    Ctx.eval_Ctx c env ->
                                                    Ctx.DCtx
                                                      (fun env' : Ctx.Env kind0D' ks =>
                                                         Ctx.eval_Ctx T' (hlist_app env env')))
                                             | None => Empty_set
                                           end ->
                                           match Y with
                                             | Some T => Ctx.eval_Ctx T x
                                             | None => Empty_set
                                           end
                              with
                                | Some _ => fun Y => _
                                | None => fun x => match x with end
                              end
                | None => fun x => match x with end
              end).
      eapply Ctx.dap. 2: eapply Y. 2: eapply X.
      simpl. eapply Ctx.dpure. refine (fun _ x => x).
    Defined.
    (**
    Eval cbv beta iota zeta delta [ Inj_TCtxT Ctx.dpure Ctx.dap Applicative.pure Applicative.ap CtxT.Applicative_Ctx CtxT.dpure CtxT.dap ] in @Inj_TCtxT.
    **)

    Definition App1_TCtxT {tvs t' t} :
      TCtxT1 tvs (tLift (tArr t' t)) ->
      TCtxT1 tvs (tLift t') ->
      TCtxT1 tvs (tLift t).
    Proof.
      unfold TCtxT1, TCtx. unfold typD1'. simpl.
      destruct (typD0 ks t' kTy0).
      { destruct (typD0 ks t kTy0).
        { intros.
          eapply Ctx.dap. 2: eapply X.
          eapply Ctx.dap. 2: eapply X0.
          eapply Ctx.dpure.
          intros.
          eapply Applicative.ap. 2: eapply X1.
          eapply Applicative.ap. 2: eapply X2.
          eapply Applicative.pure.
          refine (fun x => x). }
        { refine (fun x _ => x). } }
      { refine (fun f _ => Ctx.dap _ f).
        clear.
        eapply Ctx.dpure. intros.
        eapply Functor.fmap. eauto with typeclass_instances. 2: eapply X.
        refine (fun x => match x with end). }
    Defined.

    Definition App_TCtxT {tvs t' t} :
      TCtxT0 tvs (tArr t' t) ->
      TCtxT0 tvs t' ->
      TCtxT0 tvs t.
    Proof.
      unfold TCtxT0, TCtx. unfold typD0'. simpl.
      destruct (typD0 ks t' kTy0).
      { destruct (typD0 ks t kTy0).
        { intros.
          eapply Ctx.dap. 2: eapply X.
          eapply Ctx.dap. 2: eapply X0.
          eapply Ctx.dpure.
          intros.
          eapply Applicative.ap. 2: eapply X1.
          eapply Applicative.ap. 2: eapply X2.
          eapply Applicative.pure.
          compute. refine (fun x => x). }
        { refine (fun x _ => x). } }
      { refine (fun f _ => Ctx.dap _ f).
        clear.
        eapply Ctx.dpure. intros.
        eapply Functor.fmap. eauto with typeclass_instances. 2: eapply X.
        refine (fun x => match x with end). }
    Defined.

(*
    Axiom typD_weaken'
    : forall ks ks' tvs t,
        Ctx.DCtx
          (fun x : Ctx.Env skindD ks =>
             CtxT.Ctx tvs
                      match typD ks t kTy with
                        | Some T => Ctx.eval_Ctx T x
                        | None => Empty_set
                      end ->
             Ctx.DCtx (fun y : Ctx.Env ks' =>
                         CtxT.Ctx tvs
                                  match typD (ks ++ ks') t kTy with
                                    | Some T => Ctx.eval_Ctx T (hlist_app x y)
                                    | None => Empty_set
                                  end)).
*)


    Lemma not_lt_false a b c (H : false = a ?[ lt ] b)
    : false = (a + c) ?[ lt ] b.
      refine (match (a + c) ?[ lt ] b as X return (a + c) ?[ lt ] b = X -> false = X with
                | true => fun pf => match _ in False with end
                | false => fun _ => eq_refl
              end eq_refl).
      admit.
    Defined.

    Definition plus_comm_assoc_trans a b c : a + b + c = a + (c + b) :=
      match NPeano.Nat.eq_dec (a + b + c) (a + (c + b)) with
        | left pf => pf
        | right pf =>
          match pf (match
                       Plus.plus_comm b c in (_ = y)
                       return (a + b + c <> a + y -> a + b + c = a + y)
                     with
                       | eq_refl =>
                         fun _ : a + b + c <> a + (b + c) =>
                           eq_sym (Plus.plus_assoc a b c)
                     end pf) with end
      end.

    Lemma lift_typ_compose_sub : forall n s m n0,
      (if (if n ?[ lt ] s then n else n + m) ?[ lt ] s
       then if n ?[ lt ] s then n else n + m
       else (if n ?[ lt ] s then n else n + m) + n0) =
      (if n ?[ lt ] s then n else n + (n0 + m)).
      intros.
      change (let Z := n ?[ lt ] s in
              let Y := if Z then n else n + m in
              (if Y ?[ lt ] s then Y else Y + n0) =
              if Z then n else (n + (n0 + m))).
      refine (match n ?[ lt ] s as A
                    return A = n ?[ lt ] s ->
                           let Z := A in
                           let Y := if Z then n else n + m in
                           (if Y ?[ lt ] s then Y else Y + n0) =
                           (if Z then n else n + (n0 + m))
              with
                | true => fun pf =>
                            match pf in _ = t return (if t then _ else _) = _ with
                              | eq_refl => eq_refl
                            end
                | false => fun pf => _
              end eq_refl).
      simpl. rewrite <- not_lt_false; auto. apply plus_comm_assoc_trans.
    Defined.

    Theorem lift_typ0_compose_trans
    : forall t s n m,
        lift_typ0 s n (lift_typ0 s m t) = lift_typ0 s (n + m) t.
    Proof.
      induction t; simpl; intros.
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { f_equal. apply lift_typ_compose_sub. }
      { reflexivity. }
    Defined.

    Theorem lift_typ1_compose_trans
    : forall t s n m,
        lift_typ1 s n (lift_typ1 s m t) = lift_typ1 s (n + m) t.
    Proof.
      induction t; simpl; intros.
      { rewrite <- IHt. reflexivity. }
      { f_equal. apply lift_typ0_compose_trans. }
    Defined.

    Require Import MirrorCore.Iso.

    Record BigIso (A B : Type) : Type :=
    { binto : A -> B
    ; boutof : B -> A
    }.

    Definition Uhuge := Type.

    Fixpoint same {k} : kind0D' k -> kind0D' k -> Uhuge.
    refine
      match k as k return kind0D' k -> kind0D' k -> Uhuge with
        | kTy0 => fun a b => BigIso a b
        | kArr0 a b => fun x y =>
                        forall c d, @same a c d ->
                                    @same b (x c) (y d)
      end%type.
    Defined.

    Record BigSig2 (T : Type) (A B : T -> Uhuge) : Uhuge :=
    { value : T
    ; projT2_1 : A value
    ; projT2_2 : B value
    }.

    Lemma typD0_subst tvs t' A (H : typD0 tvs t' kTy0 = Some A)
    : forall t k' tvs' B,
        typD0 (tvs' ++ kTy0 :: tvs) t k' = Some B ->
        @BigSig2 (@Ctx.DCtx kind0D' (tvs' ++ tvs)
                            (fun _ : Ctx.Env kind0D' (tvs' ++ tvs) => kind0D' k'))
          (fun C => typD0 (tvs' ++ tvs)
                          (typ0_sub t (length tvs') (lift_typ0 0 (length tvs') t')) k' = Some C)
          (fun C =>
             forall (ts : hlist kind0D' (tvs' ++ tvs)),
               @same k'
                     (Ctx.eval_Ctx C ts)
                     (let (vs,vs') := hlist_split tvs' tvs ts in
                      let val : U0 := Ctx.eval_Ctx A vs' in
                      Ctx.eval_Ctx B (hlist_app vs (Hcons (l := kTy0) val vs'))
)).
    Admitted.


    Lemma typD1_subst tvs t' A (H : typD0 tvs t' kTy0 = Some A)
    : forall t k' tvs' B,
        typD1 (tvs' ++ kTy0 :: tvs) t k' = Some B ->
        @BigSig2 (@Ctx.DCtx kind0D' (tvs' ++ tvs)
                            (fun _ : Ctx.Env kind0D' (tvs' ++ tvs) => kind1D k'))
          (fun C => typD1 (tvs' ++ tvs)
                          (typ1_sub t (length tvs') (lift_typ0 0 (length tvs') t')) k' = Some C)
          (fun C =>
             forall (ts : hlist kind0D' (tvs' ++ tvs)),
               BigIso (Ctx.eval_Ctx C ts)
                      (let (vs,vs') := hlist_split tvs' tvs ts in
                       let val : U0 := Ctx.eval_Ctx A vs' in
                       Ctx.eval_Ctx B (hlist_app vs (Hcons (l := kTy0) val vs'))
)).
    Proof.
      induction t.
      { simpl. intros.
        destruct k'.
        specialize (IHt kTy1 (k :: tvs')).
        simpl in *.
        destruct (typD1 (k :: tvs' ++ kTy0 :: tvs) t kTy1); try congruence.
        specialize (@IHt _ eq_refl).
        unfold Quant_Ctx, Ctx.Quant_Ctx, Ctx.Quant_DCtx, Ctx.eval_Ctx in *.
        rewrite lift_typ0_compose_trans. destruct IHt.
        simpl. rewrite projT2_3.
        eexists. reflexivity.
        inversion H0; clear H0; subst. (** TODO: not efficient **)
        intros. constructor.
        { intros.
          remember (hlist_split tvs' tvs ts).
          destruct p. intro.
          specialize (projT2_4 (@Hcons _ kind0D' k _ x ts)).
          simpl in *. rewrite <- Heqp in *.
          specialize (X x). eapply projT2_4 in X. apply X. }
        { remember (hlist_split tvs' tvs ts).
          destruct p. intro.
          intro. specialize (X x).
          specialize (projT2_4 (@Hcons _ _ k _ x ts)).
          simpl in *. rewrite <- Heqp in *. apply projT2_4. apply X. } }
      { simpl.
        destruct k'. admit. }
    Admitted.

    Definition TApp_TCtxT {tvs t k}
               (F : TCtxT1 tvs (tPi k t))
               (t' : typ0) (** TODO: This must to be a good type! **)
               (H : typD0 ks t' k <> None)
    : TCtxT1 tvs (typ1_sub t 0 t').
      red in F. red. simpl in *.
      revert F.
      eapply Ctx.dap. red. intro.
      unfold CtxT.Ctx. unfold CtxT.DCtx. unfold typD1'.
      intros. specialize (X env0). clear env0.
      simpl in *. unfold Quant_Ctx, Ctx.Quant_Ctx, Ctx.Quant_DCtx in X.
    Admitted.

    Definition Use0_TCtxT {tvs t} (mem : member t tvs)
    : TCtxT0 tvs t.
      red. red.
      eapply Ctx.dap.
      2: eapply Ctx.dpure; intros; eapply (@CtxT.Use_Ctx (typD0' x) _ _ mem).
      simpl.
      eapply Ctx.dpure. intro.
      refine (fun x => x).
    Defined.

    Lemma Lift_0_1 {x tvs t}
    : CtxT.Ctx (typD0' (ks := ks) x) tvs (typD0' x t) ->
      CtxT.Ctx (typD0' x) tvs (typD1' x (tLift t)).
      unfold typD0', typD1'. simpl.
      destruct (typD0 ks t kTy0).
      { unfold Ctx.dfmap. unfold CtxT.Ctx, CtxT.DCtx, Ctx.eval_Ctx.
        refine (fun f e => f e). }
      { refine (fun x => x). }
    Defined.

    Definition Use1_TCtxT {tvs t} (mem : member t tvs)
    : TCtxT1 tvs (tLift t).
      red. red.
      eapply Ctx.dap.
      2: eapply Ctx.dpure; intros; eapply (@CtxT.Use_Ctx (typD0' x) _ _ mem).
      simpl.
      eapply Ctx.dpure. intro.
      apply Lift_0_1.
    Defined.

    Definition Env_hlist : forall d (tvs : list typ0) ctx,
                             @typD0' ks ctx d -> CtxT.Env (typD0' ctx) tvs ->
                             CtxT.Env (typD0' ctx) (d :: tvs).
      unfold CtxT.Env. do 3 intro. eapply Hcons.
    Defined.

    Definition Abs1_TCtxT {tvs d r}
    : option (TCtxT1 (d :: tvs) (tLift r) -> TCtxT1 tvs (tLift (tArr d r))).
      unfold TCtxT1. simpl.
      generalize (@Env_hlist d tvs).
      unfold typD1', typD0'.
      simpl.
      destruct (typD0 ks d kTy0).
      { destruct (typD0 ks r kTy0).
        { intro. apply Some.
          eapply Ctx.dap. eapply Ctx.dpure. intro.
          unfold CtxT.Ctx, CtxT.DCtx, Arr0_Ctx.
          simpl. unfold Ctx.dap, Ctx.dpure, Ctx.dfmap.
          specialize (X x).
          revert X. unfold Ctx.eval_Ctx.
          auto. }
        { exact (fun _ => None). } }
      { exact (fun _ => None). }
    Defined.

    Definition Abs_TCtxT {tvs d r}
    : option (TCtxT0 (d :: tvs) r -> TCtxT0 tvs (tArr d r)).
      unfold TCtxT0. simpl.
      generalize (@Env_hlist d tvs).
      unfold typD0'.
      simpl.
      destruct (typD0 ks d kTy0).
      { destruct (typD0 ks r kTy0).
        { intro. apply Some.
          eapply Ctx.dap. eapply Ctx.dpure. intro.
          unfold CtxT.Ctx. unfold CtxT.DCtx.
          unfold Arr0_Ctx. simpl. unfold Ctx.dap, Ctx.dpure.
          specialize (X x).
          revert X. unfold Ctx.eval_Ctx. auto. }
        { exact (fun _ => None). } }
      { exact (fun _ => None). }
    Defined.

    Fixpoint exprD (tvs : list typ0) (e : expr) (t : typ1) {struct e}
    : option (TCtxT1 tvs t).
      refine
        match e with
          | eExt x =>
            match EExt.typeof_ext x as toe
                  return match toe with
                           | Some T => match typD1 nil T kTy1 with
                                         | Some T => Ctx.eval_Ctx T (Ctx.Env_nil _)
                                         | None => Empty_set
                                       end
                           | None => unit
                         end -> _
            with
              | Some t' =>
                match typ1_eq t' t with
                  | Some pf => fun val =>
                                 Some (match pf in _ = z
                                             return TCtxT1 tvs z
                                       with
                                         | eq_refl => Inj_TCtxT val
                                       end)
                  | None => fun _ => None
                end
              | None => fun _ => None
            end (EExt.extD x)
          | eApp f x =>
            match t as t return option (TCtxT1 tvs t) with
              | tLift t =>
                match typeof_expr ks tvs x with
                  | Some (tLift t') =>
                    match exprD tvs f (tLift (tArr t' t)) with
                      | Some f =>
                        match exprD tvs x (tLift t') with
                          | Some x => Some (App1_TCtxT f x)
                          | None => None
                        end
                      | None => None
                    end
                  | _ => None
                end
              | _ => None
            end
          | eAbs t' e =>
            match t as t return option (TCtxT1 tvs t) with
              | tLift (tArr d r) =>
                match typ0_eq t' d with
                  | Some pf =>
                    match exprD (t' :: tvs) e (tLift r) with
                      | Some val =>
                        match @Abs1_TCtxT tvs t' r with
                          | Some abs =>
                            Some (match pf in _ = z
                                        return TCtxT1 tvs (tLift (tArr z r))
                                  with
                                    | eq_refl => abs val
                                  end)
                          | None => None
                        end
                      | None => None
                    end
                  | _ => None
                end
              | _ => None
            end
          | eVar v =>
            match t as t return option (TCtxT1 tvs t) with
              | tLift t =>
                match nth_member tvs v with
                  | Some (existT t' m) =>
                    match typ0_eq t' t with
                      | Some pf =>
                        Some match pf in _ = z return TCtxT1 tvs (tLift z) with
                               | eq_refl => Use1_TCtxT m
                             end
                      | None => None
                    end
                  | None => None
                end
              | _ => None
            end
          | eTApp e t' =>
            match typeof_expr ks tvs e with
              | Some t''' =>
                match t''' with
                  | tPi k t'' =>
                    match typD0 ks t' k as Z return typD0 ks t' k = Z -> _ with
                      | Some _ => fun pf' =>
                        match exprD tvs e (tPi k t'') with
                          | Some L =>
                            match typ1_eq (typ1_sub t'' 0 t') t with
                              | Some pf =>
                                Some match pf in _ = z return TCtxT1 tvs z with
                                       | eq_refl => TApp_TCtxT L _ _
                                     end
                              | None => None

                            end
                          | None => None
                        end
                      | _ => fun _ => None
                    end eq_refl
                  | _ => None
                end
              | None => None
            end
        end.
      clear - pf'. abstract congruence. (** This is a proof of False! **)
    Defined.
  End exprD.

  (** Some simple examples **)
  Time Eval compute in
      match exprD (kTy0 :: nil) nil (eAbs (tVar 0) (eVar 0)) (tLift (tArr (tVar 0) (tVar 0))) with
        | None => (fun x => x + 1)
        | Some val => val (@Hcons _ kind0D' kTy0 _ nat Hnil) Hnil
      end.

  Time Eval compute in
      match exprD (kTy0 :: nil) (tVar 0 :: nil)
                   (eApp (eAbs (tVar 0) (eVar 0)) (eVar 0))
                   (tLift (tVar 0)) with
        | None => 9
        | Some val =>
          let Ks := @Hcons _ kind0D' kTy0 _ nat Hnil in
          val Ks (@Hcons _ (typD0' Ks) (tVar 0) _ 0 Hnil)
      end.

End Expr.
