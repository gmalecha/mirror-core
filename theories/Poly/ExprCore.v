Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Poly.TypeI.
Require Import MirrorCore.Poly.Ctx.
Require Import MirrorCore.Poly.ML.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Move this, or consolidate it! **)
Section nth_mem.
  Variable T : Type.

  Fixpoint nth_mem (ls : list T) (n : nat) {struct ls} :
    option { x : T & member x ls } :=
    match ls as ls return (option { x : T & member x ls }) with
      | nil => None
      | l' :: ls =>
        match n with
          | 0 =>
            Some (@existT _ _ l' (MZ l' ls))
          | S n =>
            match nth_mem ls n with
              | Some m => Some (@existT _ _ (projT1 m) (MN l' (projT2 m)))
              | None => None
            end
        end
    end.
End nth_mem.

Module Ext : MLExt.
  Definition ext : Type := unit.
  Definition kindof_ext (e : ext) : option kind :=
    Some kTy.
  Definition extD (e : ext) : match kindof_ext e with
                                | Some k => kindD k
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

(** Definnition of expression extensions **)
Module Type ExprExt.

  (** NOTE: This precludes any environments! **)
  Record SymVal : Type :=
  { Typ : MLtypes.typ
  ; Value : match MLtypes.typD nil Typ kTy with
              | None => Empty_set
              | Some T => MLtypes.Ctx.eval_Ctx T (MLtypes.Ctx.Env_nil _)
            end
  }.

  Parameter ext : Type.
  Parameter typeof_ext : ext -> option MLtypes.typ.
  Parameter extD : forall e : ext,
                     match typeof_ext e with
                       | Some T =>
                         match MLtypes.typD nil T kTy with
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
  | eAbs  : typ -> expr -> expr
  | eVar  : nat -> expr
  | eTApp : expr -> typ -> expr
  | eExt  : EExt.ext -> expr.

  Section typeof_expr.
    Variable ks : list kind.
    Fixpoint typeof_expr  (tvs : list typ) (e : expr) : option typ.
      refine
        match e with
          | eApp f x =>
            match typeof_expr tvs f
                  , typeof_expr tvs x
            with
              | Some (tArr d r) , Some d' =>
                if typ_eq d d' then Some r else None
              | _ , _ => None
            end
          | eAbs t e =>
            match typeof_expr (cons t tvs) e with
              | Some r => Some (tArr t r)
              | _ => None
            end
          | eVar v => List.nth_error tvs v
          | eTApp e t =>
            match typeof_expr tvs e with
              | Some t'' =>
                match t'' with
                  | tPi t' =>
                    match kindof_typ ks t with
                      | Some k'' =>
                        match k'' with
                          | kTy => Some (typ_sub t' 0 t)
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

  (** TODO: This needs to be over an arbitrary kind environment **)
  Module Env <: ContextP.
    Definition iT := typ.
  End Env.

  Definition typD' (ks : list kind) (ctxK : Ctx.Env skindD ks) (t : typ) :=
    match @typD ks t kTy return Ustar with
      | None => Empty_set
      | Some T => Ctx.eval_Ctx T ctxK
    end.


  Module CtxT := ContextHList Env.
  Existing Instance CtxT.Applicative_Ctx.
  Existing Instance CtxT.Functor_Ctx.

  Section exprD.
    Variable ks : list kind.

    (** These have a good phase split, but it seems useful to have
     ** the context immediately to avoid the need to repeatedly destruct the
     ** types.
     **)
    Definition TCtx (ts : list typ) (T : Ctx.Env skindD ks -> Type) : Type :=
      @Ctx.DCtx skindD ks (fun kenv => CtxT.Ctx (typD' kenv) ts (T kenv)).

    Definition TCtxT (ts : list typ) (T : typ) :=
      TCtx ts (fun ctx => typD' ctx T).

    Definition Inj_TCtxT {ts t} (val : typD' (Ctx.Env_nil _) t)
    : TCtxT ts t.
      red. eapply Ctx.dpure; intro.
      eapply Applicative.pure.
      generalize (typD_weaken nil ks t); simpl.
      revert val.
      unfold typD'.
      refine (match typD nil t kTy as X
                    return match X with
                             | Some T => Ctx.eval_Ctx T (Ctx.Env_nil skindD)
                             | None => Empty_set
                           end ->
                           match X with
                             | Some T =>
                               match typD ks t kTy with
                                 | Some T' =>
                                   Ctx.DCtx
                                     (fun env : Ctx.Env skindD nil =>
                                        Ctx.eval_Ctx T env ->
                                        Ctx.DCtx
                                          (fun env' : Ctx.Env skindD ks =>
                                             Ctx.eval_Ctx T' (hlist_app env env')))
                                 | None => Empty_set
                               end
                             | None => unit
                           end ->
                           match typD ks t kTy with
                             | Some T => Ctx.eval_Ctx T x
                             | None => Empty_set
                           end
              with
                | Some c => fun X =>
                              match typD ks t kTy as Y
                                    return match Y with
                                             | Some T' =>
                                               Ctx.DCtx
                                                 (fun env : Ctx.Env skindD nil =>
                                                    Ctx.eval_Ctx c env ->
                                                    Ctx.DCtx
                                                      (fun env' : Ctx.Env skindD ks =>
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

    Definition App_TCtxT {tvs t' t} :
      TCtxT tvs (tArr t' t) ->
      TCtxT tvs t' ->
      TCtxT tvs t.
    Proof.
      unfold TCtxT, TCtx. unfold typD'. simpl.
      destruct (typD ks t' kTy).
      { destruct (typD ks t kTy).
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

    Theorem lift_typ_compose
    : forall t s n m,
        lift_typ s n (lift_typ s m t) = lift_typ s (m + n) t.
    Proof.
      induction t; simpl; intros.
      { rewrite <- IHt. reflexivity. }
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { remember (n ?[ lt ] s).
        destruct b.
        { rewrite <- Heqb. reflexivity. }
        { rewrite <- not_lt_false.
          clear. f_equal.
          induction n. reflexivity. simpl. rewrite IHn. reflexivity.
          assumption. } }
      { reflexivity. }
    Defined.

    (** TODO: Universes! **)
    Require Import MirrorCore.Iso.

    Fixpoint same {k} : kindD k -> kindD k -> Type.
    refine
      match k as k return kindD k -> kindD k -> Type with
        | kTy => fun a b => Iso a b
        | kArr a b => fun x y =>
                        forall c d, @same a c d ->
                                    @same b (x c) (y d)
      end%type.
    Defined.

(*
    Lemma typD_subst k tvs t' A (H : typD tvs t' k = Some A)
    : forall t k' tvs' B,
        typD (tvs' ++ k :: tvs) t k' = Some B ->
        { C : _ &
          typD (tvs' ++ tvs) (typ_sub t (length tvs') (lift_typ 0 (length tvs') t')) k' = Some C &
          forall ts,
            same (Ctx.eval_Ctx C ts)
                 (let (vs,vs') := hlist_split tvs' tvs ts in
                  Ctx.eval_Ctx B (hlist_app vs (Hcons (l := k) (Ctx.eval_Ctx A vs') vs'))) }.
    Proof.

      induction t.
      { simpl. destruct k'; simpl.
        { intros. specialize (IHt kTy (kTy :: tvs')).
          simpl in *.
          destruct (typD (kTy :: tvs' ++ k :: tvs) t kTy).
          { unfold Quant_Ctx in H0. unfold Ctx.Quant_Ctx in H0.
            unfold Ctx.Quant_DCtx in H0.
            specialize (@IHt _ eq_refl).
            rewrite lift_typ_compose. destruct IHt.
            simpl. rewrite e. eexists. reflexivity.
            intros.
            unfold Quant_Ctx in *.
            unfold Ctx.Quant_Ctx in *.
            unfold Ctx.Quant_DCtx in *.
            unfold Ctx.eval_Ctx in *. inversion H0. subst.
            constructor.
            { intros.
              remember (hlist_split tvs' tvs ts).
              destruct p. intro.
              specialize (i (Hcons (l := kTy) x0 ts)).
              simpl in i. rewrite <- Heqp in i.
              specialize (X x0). eapply i in X. apply X. }
            { 
            
  }
          { exfalso. inversion H0. }
*)

    Definition TApp_TCtxT {tvs t}
               (F : TCtxT tvs (tPi t))
               (t' : typ) (** TODO: This must to be a good type! **)
(*               (H : typD ks t' kTy <> None) *)
    : TCtxT tvs (typ_sub t 0 t').
      red in F. red. simpl in *.
      revert F.
      eapply Ctx.dap. red. intro.
      unfold CtxT.Ctx. unfold CtxT.DCtx. unfold typD'. simpl.
    Admitted.


    Definition Use_TCtxT {tvs t} (mem : member t tvs)
    : TCtxT tvs t.
      red. red.
      eapply Ctx.dap.
      2: eapply Ctx.dpure; intros; eapply (@CtxT.Use_Ctx (typD' x) _ _ mem).
      simpl.
      eapply Ctx.dpure. intro.
      refine (fun x => x).
    Defined.

    Definition Env_hlist : forall d tvs ctx,
                             @typD' ks ctx d -> CtxT.Env (typD' ctx) tvs ->
                             CtxT.Env (typD' ctx) (d :: tvs).
      unfold CtxT.Env. do 3 intro. eapply Hcons.
    Defined.

    Definition Abs_TCtxT {tvs d r}
    : option (TCtxT (d :: tvs) r -> TCtxT tvs (tArr d r)).
      unfold TCtxT. simpl.
      generalize (@Env_hlist d tvs).
      unfold typD'.
      simpl.
      destruct (typD ks d kTy).
      { destruct (typD ks r kTy).
        { intro. apply Some.
          eapply Ctx.dap. eapply Ctx.dpure. intro.
          unfold CtxT.Ctx. unfold CtxT.DCtx.
          unfold Arr_Ctx. simpl. unfold Ctx.dap, Ctx.dpure.
          specialize (X x).
          revert X. unfold Ctx.eval_Ctx. auto. }
        { exact (fun _ => None). } }
      { exact (fun _ => None). }
    Defined.

    Fixpoint exprD (tvs : list typ) (e : expr) (t : typ) {struct e}
    : option (TCtxT tvs t).
      refine
        match e with
          | eExt x =>
            match EExt.typeof_ext x as toe
                  return match toe with
                           | Some T => match typD nil T kTy with
                                         | Some T => Ctx.eval_Ctx T (Ctx.Env_nil _)
                                         | None => Empty_set
                                       end
                           | None => unit
                         end -> _
            with
              | Some t' =>
                match typ_eq t' t with
                  | Some pf => fun val =>
                                 Some (match pf in _ = z
                                             return TCtxT tvs z
                                       with
                                         | eq_refl => Inj_TCtxT val
                                       end)
                  | None => fun _ => None
                end
              | None => fun _ => None
            end (EExt.extD x)
          | eApp f x =>
            match typeof_expr ks tvs x with
              | Some t' =>
                match exprD tvs f (tArr t' t) with
                  | Some f =>
                    match exprD tvs x t' with
                      | Some x => Some (App_TCtxT f x)
                      | None => None
                    end
                  | None => None
                end
              | None => None
            end
          | eAbs t' e =>
            match t as t return option (TCtxT tvs t) with
              | tArr d r =>
                match typ_eq t' d with
                  | Some pf =>
                    match exprD (t' :: tvs) e r with
                      | Some val =>
                        match @Abs_TCtxT tvs t' r with
                          | Some abs =>
                            Some (match pf in _ = z return TCtxT tvs (tArr z r) with
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
            match nth_mem tvs v with
              | Some (existT t' m) =>
                match typ_eq t' t with
                  | Some pf =>
                    Some match pf in _ = z return TCtxT tvs z with
                           | eq_refl =>
                             Use_TCtxT m
                         end
                  | None => None
                end
              | None => None
            end
          | eTApp e t' =>
            match typeof_expr ks tvs e with
              | Some t''' =>
                match t''' with
                  | tPi t'' =>
                    match exprD tvs e (tPi t'') with
                      | Some L =>
                        match typ_eq (typ_sub t'' 0 t') t with
                          | Some pf =>
                            Some match pf in _ = z return TCtxT tvs z with
                                   | eq_refl => TApp_TCtxT L _
                                 end
                          | None => None

                        end
                      | None => None
                    end
                  | _ => None
                end
              | _ => None
            end
        end.
    Defined.
  End exprD.

  (** Some simple examples **)
  Time Eval compute in
      match exprD (kTy :: nil) nil (eAbs (tVar 0) (eVar 0)) (tArr (tVar 0) (tVar 0)) with
        | None => (fun x => x + 1)
        | Some val => val (@Hcons _ skindD kTy _ nat Hnil) Hnil
      end.

  Time Eval compute in
      match exprD (kTy :: nil) (tVar 0 :: nil) (eApp (eAbs (tVar 0) (eVar 0)) (eVar 0)) (tVar 0) with
        | None => 9
        | Some val =>
          let Ks := @Hcons _ skindD kTy _ nat Hnil in
          val Ks (@Hcons _ (typD' Ks) (tVar 0) _ 0 Hnil)
      end.

End Expr.
