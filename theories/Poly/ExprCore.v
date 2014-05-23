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
  Definition ext : Type := Empty_set.
  Definition kindof_ext (e : ext) : option kind :=
    match e with end.
  Definition extD (e : ext) : match kindof_ext e with
                                | Some k => kindD k
                                | None => unit
                              end :=
    match e with end.
  Definition ext_eq (a b : ext) : option (a = b) :=
    Some (match a with end).
End Ext.

Module MLtypes := ML Ext (* ContextHList *).

(** Definnition of expression extensions **)
Module Type ExprExt.

  (** NOTE: This precludes any environments! **)
  Record SymVal : Type :=
  { Typ : MLtypes.typ
  ; Value : match MLtypes.typD nil Typ kTy with
              | None => Empty_set
              | Some T => MLtypes.Ctx.eval_Ctx T MLtypes.Ctx.Env_nil
            end
  }.

  Parameter ext : Type.
  Parameter typeof_ext : ext -> option MLtypes.typ.
  Parameter extD : forall e : ext,
                     match typeof_ext e with
                       | Some T =>
                         match MLtypes.typD nil T kTy with
                           | None => Empty_set
                           | Some T => MLtypes.Ctx.eval_Ctx T MLtypes.Ctx.Env_nil
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
    Definition Denote (t : typ) :=
      match @typD nil t kTy return Ustar with
        | None => Empty_set
        | Some T =>  (** TODO: This requires the context of values **)
          Ctx.eval_Ctx T MLtypes.Ctx.Env_nil
      end.
  End Env.

  Module CtxT := ContextHList Env.
  Existing Instance CtxT.Applicative_Ctx.
  Existing Instance CtxT.Functor_Ctx.

  Section exprD.
    Variable ks : list kind.

    (** These have a good phase split, but it seems useful to have
     ** the context immediately to avoid the need to repeatedly destruct the
     ** types.
     **)
    Definition TCtx (ts : list typ) (T : Ctx.Env ks -> Type) : Type :=
      @Ctx.DCtx ks (fun kenv => CtxT.Ctx ts (T kenv)).

    Definition TCtxT (ts : list typ) (T : typ) :=
      TCtx ts (fun ctx =>
                 match typD ks T kTy with
                   | Some T => Ctx.eval_Ctx T ctx
                   | None => Empty_set
                 end).

    Definition Inj_TCtxT {ts t}
               (val : match typD nil t kTy with
                        | Some T => Ctx.eval_Ctx T Ctx.Env_nil
                        | None => Empty_set
                      end)
    : TCtxT ts t.
      red. eapply Ctx.dpure; intro.
      eapply Applicative.pure.
      generalize (typD_weaken nil ks t); simpl.
      revert val.
      destruct (typD nil t kTy). 2: destruct 1.
      destruct (typD ks t kTy).
      { intros. eapply Ctx.dap. 2: eapply X.
        2: eapply val. clear val.
        simpl. eapply Ctx.dpure. refine (fun _ x => x). }
      { destruct 2. }
    Defined.
    (**
    Eval cbv beta iota zeta delta [ Inj_TCtxT Ctx.dpure Ctx.dap Applicative.pure Applicative.ap CtxT.Applicative_Ctx CtxT.dpure CtxT.dap ] in @Inj_TCtxT.
    **)

    Definition App_TCtxT {tvs t' t} :
      TCtxT tvs (tArr t' t) ->
      TCtxT tvs t' ->
      TCtxT tvs t.
    Proof.
      unfold TCtxT. simpl.
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

    Axiom typD_weaken'
    : forall ks ks' tvs t,
        Ctx.DCtx
          (fun x : Ctx.Env ks =>
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

    Theorem lift_typ_compose
    : forall t s n m,
        lift_typ s n (lift_typ s m t) = lift_typ s (n + m) t.
    Proof.
      induction t; simpl; intros.
      { rewrite <- IHt. reflexivity. }
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { rewrite <- IHt1. rewrite <- IHt2. reflexivity. }
      { destruct (n ?[ lt ] s). admit. admit. }
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
      eapply Ctx.dap. red. intros.

    Admitted.


    Definition Use_TCtxT {tvs t} (mem : member t tvs)
    : TCtxT tvs t.
      red. red.
      eapply Ctx.dap.
      2: eapply Ctx.dpure; intros; eapply (CtxT.Use_Ctx mem).
      simpl.
      unfold CtxT.Denote, Env.Denote.
      eapply Ctx.dpure. intro.
      generalize (typD_weaken nil ks t).
      simpl.
      destruct (typD nil t kTy).
      { destruct (typD ks t kTy).
        { intro. eapply (fun H => Ctx.eval_Ctx H Ctx.Env_nil) in X.
          simpl in X.
          eapply Functor.fmap. eauto with typeclass_instances.
          intro. specialize (X X0).
          eapply Ctx.eval_Ctx in X. eapply X. }
        { destruct 1. } }
      { intro. eapply CtxT.dap.
        eapply CtxT.dpure. destruct 2. }
    Defined.

    Definition Env_hlist : forall d tvs,
                             Env.Denote d -> CtxT.Env tvs ->
                             CtxT.Env (d :: tvs).
      unfold CtxT.Env. do 2 intro. eapply Hcons.
    Defined.

    Definition Abs_TCtxT {tvs d r}
    : option (TCtxT (d :: tvs) r -> TCtxT tvs (tArr d r)).
      unfold TCtxT. simpl.
      generalize (@Env_hlist d tvs).
      unfold Env.Denote.
      (** TODO: This isn't true because of the configuration of the
       ** environment, see notes above
       **)
(*
      destruct (typD ks d kTy).
      { destruct (typD ks r kTy).
        { apply Some.
          eapply Ctx.dap. eapply Ctx.dpure. intro.
          unfold CtxT.Ctx. unfold CtxT.DCtx.
          unfold Arr_Ctx. simpl. unfold Ctx.dap, Ctx.dpure.
          unfold Ctx.eval_Ctx.
        }
        { exact None. } }
      { exact None. }
      Check CtxT.Quant_Ctx.
      simpl.

*)
    Admitted.

    Fixpoint exprD (tvs : list typ) (e : expr) (t : typ) {struct e}
    : option (TCtxT tvs t).
      refine
        match e with
          | eExt x =>
            match EExt.typeof_ext x as toe
                  return match toe with
                           | Some T => match typD nil T kTy with
                                         | Some T => Ctx.eval_Ctx T Ctx.Env_nil
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

  Time Eval simpl in
      exprD (kTy :: nil) nil (eAbs (tVar 0) (eVar 0)) (tArr (tVar 0) (tVar 0)).

End Expr.


(**
      Fixpoint exprD (tvs : list typ) (e : expr) (t : typ) (k : kind) {struct e}
      : option (TCtxT tvs t k).
      refine
        match e with
          | eExt x =>
            match k as k return option (TCtxT tvs t k) with
              | kTy =>
                match EExt.typeof_ext x as toe
                      return match toe with
                               | Some T => match typD nil T kTy with
                                             | Some T => Ctx.eval_Ctx T
                                             | None => Empty_set
                                           end
                               | None => unit
                             end -> _
                with
                  | Some t' =>
                    match typ_eq t' t with
                      | Some pf => fun val =>
                                     Some (match pf in _ = z
                                                 return TCtxT tvs z kTy
                                           with
                                             | eq_refl => Inj_TCtxT val
                                           end)
                      | None => fun _ => None
                    end
                  | None => fun _ => None
                end (EExt.extD x)
              | _ => None
            end
          | eApp f x =>
            match typeof_expr ks tvs x with
              | Some t' =>
                match exprD tvs f (tArr t' t) kTy with (** TODO **)
                  | Some f =>
                    match exprD tvs x t' kTy with
                      | Some x => _
                        (*
                        match CtxD_App tvs t' t with
                          | Some C => Some (C f x)
                          | None => None
                        end
                         *)
                      | None => None
                    end
                  | None => None
                end
              | None => None
            end
          | eAbs t' e => _
          (*
          match t with
            | tyArr d r => (** TODO **)
              match typ_eq t' d with
                | left pf =>
                  match exprD (t' :: tvs) e r with
                    | Some val =>
                      match CtxD_Abs tvs t' r with
                        | Some C =>
                          Some match pf in _ = t
                                     return CtxD_typ tvs (tyArr t r) with
                                 | eq_refl => C val
                               end
                        | None => None
                      end
                    | None => None
                  end
                | _ => None
              end
            | _ => None
          end
           *)
          | eVar v => _ (* CtxD_Use _ _ v *)
          | eTApp e t' => _
        (*
          match typeof_expr tvs e with
            | Some (tyPi s t'') => (** TODO **)
              match exprD tvs e (tyPi s t') with (** TODO **)
                | Some L =>
                  match typD ts t' s with
                    | Some T => _
                    | None => None
                  end
                | None => None
              end
            | _ => None
          end
         *)
        end.
*)

(*
  Section exprD.
    Variable ts : list kind.
    Variable ctx : Ctx ts.

(*
    Fixpoint default_kind_val (s : kind) : kindD s :=
      match s as s return kindD s with
        | kTy => Empty_set
        | kArr s1 s2 => fun _ => default_kind_val s2
      end.
*)

    Let typD' t : U1 :=
      match typD ts t kTy return U1 with
        | None => Empty_set
        | Some T => applyCtx _ kTy T ctx
      end.

    Fixpoint CtxD_typ (ls : list typ) (t : typ) k : option (kindD k)
      match mapT typD' ls
          , typD ts t k
      with
        | Some Ts , Some T => _
        | _ , _ => None
      end.

    Fixpoint Abs_applyCtx ts' {struct ts'}
    : forall (d r : CtxD ts' kTy) ctx,
        (applyCtx ts' kTy d ctx -> applyCtx ts' kTy r ctx) ->
        applyCtx ts' kTy (Arr ts' d r) ctx :=
      match ts' as ts'
            return forall (d r : CtxD ts' kTy) ctx,
                     (applyCtx ts' kTy d ctx -> applyCtx ts' kTy r ctx) ->
                     applyCtx ts' kTy (Arr ts' d r) ctx
      with
        | nil => fun _ _ _ x => x
        | cons t ts => fun _ _ x_y f => @Abs_applyCtx ts _ _ _ f
      end.


    Fixpoint CtxD_Abs tvs d r
    : option (CtxD_typ (d :: tvs) r -> CtxD_typ tvs (tyArr d r)) :=
      match tvs as tvs
            return option (CtxD_typ (d :: tvs) r -> CtxD_typ tvs (tyArr d r))
      with
        | nil =>
          match typD ts d kTy as D
              , typD ts r kTy as R
                return option ((match D with
                                  | Some T => applyCtx ts kTy T ctx
                                  | None => Empty_set
                                end ->
                                match R with
                                  | Some T => applyCtx ts kTy T ctx
                                  | None => Empty_set
                                end) ->
                               match
                                 match D with
                                   | Some l =>
                                     match R with
                                       | Some r0 => Some (Arr ts l r0)
                                       | None => None
                                     end
                                   | None => None
                                 end
                               with
                                 | Some T => applyCtx ts kTy T ctx
                                 | None => Empty_set
                               end)
          with
            | Some d , Some r => Some (Abs_applyCtx _ _ _ _)
            | _ , _ => None
          end
        | cons t tvs =>
          match CtxD_Abs tvs d r with
            | None => None
            | Some Z => Some (fun f x => Z (fun y => f y x))
          end
      end.

    Fixpoint App_applyCtx ts' {struct ts'}
    : forall (d r : CtxD ts' kTy) ctx, (applyCtx ts' kTy (Arr ts' d r) ctx ->
                                        applyCtx ts' kTy d ctx ->
                                        applyCtx ts' kTy r ctx)
    :=
      match ts' as ts'
            return forall (d r : CtxD ts' kTy) ctx, (applyCtx ts' kTy (Arr ts' d r) ctx ->
                                        applyCtx ts' kTy d ctx ->
                                        applyCtx ts' kTy r ctx)
      with
        | nil => fun _ _ _ x => x
        | cons t ts => fun _ _ x_y f => @App_applyCtx ts _ _ _ f
      end.

    Fixpoint CtxD_App tvs d r
    : option (CtxD_typ tvs (tyArr d r) -> CtxD_typ tvs d -> CtxD_typ tvs r) :=
      match tvs as tvs
            return option (CtxD_typ tvs (tyArr d r) -> CtxD_typ tvs d -> CtxD_typ tvs r)
      with
        | nil => match typD ts d kTy as D
                     , typD ts r kTy as R
                       return option
                                (match
                                    match D with
                                      | Some l =>
                                        match R with
                                          | Some r0 => Some (Arr ts l r0)
                                          | None => None
                                        end
                                      | None => None
                                    end
                                  with
                                    | Some T => applyCtx ts kTy T ctx
                                    | None => Empty_set
                                  end ->
                                 match D with
                                   | Some T => applyCtx ts kTy T ctx
                                   | None => Empty_set
                                 end ->
                                 match R with
                                   | Some T => applyCtx ts kTy T ctx
                                   | None => Empty_set
                                 end)
                 with
                   | Some d , Some r => Some (App_applyCtx _ d r ctx)
                   | _ , _ => None
                 end
        | cons t tvs =>
          match CtxD_App tvs d r with
            | Some Z => Some (fun f g x => Z (f x) (g x))
            | None => None
          end
      end.

    Fixpoint CtxD_Inj tvs t (val : typD' t) {struct tvs} : CtxD_typ tvs t :=
      match tvs as tvs return CtxD_typ tvs t with
        | nil => val
        | cons _ tvs => fun _ => CtxD_Inj tvs t val
      end.

    Fixpoint CtxD_Use tvs t (n : nat) : option (CtxD_typ tvs t) :=
      match tvs as tvs return option (CtxD_typ tvs t) with
        | nil => None
        | cons t' tvs =>
          match n with
            | 0 => match typ_eq t' t with
                     | left pf => Some match eq_sym pf in _ = t'
                                             return CtxD_typ (t' :: tvs) t
                                       with
                                         | eq_refl => CtxD_Inj _ _
                                       end
                     | right _ => None
                   end
            | S n =>
              match CtxD_Use tvs t n with
                | None => None
                | Some Z => Some (fun _ => Z)
              end
          end
      end.
*)
