Require Import List Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.

Set Implicit Arguments.
Set Strict Implicit.

Section env.

  Variable types : types.

  Definition typ_cast_val ts (a b : typ) (v : typD types ts a)
  : option (typD types ts b) :=
    match typ_cast_typ types (fun x => x) ts a b with
      | None => None
      | Some f => Some (f v)
    end.

  Definition func := nat.
  Record tfunction : Type :=
  { tfenv : nat ; tftype : typ }.
  Definition tfunctions := list tfunction.
  Definition var := nat.
  Definition uvar := nat.

  Unset Elimination Schemes.

  Inductive expr : Type :=
  | Var : var -> expr
  | Func : func -> list typ -> expr
  | App : expr -> list expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> expr
  | Equal : typ -> expr -> expr -> expr
  | Not : expr -> expr.

  Inductive expr_acc : expr -> expr -> Prop :=
  | acc_App_l : forall f a, expr_acc f (App f a)
  | acc_App_r : forall f a x, In a x -> expr_acc a (App f x)
  | acc_Abs : forall t e, expr_acc e (Abs t e)
  | acc_Equal_l : forall t l r, expr_acc l (Equal t l r)
  | acc_Equal_r : forall t l r, expr_acc r (Equal t l r)
  | acc_Not : forall e, expr_acc e (Not e).

  Definition exprs : Type := list expr.

  Set Elimination Schemes.

  Section expr_ind.
    Variable P : expr -> Prop.
    Hypothesis HVar : forall v : var, P (Var v).
    Hypothesis HFunc : forall f ts, P (Func f ts).
    Hypothesis HUVar : forall v : var, P (UVar v).
    Hypothesis HApp : forall f es, P f -> Forall P es -> P (App f es).
    Hypothesis HAbs : forall t e, P e -> P (Abs t e).
    Hypothesis HEqual : forall t e1 e2, P e1 -> P e2 -> P (Equal t e1 e2).
    Hypothesis HNot : forall e, P e -> P (Not e).

    Fixpoint expr_ind x : P x.
    Proof.
    refine (
      match x as x return P x with
        | Var _ => HVar _
        | UVar _ => HUVar _
        | Func _ _ => HFunc _ _
        | Abs _ _ => HAbs _ (expr_ind _)
        | App _ _ => HApp (expr_ind _) ((fix all es : Forall P es :=
          match es with
            | nil => Forall_nil _
            | e :: es => Forall_cons _ (expr_ind e) (all es)
          end) _)
        | Equal _ _ _ => HEqual _ (expr_ind _) (expr_ind _)
        | Not _ => HNot (expr_ind _)
      end).
    Qed.
  End expr_ind.

  Theorem wf_expr_acc : well_founded expr_acc.
  Proof.
    clear. red.
    induction a; simpl; intros; constructor; intros;
    try solve [ inversion H ].
    { inversion H0; clear H0; subst; auto.
      induction es; simpl in *.
      intuition.
      destruct H3. subst. inversion H; clear H; subst. auto.
      eapply IHes; eauto. inversion H; auto. }
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. }
  Qed.

  Record function := F {
    fenv : nat ;
    ftype : typ ;
    fdenote : parametric fenv nil (fun env => typD types env ftype)
  }.

  Definition functions := list function.
  Definition variables := list typ.

  Variable funcs : functions.
  Variable meta_env : env (typD types).

  Require Import ExtLib.Data.List.
  Require Import ExtLib.Data.Option.
  Require Import ExtLib.Data.Monads.OptionMonad.

  Require Import ExtLib.Structures.Reducible.

  Fixpoint typeof (var_env : tenv typ) (e : expr) {struct e} : option typ :=
    match e with
      | Var x =>
        match nth_error var_env x with
          | None => None
          | Some tv => Some tv
        end
      | UVar x =>
        match nth_error meta_env x with
          | None => None
          | Some tv => Some (projT1 tv)
        end
      | Func f ts =>
        match nth_error funcs f with
          | None => None
          | Some r =>
(*          if EqNat.beq_nat (length ts) (fenv r) then *)
              Some (instantiate_typ ts (ftype r))
(*          else
              None
*)
        end
      | App e es =>
        fold_left (fun a n => Monad.bind a (fun a =>
                              Monad.bind n (fun n =>
                              type_of_apply a n)))
                    (map (typeof var_env) es) (typeof var_env e)
      | Abs t e =>
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal _ _ _ => Some tvProp
      | Not _ => Some tvProp
    end.

  (**
   ** The denotation function with binders must be total because we
   ** can't introduce the binder until we know that we are going to get
   ** the right type out, but, at the same time, we don't know we will
   ** succeed until after we've taken the denotation of the body,
   ** which we can't do until we have the binder.
   **
   **)
  Fixpoint exprD' (var_env : tenv typ) (e : expr) (t : typ) {struct e} :
    option (hlist (typD types nil) var_env -> typD types nil t).
  refine (
    match e as e return option (hlist (typD types nil) var_env -> typD types nil t) with
      | Var x =>
        match nth_error var_env x as z
          return z = nth_error var_env x ->
                 option (hlist (typD types nil) var_env -> typD types nil t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match typ_cast_typ types (fun x => x) _ t' t with
              | Some f =>
                Some (fun e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD types nil t
                                              | None => unit
                                            end -> typD types nil t with
                                 | eq_refl => fun x => f x
                               end (hlist_nth e x))
              | None => None
            end
        end eq_refl
      | UVar x =>
        match lookupAs meta_env x t with
          | None => None
          | Some v => Some (fun _ => v)
        end
(*
      | Func f nil =>
        match nth_error funcs f with
          | None => None
          | Some {| fenv := 0 ; ftype := ft ; fdenote := f |} =>
            Monad.bind (m := option) (typ_cast (fun x => x) _ ft t)
                       (fun cst => Monad.ret (fun _ => cst f))
          | Some _ => None
        end
*)
      | Func f ts' =>
        match nth_error funcs f with
          | None => None
          | Some f =>
            match type_apply _ _ ts' _ _ f.(fdenote) with
              | None => None
              | Some t' =>
                match @typ_cast_val _ (instantiate_typ ts' (ftype f)) t t' with
                  | Some v => Some (fun _ => v)
                  | None => None
                end
            end
        end
      | Abs t' e =>
        match t as t return option (hlist (typD types nil) var_env -> typD types nil t)
        with
          | tvArr lt rt =>
            match typ_cast_typ types (fun x => x) nil lt t' with
              | None => None
              | Some cast =>
                match @exprD' (lt :: var_env) e rt with
                  | None => None
                  | Some a => Some (fun x y => a (Hcons y x))
                end
            end
          | _ => None
        end
      | App f xs =>
        match typeof var_env f with
          | None => None
          | Some tf =>
            match exprD' var_env f tf with
              | None => None
              | Some f =>
                (fix eval_args (t' : typ) (xs : list expr) {struct xs} :
                  (hlist (typD types nil) var_env -> typD types nil t') ->
                  option (hlist (typD types nil) var_env -> typD types nil t) :=
                  match xs with
                    | nil =>
                      match typ_cast_typ types (fun x => x) _ t' t with
                        | None => fun _ => None
                        | Some cast => fun f => Some (fun g => cast (f g))
                      end
                    | x :: xs =>
                      match t' as t'
                        return        (hlist (typD types nil) var_env -> typD types nil t') ->
                               option (hlist (typD types nil) var_env -> typD types nil t)
                      with
                        | tvArr tl tr => fun f =>
                          match exprD' var_env x tl with
                            | None => None
                            | Some xv =>
                              eval_args tr xs (fun e => f e (xv e))
                          end
                        | _ => fun _ => None
                      end
                  end) tf xs f
            end
        end
      | Equal t' e1 e2 =>
        match t as t return option (hlist (typD types nil) var_env -> typD types nil t) with
          | tvProp =>
            match exprD' var_env e1 t' , exprD' var_env e2 t' with
              | Some l , Some r =>
                Some (fun g => (l g) = (r g))
              (* equal (type := typeFor (typD := typD types) nil t') *)
              | _ , _ => None
            end
          | _ => None
        end
      | Not e =>
        match t as t return option (hlist (typD types nil) var_env -> typD types nil t)
 with
          | tvProp =>
            match exprD' var_env e tvProp with
              | Some P => Some (fun g => not (P g))
              | _ => None
            end
          | _ => None
        end
    end).
  Defined.


  Definition exprD (var_env : env (typD types)) (e : expr) (t : typ)
  : option (typD types nil t) :=
    let (ts,vs) := split_env var_env in
    match exprD' ts e t with
      | None => None
      | Some f => Some (f vs)
    end.

  Require Import ExtLib.Tactics.Injection.
  Require Import ExtLib.Tactics.EqDep.
  Require Import ExtLib.Data.ListNth.


    Theorem split_env_nth_error : forall ve v tv,
      nth_error ve v = Some tv <->
      match nth_error (projT1 (split_env ve)) v as t
      return match t with
               | Some v => typD types nil v
               | None => unit
             end -> Prop
      with
        | None => fun _ => False
        | Some v => fun res => tv = existT _ v res
      end (hlist_nth (projT2 (split_env ve)) v).
    Proof.
      induction ve; simpl; intros.
      { destruct v; simpl in *; intuition; inversion H. }
      { destruct v; simpl in *.
        { intuition.
          { inversion H; subst. destruct tv; reflexivity. }
          { subst. destruct a. reflexivity. } }
        { eapply IHve. } }
    Qed.

  Theorem exprD_Var : forall ve v t,
    exprD ve (Var v) t = lookupAs ve v t.
  Proof.
    unfold exprD; simpl; intros.
    consider (split_env ve); intros.
    unfold lookupAs.
    generalize (split_env_nth_error ve v).
    consider (nth_error ve v).
    { intros. destruct (H1 s); clear H1. clear H3. specialize (H2 eq_refl).
      rewrite H in *. simpl in *.
      destruct s; simpl in *.
      revert H2.
      change (
          let f' e0 := hlist_nth e0 v in
          match
            nth_error x v as t1
            return
            (match t1 with
               | Some v0 => typD types nil v0
               | None => unit
             end -> Prop)
          with
            | Some v0 =>
              fun res : typD types nil v0 =>
                existT (typD types nil) x0 t0 = existT (typD types nil) v0 res
            | None => fun _ : unit => False
          end (f' h) ->
          match
            match
              nth_error x v as z
              return
              (z = nth_error x v ->
               option (hlist (typD types nil) x -> typD types nil t))
            with
              | Some t' =>
                fun pf : Some t' = nth_error x v =>
                  match typ_cast_typ types (fun x1 : Type => x1) nil t' t with
                    | Some f =>
                      Some
                        (fun e0 : hlist (typD types nil) x =>
                           match
                             pf in (_ = t'')
                             return
                             (match t'' with
                                | Some t1 => typD types nil t1
                                | None => unit
                              end -> typD types nil t)
                           with
                             | eq_refl => fun x1 : typD types nil t' => f x1
                           end (f' e0))
                    | None => None
                  end
              | None => fun _ : None = nth_error x v => None
            end eq_refl
          with
            | Some f => Some (f h)
            | None => None
          end =
          match typ_cast_typ types (fun x1 : Type => x1) nil x0 t with
            | Some f => Some (f t0)
            | None => None
          end).
      match goal with
        | |- context [ @eq_refl ?X ?Y ] =>
          generalize dependent (@eq_refl X Y)
      end.
      pattern (nth_error x v) at 1 5.
      destruct (nth_error x v).
      { intro.
        assert (nth_error x v = Some x0).
        { cutrewrite (x = projT1 (split_env ve)).
          rewrite split_env_projT1.
          erewrite map_nth_error. 2: eassumption. reflexivity.
          rewrite H. reflexivity. }
        { assert (x0 = t1).
          { rewrite H1 in e. inv_all; auto. }
          subst. destruct (typ_cast_typ types (fun x => x) nil t1 t); auto.
          { intros. f_equal.
            subst f'. simpl in *. generalize dependent (hlist_nth h v).
            generalize dependent (nth_error x v).
            intros; subst.
            inv_all. f_equal; auto. } } }
      { simpl. intro. generalize dependent (hlist_nth h v).
        rewrite <- e. intuition. } }
    { intro.
      assert (nth_error x v = None).
      { cutrewrite (x = projT1 (split_env ve)).
        rewrite split_env_projT1.
        rewrite nth_error_map.
        rewrite H0. reflexivity.
        rewrite H. reflexivity. }
      { match goal with
          | |- context [ @eq_refl ?X ?Y ] =>
            generalize dependent (@eq_refl X Y)
        end.
        rewrite H; simpl. intros. clear H2.
        change (
            let f t' := fun pf : Some t' = nth_error x v =>
                    match typ_cast_typ types (fun x0 : Type => x0) nil t' t with
                      | Some f =>
                        Some
                          (fun e0 : hlist (typD types nil) x =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t0 => typD types nil t0
                                  | None => unit
                                end -> typD types nil t)
                             with
                               | eq_refl => fun x0 : typD types nil t' => f x0
                             end (hlist_nth e0 v))
                      | None => None
                    end in
            match
              match
                nth_error x v as z
                return
                (z = nth_error x v ->
                 option (hlist (typD types nil) x -> typD types nil t))
              with
                | Some t' => f t'
                | None => fun _ : None = nth_error x v => None
              end e
            with
              | Some f => Some (f h)
              | None => None
            end = None
          ).
        intro. clearbody f.
        revert e.
        pattern (nth_error x v) at 1 3.
        rewrite H1. reflexivity. } }
  Qed.

  Theorem exprD_UVar : forall ve u t,
    exprD ve (UVar u) t = lookupAs meta_env u t.
  Proof.
    unfold exprD. intros.
    destruct (split_env ve); simpl.
    destruct (lookupAs meta_env u t); auto.
  Qed.

  Theorem exprD_Equal : forall ve t l r,
    exprD ve (Equal t l r) tvProp =
    match exprD ve l t , exprD ve r t with
      | Some l , Some r => Some (l = r)
      | _ , _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct (exprD' x l t); destruct (exprD' x r t); auto.
  Qed.

  Theorem exprD_Not : forall ve p,
    exprD ve (Not p) tvProp =
    match exprD ve p tvProp with
      | Some p => Some (~p)
      | _ => None
    end.
  Proof.
    unfold exprD; intros.
    destruct (split_env ve); simpl.
    destruct (exprD' x p tvProp); auto.
  Qed.

  Fixpoint arrow (ls : list typ) (r : typ) : typ :=
    match ls with
      | nil => r
      | l :: ls => tvArr l (arrow ls r)
    end.

  Fixpoint apply {ts} {ls : list typ} {r : typ} (f : typD types ts (arrow ls r))
           (args : hlist (typD types ts) ls) : typD types ts r :=
    match args in hlist _ ls
          return typD types ts (arrow ls r) -> typD types ts r
    with
      | Hnil => fun x => x
      | Hcons _ _ v vs => fun x => apply (x v) vs
    end f.

  Fixpoint mapD {T : Type} {F : T -> Type} (f : forall x, F x) (ls : list T)
  : hlist F ls :=
    match ls with
      | nil => Hnil
      | l :: ls => @Hcons T F l ls (f l) (mapD f ls)
    end.

  Fixpoint mapD2 {T U : Type} {F : T -> Type} (f : U -> forall x, F x) (ls : list (U * T))
  : hlist F (map snd ls) :=
    match ls as ls return hlist F (map snd ls) with
      | nil => Hnil
      | (l,l') :: ls => @Hcons T F _ _ (f l l') (mapD2 f ls)
    end.

  Theorem exprD_Abs : forall ve t u e val,
    exprD ve (Abs t e) (tvArr t u) = Some val ->
    forall x, exprD (existT _ t x :: ve) e u = Some (val x).
  Proof.
    unfold exprD. intros.
    change (split_env (existT (typD types nil) t x :: ve))
      with (split_env ((existT (typD types nil) t x :: nil) ++ ve)).
    rewrite split_env_app.
    destruct (split_env ve). simpl in *.
    rewrite typ_cast_typ_refl in *.
    destruct (exprD' (t :: x0) e u); intuition (try congruence).
    inv_all; subst. reflexivity.
  Qed.

  Theorem typ_cast_typ_eq : forall f ts t t' v,
                              typ_cast_typ types f ts t t' = Some v -> t = t'.
  Proof.
    clear. unfold typ_cast_typ; simpl; intros.
    destruct (typ_eq_odec t t'); auto. congruence.
  Qed.

  Theorem exprD'_typeof : forall e ve t v,
    exprD' ve e t = Some v ->
    typeof ve e = Some t.
  Proof.
    induction e; simpl; intros; auto;
    repeat match goal with
             | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
               (consider X; intros; try congruence); [ inv_all; subst ]
           end.
    { match type of H with
        | _ ?X = _ => generalize dependent X
      end.
      pattern (nth_error ve v) at 1 3.
      destruct (nth_error ve v); try congruence.
      intros.
      match goal with
        | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
          (consider X; intros; try congruence); [ inv_all; subst ]
      end.
      unfold typ_cast_typ in H.
      rewrite <- e.
      destruct (typ_eq_odec t0 t); subst; auto. congruence. }
    { destruct f0; simpl in *. clear H. f_equal.
      generalize dependent ftype0.
      induction ts; simpl; intros.
      { destruct fenv0; simpl in *. inv_all; subst.
        Lemma typ_cast_val_eq : forall ts a b v v', 
                                  typ_cast_val ts a b v = Some v' ->
                                  a = b.
        Proof.
          clear. unfold typ_cast_val; simpl; intros.
          unfold typ_cast_typ in *. generalize (@typ_eq_odec_None a b).
          destruct (typ_eq_odec a b); auto. congruence.
        Qed.
        eapply typ_cast_val_eq in H1. auto. congruence. }
      { destruct fenv0; simpl in *; try congruence.
        match goal with
          | H : match ?X with _ => _ end = _ |- _ =>
            consider X
        end; intros; try congruence.
        inv_all; subst.
        specialize (IHts _ fdenote0). unfold typ_cast_val in *.
        unfold typ_cast_typ in *.
        generalize (@typ_eq_odec_None (subst0_typ a (instantiate_typ ts ftype0)) t).
        destruct (typ_eq_odec (subst0_typ a (instantiate_typ ts ftype0)) t); try congruence. } }
    { unfold lookupAs in *.
      destruct (nth_error meta_env v).
      { destruct s. simpl in *.
        unfold typ_cast_typ in *.
        destruct (typ_eq_odec x t); subst; auto.
        congruence. }
      { congruence. } }
    { clear H1 H0 IHe. generalize dependent t0. generalize dependent t. clear - H.
      induction H; simpl; intros.
      { generalize (@typ_cast_typ_eq (fun x => x) nil t0 t).
        destruct (typ_cast_typ types (fun x : Type => x) nil t0 t); try congruence.
        inv_all. subst. intros. specialize (H _ eq_refl). subst; auto. }
      { destruct t0; try congruence.
        consider (exprD' ve x t0_1); try congruence; intros. eapply H in H1.
        rewrite H1 in *. simpl in *.
        change (typ_eqb t0_1 t0_1) with (t0_1 ?[ eq ] t0_1).
        consider (t0_1 ?[ eq ] t0_1); try congruence; intros.
        clear H3. eapply IHForall; eauto. } }
    { eapply IHe in H0.
      generalize (typ_cast_typ_eq (fun x => x) nil t1 t H); intros; subst.
      rewrite H0. reflexivity. }
    { destruct t0; auto; congruence. }
    { destruct t; auto; congruence. }
  Qed.

  Theorem exprD_app_nil : forall ve t e,
    exprD ve (App e nil) t = exprD ve e t.
  Proof.
    unfold exprD; simpl; intros.
    destruct (split_env ve); simpl in *.
    consider (exprD' x e t); intros.
    { rewrite (exprD'_typeof _ _ H).
      rewrite H.
      rewrite typ_cast_typ_refl. reflexivity. }
    { consider (typeof x e); intros; auto.
      { unfold typ_cast_typ.
        destruct (typ_eq_odec t0 t); subst.
        { rewrite H. reflexivity. }
        { destruct (exprD' x e t0); auto. } } }
  Qed.

  Theorem exprD_App : forall ve t e args,
    exprD ve (App e args) t =
    match typeof (map (@projT1 _ _) ve) e with
      | None => None
      | Some tf =>
        match exprD ve e tf with
          | None => None
          | Some f =>
            (fix eval_args (tf : typ) (f : typD types nil tf) (args : list expr)
                 {struct args}
             : option (typD types nil t) :=
               match args with
                 | nil => typ_cast_val nil tf t f
                 | arg :: args =>
                   match tf as tf
                         return typD types nil tf -> option (typD types nil t)
                   with
                     | tvArr l r => fun f =>
                       match exprD ve arg l with
                         | None => None
                         | Some argv =>
                           eval_args r (f argv) args
                       end
                     | _ => fun _ => None
                   end f
               end) tf f args
        end
    end.
  Proof.
    intros; simpl.
    unfold exprD; simpl; intros.
    rewrite <- split_env_projT1.
    destruct (split_env ve); simpl in *; intros.
    destruct (typeof x e); auto.
    destruct (exprD' x e t0); auto.
    clear. generalize dependent t0.
    induction args; simpl; intros.
    { unfold typ_cast_val.
      destruct (typ_cast_typ types (fun x0 : Type => x0) nil t0 t); auto. }
    { destruct t0; auto.
      destruct (exprD' x a t0_1); auto.
      rewrite IHargs. reflexivity. }
  Qed.

  Fixpoint anyb {T} (p : T -> bool) (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls => if p l then true else anyb p ls
    end.

  Fixpoint mentionsU (u : nat) (e : expr) {struct e} : bool :=
    match e with
      | Var _
      | Func _ _ => false
      | UVar u' => EqNat.beq_nat u u'
      | App f es =>
        if mentionsU u f then true else
          (fix anyb ls : bool :=
            match ls with
              | nil => false
              | l :: ls => if mentionsU u l then true else anyb ls
            end) es
      | Abs _ e => mentionsU u e
      | Equal _ e1 e2 => if mentionsU u e1 then true else mentionsU u e2
      | Not e => mentionsU u e
    end.

  Fixpoint expr_eq_dec (e1 e2 : expr) : bool.
  refine (
    match e1 , e2 with
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
      | Func f1 ts1 , Func f2 ts2 =>
        if EqNat.beq_nat f1 f2 then
          ts1 ?[ eq ] ts2
        else false
      | App f1 es1 , App f2 es2 =>
        if expr_eq_dec f1 f2 then
          (fix check es1 es2 : bool :=
            match es1 , es2 with
              | nil , nil => true
              | e1 :: es1 , e2 :: es2 =>
                if expr_eq_dec e1 e2 then check es1 es2 else false
              | _ , _ => false
            end) es1 es2
        else
          false
      | Abs t1 e1 , Abs t2 e2 =>
        if t1 ?[ eq ] t2 then expr_eq_dec e1 e2
        else false
      | Equal t1 e1 e2 , Equal t1' e1' e2' =>
        if t1 ?[ eq ] t1' then
          if expr_eq_dec e1 e1' then
            if expr_eq_dec e2 e2' then true
            else false
          else false
        else false
      | Not e1 , Not e2 => expr_eq_dec e1 e2
      | _ , _ => false
    end).
  Defined.

  Theorem expr_eq_dec_eq : forall e1 e2,
    expr_eq_dec e1 e2 = true <-> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros; try solve [ intuition congruence ].
    { consider (EqNat.beq_nat v v0); intros; subst; intuition. inversion H0; subst; auto. }
    { consider (EqNat.beq_nat f f0); intros; subst.
      { change (ts ?[ eq ] l = true <-> Func f0 ts = Func f0 l).
        consider (ts ?[ eq ] l). intros; subst. intuition.
        intuition congruence. }
      { intuition congruence. } }
    { consider (EqNat.beq_nat v u); subst; intuition congruence. }
    { consider (expr_eq_dec e1 e2); intros.
      { eapply IHe1 in H0. subst.
        generalize dependent l. clear - H.
        induction H; simpl; intros.
        { destruct l; intuition congruence. }
        { destruct l0; try intuition congruence.
          consider (expr_eq_dec x e).
          rewrite IHForall. intros. eapply H in H1. subst; f_equal.
          intuition; inversion H1; subst; auto.
          intros. intuition.
          inversion H2; subst.
          rewrite <- H1. eapply H. reflexivity. } }
      { intuition. inversion H1; subst. rewrite <- H0. apply IHe1. reflexivity. } }
    { change typ_eqb with (@rel_dec _ _ _) in *. consider (t ?[ eq ] t0).
      intros; subst. intuition try congruence.
      eapply IHe1 in H; congruence.
      inversion H; subst.
      eapply IHe1. reflexivity.
      intros. intuition congruence. }
    { change typ_eqb with (@rel_dec _ _ _) in *.
      specialize (IHe1_1 e2_1). specialize (IHe1_2 e2_2).
      consider (t ?[ eq ] t0);
      consider (expr_eq_dec e1_1 e2_1);
      consider (expr_eq_dec e1_2 e2_2); intros; subst; intuition try congruence; subst.
      inversion H5; subst; auto.
      inversion H4; subst; auto.
      inversion H2; subst; auto. }
    { rewrite IHe1. intuition congruence. }
  Qed.

  Global Instance RelDec_eq_expr : RelDec (@eq expr) :=
  { rel_dec := expr_eq_dec }.

  Global Instance RelDecCorrect_eq_expr : RelDec_Correct RelDec_eq_expr.
  Proof.
    constructor. eapply expr_eq_dec_eq.
  Qed.

End env.

Section expr.
  Variable types : types.

  Instance Expr_expr (fs : functions types) : Expr (typD types) expr :=
  { exprD := exprD fs
  ; acc := expr_acc
  ; wf_acc := wf_expr_acc
  }.
End expr.
