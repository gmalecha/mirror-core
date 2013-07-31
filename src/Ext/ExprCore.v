Require Import List Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fun.
Require Import MirrorCore.Generic.
Require Import MirrorCore.Iso.
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
(*            if EqNat.beq_nat (length ts) (fenv r) then  *)
              Some (instantiate_typ ts (ftype r))
(*
            else
              None
*)
        end
      | App e es =>
        match typeof var_env e with
          | None => None
          | Some tf =>
            foldM (fun e tf =>
                     Monad.bind (typeof var_env e) (type_of_apply tf))
                  (Monad.ret tf) es
        end
      | Abs t e =>
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal _ _ _ => Some tvProp
      | Not _ => Some tvProp
    end.

  Fixpoint type_apply (n : nat) (ls : list typ) (acc : list Type) (t : typ) {struct n} :
                 parametric n acc (fun env : list Type => typD types env t) ->
                 option (typD types acc (instantiate_typ ls t)) :=
    match n as n , ls as ls
          return parametric n acc (fun env : list Type => typD types env t) ->
                 option (typD types acc (instantiate_typ ls t))
    with
      | 0 , nil => fun f => Some f
      | S n , l :: ls => fun f =>
        match typD_subst0_typ _ _ _ _ in _ = t return option t with
          | eq_refl =>
            @type_apply n ls (typD types acc l :: acc) _ (f (typD types acc l))
        end
      | _ , _ => fun _ => None
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
            match type_apply _ ts' _ _ f.(fdenote) with
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

(*
  Definition const_seqb ts (a b : typ) (x : typD types ts a) (y : typD types ts b)
  : option bool :=
    match @typ_cast_val ts a b x with
      | None => None
      | Some x' => eqb ts b x' y
    end.
*)

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
    expr_eq_dec e1 e2 = true -> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros; try congruence.
    { consider (EqNat.beq_nat v v0); subst; auto. }
    { consider (EqNat.beq_nat f f0); intros; subst.
      revert H0.
      change (ts ?[ eq ] l = true -> Func f0 ts = Func f0 l).
      consider (ts ?[ eq ] l). intros; subst; reflexivity. }
    { consider (EqNat.beq_nat v u); subst; auto. }
    { consider (expr_eq_dec e1 e2); intros.
      f_equal; eauto. clear - H1 H.
      generalize dependent l; induction H.
      { destruct l; simpl; auto; try congruence. }
      { destruct l0; simpl; auto; try congruence.
        consider (expr_eq_dec x e); intros.
        f_equal; auto. } }
    { change typ_eqb with (@rel_dec _ _ _) in *. consider (t ?[ eq ] t0).
      intros; subst. f_equal; auto. }
    { change typ_eqb with (@rel_dec _ _ _) in *.
      consider (t ?[ eq ] t0);
      consider (expr_eq_dec e1_1 e2_1);
      consider (expr_eq_dec e1_2 e2_2); intros; subst.
      f_equal; auto. }
    { f_equal; auto. }
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
