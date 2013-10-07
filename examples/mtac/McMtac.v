(** The core definitions of the "mtac" monad.
 **
 ** Here, we only provide the [mmatch] feature, other features
 ** of the monad can be achieved using monad transformers, e.g.
 ** - non-termination
 ** - exceptions
 ** - backtracking
 **
 ** It may also be desireable to add a hook to resolve, e.g.
 ** type-class instances through a hint database.
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Vector.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.

Set Implicit Arguments.
Set Strict Implicit.

Record McEnv : Type :=
{ mtac_tfuncs : tfunctions
; mtac_tus  : EnvI.tenv typ
; mtac_tvs  : EnvI.tenv typ
; mtac_fuel : nat
}.

Definition McMtac := reader McEnv.

Global Instance Monad_McMtac : Monad McMtac := _.
Instance MonadReader_McMtac : MonadReader McEnv McMtac := _.

Definition mc_expr (t : Type) : Type := expr.

Definition mpattern := expr.

Fixpoint vars_of_mpattern (p : mpattern) : nat :=
  match p with
    | Var _
    | Func _ _ => 0
    | App l r => max (vars_of_mpattern l) (vars_of_mpattern r)
    | Abs _ e => vars_of_mpattern e
    | UVar u => u
    | Equal _ l r => max (vars_of_mpattern l) (vars_of_mpattern r)
    | Not e => vars_of_mpattern e
  end.

Section exp_app.

  Variables D R : Type.

  Fixpoint exp n : Type :=
    match n with
      | 0 => R
      | S n => D -> exp n
    end.

  Variable M : Type -> Type.
  Variable Monad_M : Monad M.
  Variable arg : nat -> M D.

  Fixpoint exp_app {n} : exp n -> M R :=
    match n as n return exp n -> M R with
      | 0 => ret
      | S n' => fun f =>
                 bind (arg n) (fun a => exp_app (f a))
    end.

  Fixpoint exp_app_vector {n} (vs : vector D n) : exp n -> R :=
    match vs in vector _ n return exp n -> R with
      | Vnil => fun x => x
      | Vcons _ v vs => fun f => exp_app_vector vs (f v)
    end.
End exp_app.

Fixpoint lift_uvars' (us uadd : nat) (e : expr) : expr :=
  match e with
    | Var _
    | Func _ _ => e
    | App l r => App (lift_uvars' us uadd l) (lift_uvars' us uadd l)
    | Abs t e => Abs t (lift_uvars' us uadd e)
    | UVar u => UVar (if u ?[ lt ] us then u
                      else u + uadd)
    | Equal t l r => Equal t (lift_uvars' us uadd l) (lift_uvars' us uadd r)
    | Not e => Not (lift_uvars' us uadd e)
  end.

Definition lift_uvars (us uadd : nat) (e : expr) : expr :=
  match uadd with
    | 0 => e
    | _ => lift_uvars' us uadd e
  end.

Parameter subst : Type.
Parameter Subst_subst : Subst.Subst subst expr.
Parameter empty_subst : subst.

Fixpoint get_args_from sub from cnt : option (vector expr cnt) :=
  match cnt with
    | 0 => Some (Vnil _)
    | S n =>
      match Subst.lookup from sub with
        | None => None
        | Some a => match get_args_from sub (S from) n with
                      | None => None
                      | Some x => Some (Vcons a x)
                    end
      end
  end.

Definition mmatch {T}
           (t : expr)
           (ls : list { p : mpattern & exp expr (McMtac T) (vars_of_mpattern p) })
           (default : McMtac T) : McMtac T :=
  bind ask (fun env =>
              let tf := env.(mtac_tfuncs) in
              let tus := env.(mtac_tus) in
              let tvs := env.(mtac_tvs) in
              let fuel := env.(mtac_fuel) in
              match typeof_expr tf tus tvs t with
                | None => default
                | Some ty =>
                  (fix find_pattern (pats : list { p : mpattern & exp expr (McMtac T) (vars_of_mpattern p) })  : McMtac T :=
                     match pats with
                       | nil => default
                       | (existT p case) :: ps =>
                         let var_count := vars_of_mpattern p in
                         let p := lift_uvars (length tus) (length tus) p in
                         match
                           @exprUnify subst _ tf fuel tus tvs (length tvs) empty_subst
                                      t p ty
                         with
                           | None => find_pattern ps
                           | Some sub =>
                             match
                               get_args_from sub (length tus) var_count
                             with
                               | Some args =>
                                 @exp_app_vector _ (McMtac T) var_count args case
                               | None => find_pattern ps
                             end
                         end
                     end) ls
              end).
