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
Require Import ExtLib.Data.List.
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

Definition runMcMtac {T} (fs : tfunctions) (tus tvs : EnvI.tenv typ)
           (fuel : nat) (cmd : McMtac T) : T :=
  runReader cmd {| mtac_tfuncs := fs
                 ; mtac_tus := tus
                 ; mtac_tvs := tvs
                 ; mtac_fuel := fuel |}.

Global Instance Monad_McMtac : Monad McMtac := _.
Instance MonadReader_McMtac : MonadReader McEnv McMtac := _.

Definition mc_expr (t : Type) : Type := expr.

Definition mpattern := expr.

Definition omax (l r : option nat) : option nat :=
  match l , r with
    | Some l , Some r => Some (max l r)
    | None , r => r
    | l , None => l
  end.

Fixpoint vars_of_mpattern (p : mpattern) : option nat :=
  match p with
    | Var _
    | Func _ _ => None
    | App l r => omax (vars_of_mpattern l) (vars_of_mpattern r)
    | Abs _ e => vars_of_mpattern e
    | UVar u => Some u
    | Equal _ l r => omax (vars_of_mpattern l) (vars_of_mpattern r)
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

Require MirrorCore.SealedSubst.
Require MirrorCore.Ext.FMapSubst.

Definition subst := SealedSubst.seal_subst FMapSubst.SUBST.subst.
Local Instance Subst_subst : Subst.Subst subst expr :=
  @SealedSubst.Subst_seal_subst _ _ FMapSubst.SUBST.Subst_subst.
Definition empty_above (above : uvar) : subst :=
  SealedSubst.seal (fun x => above ?[ le ] x)
                   (@Subst.empty _ _ FMapSubst.SUBST.Subst_subst).

Fixpoint get_args_from (sub : subst) from cnt : option (vector expr cnt) :=
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

Inductive Branch (T : Type) : Type :=
| Case (p : mpattern) (d : match vars_of_mpattern p with
                             | None => McMtac T
                             | Some p => exp expr (McMtac T) (S p)
                           end).

Definition typeof (t : expr) : McMtac (option typ) :=
  bind (Monad := Monad_McMtac) ask (fun env =>
              let tf := env.(mtac_tfuncs) in
              let tus := env.(mtac_tus) in
              let tvs := env.(mtac_tvs) in
              let fuel := env.(mtac_fuel) in
              ret (typeof_expr tf tus tvs t)).

Definition _mmatchAt {T}
           (e: expr) (ty : typ)
           (ls : list (Branch T))
           (default : McMtac T) : McMtac T :=
  bind (Monad := Monad_McMtac) ask (fun env =>
              let tf := env.(mtac_tfuncs) in
              let tus := env.(mtac_tus) in
              let tvs := env.(mtac_tvs) in
              let fuel := env.(mtac_fuel) in
              (fix find_pattern (pats : list (Branch T))  : McMtac T :=
                 match pats with
                   | nil => default
                   | Case p case :: ps =>
                     let p' := lift_uvars (length tus) (length tus) p in
                     match
                       @exprUnify subst _ tf fuel tus tvs 0
                                  (empty_above (length tus))
                                  e p' ty
                     with
                       | None => find_pattern ps
                       | Some sub =>
                         match vars_of_mpattern p as vs
                           return match vs with
                                    | None => McMtac T
                                    | Some p => exp expr (McMtac T) (S p)
                                  end -> McMtac T
                         with
                           | None => fun x => x
                           | Some var_count => fun case =>
                             match
                               get_args_from sub (length tus) (S var_count)
                             with
                               | Some args =>
                                 @exp_app_vector _ (McMtac T) (S var_count) args case
                               | None => find_pattern ps
                             end
                         end case
                     end
                 end) ls).

Definition _mmatch {T}
           (t : expr)
           (ls : list (Branch T))
           (default : McMtac T) : McMtac T :=
  bind (Monad := Monad_McMtac) ask (fun env =>
              let tf := env.(mtac_tfuncs) in
              let tus := env.(mtac_tus) in
              let tvs := env.(mtac_tvs) in
              let fuel := env.(mtac_fuel) in
              match typeof_expr tf tus tvs t with
                | None => default
                | Some ty =>
                  (fix find_pattern (pats : list (Branch T))  : McMtac T :=
                     match pats with
                       | nil => default
                       | Case p case :: ps =>
                         let p' := lift_uvars (length tus) (length tus) p in
                         match
                           @exprUnify subst _ tf fuel tus tvs 0
                                      (empty_above (length tus))
                                      t p' ty
                         with
                           | None => find_pattern ps
                           | Some sub =>
                             match vars_of_mpattern p as vs
                                   return match vs with
                                            | None => McMtac T
                                            | Some p => exp expr (McMtac T) (S p)
                                          end -> McMtac T
                             with
                               | None => fun x => x
                               | Some var_count => fun case =>
                                 match
                                   get_args_from sub (length tus) (S var_count)
                                 with
                                   | Some args =>
                                     @exp_app_vector _ (McMtac T) (S var_count) args case
                                   | None => find_pattern ps
                                 end
                             end case
                         end
                     end) ls
              end).

Module McMtacNotation.
  Delimit Scope mcmtac_scope with mcmtac.
  Delimit Scope mcpattern_scope with mcmtac_pattern.
  Notation "[  x  ]  '=>>' e" :=
    (@Case _ x e%mcmtac)
      (at level 50) : mcpattern_scope.
  Delimit Scope mcpatterns_scope with mcmtac_patterns.
  Notation "| p1 | .. | p2" :=
    (@cons (@Branch _) p1%mcmtac_pattern ..
           (@cons (@Branch _) p2%mcmtac_pattern nil) ..)
      (at level 50) : mcpatterns_scope.
  Notation "'mmatch' t 'with' ps \ e 'end'" :=
    (@_mmatch _ t ps%mcmtac_patterns e%mcmtac) (at level 50) : mcmtac_scope.

  Notation "'mmatch' t '@' ty 'with' ps \ e 'end'" :=
    (@_mmatchAt _ t ty ps%mcmtac_patterns e%mcmtac) (at level 50) : mcmtac_scope.

  (** Morally, this is just [e] **)
  Notation "'mmatch' t 'with' \ e 'end'" :=
    (@_mmatch _ t nil e%mcmtac) (at level 50) : mcmtac_scope.

(*
  Eval cbv iota in ([ Var 0 ] =>> ret true)%mcmtac_pattern.
  Eval cbv iota in ([ UVar 0 ] =>> ret)%mcmtac_pattern.

  Eval cbv iota in (fun x => mmatch x with
                               | [ UVar 0 ] =>> fun x => ret true
                               \ ret false
                             end)%mcmtac.

  Eval cbv iota in (fun x => mmatch x with
                               \ ret false
                             end)%mcmtac.
*)
End McMtacNotation.
