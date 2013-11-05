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
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.
Require MirrorCore.SealedSubst.
Require Import mtac.Patterns.

(** This is just a default. Most users won't want/want
 ** to chnage this, but if there is a better substitution
 ** available we should change to use that.
 **)
Require MirrorCore.Ext.FMapSubst.

Set Implicit Arguments.
Set Strict Implicit.

(** The basic McMtac monad just keeps data about the
 ** current context and a fuel parameter that we'll use for unification.
 **)
Record McEnv : Type :=
{ mtac_tfuncs : tfunctions
; mtac_tus  : EnvI.tenv typ
; mtac_tvs  : EnvI.tenv typ
; mtac_fuel : nat
}.

Definition McMtacT := readerT McEnv.

Definition runMcMtac {T} {m : Type -> Type} (fs : tfunctions)
           (tus tvs : EnvI.tenv typ)
           (fuel : nat) (cmd : McMtacT m T) : m T :=
  runReaderT cmd {| mtac_tfuncs := fs
                  ; mtac_tus := tus
                  ; mtac_tvs := tvs
                  ; mtac_fuel := fuel |}.

(** Monad Instances **)
Global Instance Monad_McMtac m (M : Monad m) : Monad (McMtacT m) := _.
Global Instance MonadT_McMtac m (M : Monad m) : MonadT (McMtacT m) m := _.
(** Do not expose the reader instance **)
Instance MonadReader_McMtac m (M : Monad m) : MonadReader McEnv (McMtacT m) := _.


(** Use phantom types for **)
Definition mc_expr (t : typ) : Type := expr.

Definition subst := SealedSubst.seal_subst FMapSubst.SUBST.subst.
Local Instance Subst_subst : Subst.Subst subst expr :=
  @SealedSubst.Subst_seal_subst _ _ FMapSubst.SUBST.Subst_subst.
Definition empty_above (above : uvar) : subst :=
  SealedSubst.seal (fun x => above ?[ le ] x)
                   (@Subst.empty _ _ FMapSubst.SUBST.Subst_subst).

Section over_monad.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.

  (** Typeof **)
  Definition typeof (t : expr) : McMtacT m (option typ) :=
    bind (Monad := Monad_McMtac Monad_m) ask (fun env =>
      let tf := env.(mtac_tfuncs) in
      let tus := env.(mtac_tus) in
      let tvs := env.(mtac_tvs) in
      let fuel := env.(mtac_fuel) in
      ret (typeof_expr tf tus tvs t)).

  (** Pattern matching **)
  Context {T : Type}.

  Fixpoint arm_result (ls : list typ) : Type :=
    match ls with
      | nil => McMtacT m T
      | l :: ls => mc_expr l -> arm_result ls
    end.

  Inductive Branch : Type :=
  | Case (p : mpattern) (d : match binders_of_mpattern p with
                               | None => unit (** ill-typed pattern **)
                               | Some p => arm_result p
                             end).

  Let arm_type :=
    nat -> list typ -> list typ -> (unit -> McMtacT m T) -> expr -> typ -> McMtacT m T.

  Definition arm_result_apply (s : subst) (error : unit -> McMtacT m T)
  : nat -> forall ls : list typ, arm_result ls -> McMtacT m T :=
    (fix recur (from : nat) (ls : list typ) : arm_result ls -> McMtacT m T :=
       match ls with
         | nil => fun x => x
         | l :: ls => fun f =>
                        match Subst.lookup from s with
                          | None => error tt
                          | Some e => recur (S from) ls (f e)
                        end
       end).

  Definition BranchD (tfs : tfunctions) (a : Branch)
  : arm_type :=
    match a with
      | Case p case =>
        match binders_of_mpattern p as v
          return match v with
                   | None => unit
                   | Some ps => arm_result ps
                 end -> arm_type
        with
          | None => fun _ _ _ _ error _ _ => error tt
          | Some pus => fun case fuel tus tvs error e ty =>
            let count_tus := length tus in
            let p' := expr_of_mpattern count_tus p in
            match
              @exprUnify subst _ tfs fuel (tus ++ pus) tvs 0
                         (empty_above count_tus)
                         e p' ty
            with
              | None => error tt
              | Some sub =>
                @arm_result_apply sub error count_tus
                                 _ case
            end
        end case
    end.

  Definition _mmatchAt
             (e: expr) (ty : typ)
             (ls : list Branch)
             (default : McMtacT m T) : McMtacT m T :=
    bind (Monad := Monad_McMtac Monad_m) ask (fun env =>
                let tf := env.(mtac_tfuncs) in
                let tus := env.(mtac_tus) in
                let tvs := env.(mtac_tvs) in
                let fuel := env.(mtac_fuel) in
                (fix find_pattern (pats : list Branch)  : McMtacT m T :=
                   match pats with
                     | nil => default
                     | b :: ps =>
                       BranchD tf b fuel tus tvs (fun t =>
                                                    match t with
                                                      | tt => find_pattern ps
                                                    end) e ty
                   end) ls).

  Definition _mmatch
             (e : expr)
             (ls : list Branch)
             (default : McMtacT m T) : McMtacT m T :=
    bind (Monad := Monad_McMtac Monad_m) ask (fun env =>
                let tf := env.(mtac_tfuncs) in
                let tus := env.(mtac_tus) in
                let tvs := env.(mtac_tvs) in
                let fuel := env.(mtac_fuel) in
                match typeof_expr tf tus tvs e with
                  | None => default
                  | Some ty =>
                    (fix find_pattern (pats : list Branch)  : McMtacT m T :=
                       match pats with
                         | nil => default
                         | b :: ps =>
                           BranchD tf b fuel tus tvs (fun t =>
                                                        match t with
                                                          | tt => find_pattern ps
                                                        end) e ty
                       end) ls
                end).
End over_monad.

Arguments Case {_ _} _ _.
Arguments _mmatchAt {_ _ _} _ _ _ _.

Module McMtacNotation.
  Delimit Scope mcmtac_scope with mcmtac.
  Delimit Scope mcpattern_scope with mcmtac_pattern.
  Notation "[  x  ]  '=>>' e" :=
    (@Case _ _ x e%mcmtac)
      (at level 50) : mcpattern_scope.
  Delimit Scope mcpatterns_scope with mcmtac_patterns.
  Notation "| p1 | .. | p2" :=
    (@cons (@Branch _ _) p1%mcmtac_pattern ..
           (@cons (@Branch _ _) p2%mcmtac_pattern nil) ..)
      (at level 50) : mcpatterns_scope.
  Notation "'mmatch' t 'with' ps \ e 'end'" :=
    (@_mmatch _ _ _ t ps%mcmtac_patterns e%mcmtac) (at level 50) : mcmtac_scope.

  Notation "'mmatch' t '@' ty 'with' ps \ e 'end'" :=
    (@_mmatchAt _ _ _ t ty ps%mcmtac_patterns e%mcmtac) (at level 50) : mcmtac_scope.

  (** Morally, this is just [e] **)
  Notation "'mmatch' t 'with' \ e 'end'" :=
    (@_mmatch _ _ _ t nil e%mcmtac) (at level 50) : mcmtac_scope.

  Notation "'mmatch' t '@' ty 'with' \ e 'end'" :=
    (@_mmatchAt _ _ _ t ty nil e%mcmtac) (at level 50) : mcmtac_scope.

(*
  Eval cbv iota in ([ PVar 0 ] =>> ret true)%mcmtac_pattern.
  Eval cbv iota in ([ PGet 0 (tvType 0) ] =>> ret)%mcmtac_pattern.

  Eval cbv iota in (fun x => mmatch x with
                               | [ PGet 0 (tvType 0) ] =>> fun x => ret true
                               \ ret false
                             end)%mcmtac.

  Eval cbv iota in (fun x => mmatch x with
                               \ ret false
                             end)%mcmtac.
*)
End McMtacNotation.
