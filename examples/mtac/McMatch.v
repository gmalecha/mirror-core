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
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.
Require MirrorCore.Subst.SealedSubst.
Require Import MirrorCore.Examples.mtac.Patterns.

(** This is just a default. Most users won't want/want
 ** to chnage this, but if there is a better substitution
 ** available we should change to use that.
 **)
(* Require MirrorCore.Subst.FMapSubst. *)

Set Implicit Arguments.
Set Strict Implicit.

Section with_func.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Variable subst' : Type.
  Variable Subst_subst' : Subst subst' (expr func).
  Definition subst := SealedSubst.seal_subst subst'.
  Local Instance Subst_subst : SubstI.Subst subst (expr func) :=
    @SealedSubst.Subst_seal_subst _ _ (Subst_subst').
  Definition empty_above (above : uvar) : subst :=
    SealedSubst.seal (fun x => above ?[ le ] x)
                     (@SubstI.empty _ _ _).

  (** Pattern matching **)
  Context {T : Type}.

  Fixpoint arm_result (ls : list typ) : Type :=
    match ls with
      | nil => T
      | l :: ls => expr func -> arm_result ls
    end.

  Inductive Branch : Type :=
  | Case (p : mpattern func)
         (d : match binders_of_mpattern p with
                | None => unit (** ill-typed pattern **)
                | Some p => arm_result p
              end).

  Let arm_type :=
    nat -> list typ -> list typ -> (unit -> T) -> expr func -> typ -> T.

  Definition arm_result_apply (s : subst) (error : unit -> T)
  : nat -> forall ls : list typ, arm_result ls -> T :=
    (fix recur (from : nat) (ls : list typ) : arm_result ls -> T :=
       match ls with
         | nil => fun x => x
         | l :: ls => fun f =>
                        match SubstI.lookup from s with
                          | None => error tt
                          | Some e => recur (S from) ls (f e)
                        end
       end).

  Definition BranchD (a : Branch)
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
              @exprUnify subst _ _ _ _ fuel (tus ++ pus) tvs 0
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
             (tus tvs : list typ) (fuel : nat)
             (e: expr func) (ty : typ)
             (ls : list Branch)
             (default : T) : T :=
    (fix find_pattern (pats : list Branch)  : T :=
       match pats with
         | nil => default
         | b :: ps =>
           BranchD b fuel tus tvs (fun t =>
                                     match t with
                                       | tt => find_pattern ps
                                     end) e ty
       end) ls.

  Definition _mmatch
             (tus tvs : list typ) (fuel : nat)
             (e : expr func)
             (ls : list Branch)
             (default : T) : T :=
    match typeof_expr tus tvs e with
      | None => default
      | Some ty =>
        (fix find_pattern (pats : list Branch)  : T :=
           match pats with
             | nil => default
             | b :: ps =>
               BranchD b fuel tus tvs (fun t =>
                                         match t with
                                           | tt => find_pattern ps
                                         end) e ty
           end) ls
    end.
End with_func.

Arguments Case {_ _} _ _.
Arguments _mmatchAt {_ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments _mmatch {_ _ _ _ _ _} _ _ _ _ _ _.

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
