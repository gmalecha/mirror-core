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
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Vector.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprUnifySyntactic.
Require MirrorCore.SealedSubst.

(** This is just a default. Most users won't want/want
 ** to chnage this, but if there is a better substitution
 ** available we should change to use that.
 **)
Require MirrorCore.Ext.FMapSubst.

Set Implicit Arguments.
Set Strict Implicit.

Record McEnv : Type :=
{ mtac_tfuncs : tfunctions
; mtac_tus  : EnvI.tenv typ
; mtac_tvs  : EnvI.tenv typ
; mtac_fuel : nat
}.

Definition McMtacT := readerT McEnv.

Definition runMcMtac {T} {m : Type -> Type} (fs : tfunctions) (tus tvs : EnvI.tenv typ)
           (fuel : nat) (cmd : McMtacT m T) : m T :=
  runReaderT cmd {| mtac_tfuncs := fs
                  ; mtac_tus := tus
                  ; mtac_tvs := tvs
                  ; mtac_fuel := fuel |}.

Global Instance Monad_McMtac m (M : Monad m) : Monad (McMtacT m) := _.
Instance MonadReader_McMtac m (M : Monad m) : MonadReader McEnv (McMtacT m) := _.
Global Instance MonadT_McMtac m (M : Monad m) : MonadT (McMtacT m) m := _.

Definition mc_expr (t : typ) : Type := expr.

Inductive mpattern :=
| PGet (i : nat) (t : typ)
| PVar (v : nat)
| PUVar (u : uvar)
| PFunc (f : func) (ls : list typ)
| PApp (l r : mpattern)
| PAbs (t : typ) (e : mpattern)
| PEqual (t : typ) (l r : mpattern)
| PNot (e : mpattern).

Fixpoint typeof_mpattern (tfs : tfunctions) (tus tvs : list typ) (p : mpattern)
: option typ :=
  match p with
    | PGet _ t => Some t
    | PVar v => nth_error tvs v
    | PUVar u => nth_error tus u
    | PFunc f ts =>
      match nth_error tfs f with
        | Some r =>
          if EqNat.beq_nat (length ts) (tfenv r)
          then Some (instantiate_typ ts (tftype r))
          else None
        | None => None
      end
    | PApp l r =>
      bind (typeof_mpattern tfs tus tvs l)
           (fun tf =>
              bind (typeof_mpattern tfs tus tvs r) (type_of_apply tf))
    | PAbs t e =>
      bind (typeof_mpattern tfs tus (t :: tvs) e)
           (fun t' => ret (tvArr t t'))
    | PEqual t l r =>
      bind (typeof_mpattern tfs tus tvs l)
           (fun tl => bind (typeof_mpattern tfs tus tvs r)
                           (fun tr => if andb (t ?[ eq ] tl) (t ?[ eq ] tr)
                                      then Some tvProp else None))
    | PNot e =>
      bind (typeof_mpattern tfs tus tvs e)
           (fun tl => if tl ?[ eq ] tvProp then Some tvProp else None)
  end.

Definition expr_of_mpattern (Ubase : uvar) : mpattern -> expr :=
  fix recur (p : mpattern) : expr :=
  match p with
    | PGet u _ => UVar (Ubase + u)
    | PVar v => Var v
    | PUVar v => UVar v
    | PFunc f ts => Func f ts
    | PApp l r => App (recur l) (recur r)
    | PAbs t e => Abs t (recur e)
    | PEqual t l r => Equal t (recur l) (recur r)
    | PNot e => Not (recur e)
  end.

Fixpoint list_set (n : nat) (t : typ) (ls : list (option typ))
: list (option typ) :=
  match n with
    | 0 => Some t :: tl ls
    | S n => match ls with
               | nil => None :: list_set n t nil
               | t' :: ts => t' :: list_set n t ts
             end
  end.

Fixpoint getEnv (p : mpattern) (ls : list (option typ)) : list (option typ) :=
  match p with
    | PGet u t => list_set u t ls
    | PVar _ => ls
    | PFunc _ _ => ls
    | PApp l r => getEnv l (getEnv r ls)
    | PAbs _ e => getEnv e ls
    | PUVar _ => ls
    | PEqual _ l r => getEnv l (getEnv r ls)
    | PNot e => getEnv e ls
  end.

Definition binders_of_mpattern (ptrn : mpattern) : option (list typ) :=
  mapT (fun x => x) (getEnv ptrn nil).

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
