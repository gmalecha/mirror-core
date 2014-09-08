Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.ExprTac.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Variable Typ0_Prop : Typ0 _ Prop.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_eq_func : RelDec (@eq func)}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable Rbase : Type.
  Variable Req : Rbase -> Rbase -> bool.

  Inductive RG : Type :=
  | RGinj (r : Rbase)
  | RGrespects (l r : RG)
  | RGany (n : positive).

  Record rsubst :=
  { mp : PositiveMap.tree RG
  ; max : positive
  }.
  Definition rsubst_set (n : positive) (a : RG) (r : rsubst)
  : option (RG * rsubst) :=
    match PositiveMap.find n r.(mp) with
      | None =>
        Some (a, {| mp := PositiveMap.add n a r.(mp) ; max := r.(max) |})
      | Some _ => None
    end.

  Definition rsubst_lookup (r : rsubst) n : option RG :=
    PositiveMap.find n r.(mp).

  Definition rsubst_empty : rsubst :=
    {| mp := PositiveMap.empty _ ; max := 1 |}.

  Section unifyRG.
    Variable (unifyRG : RG -> RG -> rsubst -> option (RG * rsubst)).
    Fixpoint unifyRG' (l r : RG) (env : rsubst)
    : option (RG * rsubst) :=
      match l , r with
        | RGany n , RGany n' =>
          if n ?[ eq ] n' then Some (l, env)
          else match PositiveMap.find n env.(mp) with
                 | None => rsubst_set n r env
                 | Some l => match PositiveMap.find n' env.(mp) with
                               | None => rsubst_set n' l env
                               | Some _ => None
                             end
               end
        | RGany n , _ =>
          match PositiveMap.find n env.(mp) with
            | None => rsubst_set n r env
            | Some v => unifyRG v r env
          end
        | _ , RGany n =>
          match PositiveMap.find n env.(mp) with
            | None => rsubst_set n l env
            | Some v => unifyRG l v env
          end
        | RGinj l , RGinj r =>
          if Req l r then Some (RGinj l, env) else None
        | RGrespects la lb , RGrespects ra rb =>
          match unifyRG' la ra env with
            | Some (l',env') =>
              match unifyRG' lb rb env' with
                | Some (r',env'') => Some (RGrespects l' r', env'')
                | None => None
              end
            | None => None
          end
        | _ , _ => None
      end.
  End unifyRG.

  Fixpoint unifyRG_ (n : nat) (l r : RG) (env : rsubst)
  : option (RG * rsubst) :=
    match n with
      | 0 => None
      | S n => unifyRG' (fun l r env => unifyRG_ n l r env) l r env
    end.

  Definition unifyRG := unifyRG_ 10.

  Variable rw : expr typ func -> list RG -> RG -> rsubst ->
                option (expr typ func * rsubst).
  Variable rw_default : expr typ func -> list RG -> RG -> rsubst ->
                        option (expr typ func * rsubst).

  Definition rsubst_fresh (rs : rsubst) : (positive * rsubst) :=
    (rs.(max), {| mp := rs.(mp) ; max := rs.(max) + 1 |}).

  Axiom Z : option (expr typ func * rsubst).

  Fixpoint setoid_rewrite
           (e : expr typ func) (rvars : list RG) (rg : RG) (rs : rsubst)
  : option (expr typ func * rsubst).
  refine (
      match rw e rvars rg rs with
        | None =>
          match e with
            | App f x =>
              let (nxt,rs) := rsubst_fresh rs in
              match setoid_rewrite f rvars (RGrespects (RGany nxt) rg) rs with
                | None => None
                | Some (f', rs') =>
                  match setoid_rewrite x rvars (RGany nxt) rs' with
                    | None => None
                    | Some (x',rs'') => Some (App f' x',rs'')
                  end
              end
            | Abs t b =>
              match rg with
                | RGrespects l r =>
                  match setoid_rewrite b (l :: rvars) r rs with
                    | None => None
                    | Some (b',rs') =>
                      Some (Abs t b', rs')
                  end
                | RGany n =>
                  match rsubst_lookup rs n with
                    | None =>
                      let (l,rs) := rsubst_fresh rs in
                      let (r,rs) := rsubst_fresh rs in
                      match rsubst_set n (RGrespects (RGany l) (RGany r)) rs with
                        | None => None (* DEAD *)
                        | Some (_,rs') =>
                          match setoid_rewrite b (RGany l :: rvars) (RGany r) rs' with
                            | None => None
                            | Some (b',rs') => Some (Abs t b',rs')
                          end
                      end
                    | Some (RGrespects l r) =>
                      match setoid_rewrite b (l :: rvars) r rs with
                        | None => None
                        | Some (b',rs') =>
                          Some (Abs t b', rs')
                      end
                    | _ => None
                  end
                | _ => None
              end
            | Var v =>
              match nth_error rvars v with
                | None => None (** Dead code **)
                | Some r =>
                  match unifyRG r rg rs with
                    | None => rw_default e rvars rg rs
                    | Some (r',rs') =>
                      Some (Var v, rs')
                  end
              end
            | Inj _ => rw_default e rvars rg rs
            | UVar u => rw_default e rvars rg rs
          end
        | Some x => Some x
      end).
  Defined.

  (*
  (** This will be called on the head symbol to see what it
   ** respects
   **)
  Variable respects : expr typ func -> RG -> option RG.
  Variable is_reflexive : RG -> option RG.

  Definition try_reflexive (e : expr typ func)
             (rvars : list RG) (rg : RG)
  : option (expr typ func * list RG * RG) :=
    match is_reflexive rg with
      | None => None
      | Some r => Some (e, rvars, r)
    end.
*)

  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R).

  Fixpoint RtoRG (r : R) : RG :=
    match r with
      | Rinj r => RGinj r
      | Rrespects l r => RGrespects (RtoRG l) (RtoRG r)
    end.

  Fixpoint findRewrite (ls : list (expr typ func * RG * expr typ func))
           (e : expr typ func) (rg : RG) (rs : rsubst)
  : option (expr typ func * rsubst) :=
    match ls with
      | nil => None
      | (l,R,r) :: ls =>
        if l ?[ eq ] e then
          match unifyRG R rg rs with
            | None => findRewrite ls e rg rs
            | Some (_,rs') => Some (r,rs')
          end
        else
          findRewrite ls e rg rs
    end.

  Definition fromRewrites (ls : list (expr typ func * R * expr typ func))
  : forall (e : expr typ func) (rvars : list RG) (rg : RG) (rs : rsubst),
      option (expr typ func * rsubst) :=
    let ls := map (fun x => let '(a,b,c) := x in
                            (a,RtoRG b, c)) ls in
    fun e rvars => findRewrite ls e.

  Definition fromReflexive (is_refl : RG -> rsubst -> option rsubst)
  : forall (e : expr typ func) (rvars : list RG) (rg : RG) (rs : rsubst),
      option (expr typ func * rsubst) :=
    fun e rvars rg rs =>
      match is_refl rg rs with
        | None => None
        | Some rs' => Some (e, rs')
      end.

End setoid.
