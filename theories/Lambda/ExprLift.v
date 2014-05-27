Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Option.
Require Import MirrorCore.Lambda.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section types.
  Variable typ : Type.
  Variable func : Type.

  Fixpoint lower (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : option (expr typ func) :=
    match e with
      | Var v => if v ?[ lt ] skip then Some (Var v)
                          else if (v - skip) ?[ lt ] _by then None
                               else Some (Var (v - _by))
      | Inj f => Some (Inj f)
      | UVar u => Some (UVar u)
      | App a b =>
        ap (ap (pure App) (lower skip _by a)) (lower skip _by b)
      | Abs t a =>
        ap (pure (Abs t)) (lower (S skip) _by a)
    end.

  Fixpoint lift (skip : nat) (_by : nat) (e : expr typ func) {struct e}
  : expr typ func :=
    match e with
      | Var v => Var (if v ?[ lt ] skip then v else (v + _by))
      | Inj f => Inj f
      | UVar u => UVar u
      | App a b =>
        App (lift skip _by a) (lift skip _by b)
      | Abs t a =>
        Abs t (lift (S skip) _by a)
    end.
End types.