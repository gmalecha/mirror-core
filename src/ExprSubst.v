Require Import List.
Require Import Relations.
Require Import ExprCore.
Require Import ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section substitute.
  Context {ts : types}.
    
  Fixpoint exprSubstVar (l : nat) (v : nat) (e' : expr ts) (e : expr ts) : expr ts :=
    match e with
      | Const _ _ => e
      | UVar _ => e
      | Func _ _ => e
      | App e es => App (exprSubstVar l v e' e) (map (exprSubstVar l v e') es)
      | Abs t e => Abs t (exprSubstVar (S l) v e' e)
      | Var v' => 
        match Compare_dec.nat_compare v v' with
          | Eq => lift 0 l e'
          | Lt => Var (v' - 1)
          | Gt => Var v'
        end
      | Equal t e1 e2 => Equal t (exprSubstVar l v e' e1) (exprSubstVar l v e' e2)
      | Not e => Not (exprSubstVar l v e' e)
    end.

End substitute.
