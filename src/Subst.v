Require Import List.
Require Import Relations.
Require Import Expr.

Section subst.
  Variable ts : types.
  Variable T : Type.

  Class Subst :=
  { set : uvar -> expr ts -> T -> option T
  ; lookup : uvar -> T -> option (expr ts)
  }.

  Section instantiate.
    Variable Subst_T : Subst.

    Variable subst : T.

    Fixpoint exprInstantiate (l : nat) (e : expr ts) : expr ts :=
      match e with
        | Const _ _ => e
        | Var _ => e
        | Func _ _ => e
        | App e es => App (exprInstantiate l e) (map (exprInstantiate l) es)
        | Abs t e => Abs t (exprInstantiate (S l) e)
        | UVar u =>
          match lookup u subst with
            | None => e
            | Some e' => lift 0 l e'
          end
        | Equal t e1 e2 => Equal t (exprInstantiate l e1) (exprInstantiate l e2)
        | Not e => Not (exprInstantiate l e)
      end.
  End instantiate.

(*

  Class SubstOk :=
  { Subst_WellTyped : tfunctions -> tenv -> tenv -> T -> Prop
  ; Subst_Extends : relation T
  ; PreOrder_Subst_Extends : PreOrder Subst_Extends
  }.

Section map_subst.
  Variable m : Type -> Type.
  Require Import ExtLib.Structures.Maps.
  Variable ts : types.

  *)
End subst.
