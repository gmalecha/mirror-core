Require Import List.
Require Import Relations.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section subst.
  Variable T : Type.
  Variable expr : Type.
  Let uvar : Type := nat.

  Class Subst :=
  { set : uvar -> expr -> T -> option T
  ; lookup : uvar -> T -> option expr
  ; subst : T -> expr -> expr
  }.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : Expr typD expr.

  Class SubstOk (S : Subst) : Type :=
  { substD : EnvI.env typD -> EnvI.env typD -> T -> Prop
  ; substD_subst : forall u v s e t,
                     substD u v s ->
                     exprD u v e t = exprD u v (subst s e) t
  ; substD_lookup : forall u v s uv e,
                      lookup uv s = Some e ->
                      substD u v s ->
                      exists val, nth_error u uv = Some val /\
                                  exprD u v e (projT1 val) = Some (projT2 val)
  ; substD_set : forall s s' uv e,
                   set uv e s = Some s' ->
                   forall u v val,
                     (substD u v s /\
                      nth_error u uv = Some val /\
                      exprD u v e (projT1 val) = Some (projT2 val)) <->
                     (substD u v s')
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.

  Definition Subst_Extends (a b : T) : Prop :=
    forall u v, substD u v b -> substD u v a.

  (** the [expr] type requires a notion of unification variable **)

(*
  Class SubstOk :=
  { Subst_WellTyped : tfunctions -> tenv -> tenv -> T -> Prop
  ; Subst_Extends : relation T
  ; PreOrder_Subst_Extends : PreOrder Subst_Extends
  }.
*)

(*
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
*)

(*


Section map_subst.
  Variable m : Type -> Type.
  Require Import ExtLib.Structures.Maps.
  Variable ts : types.

  *)
End subst.
