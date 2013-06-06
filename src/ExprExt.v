Require Import List Bool.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Generic.
Require Import MirrorCore.Iso.
Require Import MirrorCore.TypesExt.

Set Implicit Arguments.
Set Strict Implicit.

Section Expr.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.

  Definition env : Type := list (sigT (typD nil)).

  Variable expr : Type.

  Class Expr : Type :=
  { exprD : env -> env -> expr -> forall t : typ, option (typD nil t)
  ; expr_eq : expr -> expr -> option bool
  }.

  Class ExprOk (E : Expr) : Type :=
  { expr_eqOk : forall a b, match expr_eq a b with
                              | None => True
                              | Some true => a = b
                              | Some false => a <> b
                            end
  }.

  Context {Expr_expr : Expr}.
  
  Class FuncInstance0 (T : Type) (F : T) : Type :=
  { typ0_witness : TypInstance0 typD T
  ; ctor0 : expr
  ; ctor0_iso : forall us vs P, 
      match exprD us vs ctor0 (@typ0 _ _ _ typ0_witness) with
        | None => False
        | Some G => P F <-> P (soutof (iso := typ0_iso nil) (fun x => x) G)
      end
  ; ctor0_match : forall (R : expr -> Type)
      (caseCtor : unit -> R ctor0)
      (caseElse : forall e, R e)
      (e : expr), R e
  }.

  (** I think something is missing for the iso **)
  Class FuncInstance1 (T : Type -> Type) (F : forall x, T x) : Type :=
  { typ1_witness : TypInstance1 typD T
  ; ctor1 : expr
  ; ctor1_iso : forall us vs t P, 
      match exprD us vs ctor1 (typ1 t) with
        | None => False
        | Some G => 
          P (F (typD nil t)) <-> P (soutof (iso := typ1_iso nil t) (fun x => x) G)
      end
  ; ctor1_match : forall (R : expr -> Type)
      (caseCtor : typ -> R ctor1)
      (caseElse : forall e, R e)
      (e : expr), R e
  }.

  Class FuncInstance2 (T : Type -> Type -> Type) (F : forall x y, T x y) : Type :=
  { typ2_witness : TypInstance2 typD T
  ; ctor2 : expr
  ; ctor2_iso : forall us vs t u P, 
      match exprD us vs ctor2 (typ2 t u) with
        | None => False
        | Some G => 
          P (F (typD nil t) (typD nil u)) <-> P (soutof (iso := typ2_iso nil t u) (fun x => x) G)
      end
  ; ctor2_match : forall (R : expr -> Type)
      (caseCtor : typ -> R ctor2)
      (caseElse : forall e, R e)
      (e : expr), R e
  }.
End Expr.