(* This is a demo of developing a cancellation algorithm for
 * commutative monoids.
 *)
Require Import ExtLib.Data.Fun.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Simple.
Require Import MirrorCore.Reify.Reify.

Require Import McExamples.Cancel.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Module Syntax (M : Monoid).

  (** Define the reified language *)
  (********************************)

  (* The syntax of types *)
  Inductive typ : Set :=
  | tyArr : typ -> typ -> typ
  | tyNat | tyM
  | tyProp.

  (* The meaning of types *)
  Fixpoint typD (t : typ) : Type :=
    match t with
    | tyNat => nat
    | tyM => M.M
    | tyProp => Prop
    | tyArr a b => typD a -> typD b
    end.

  (* The accessibility relation *)
  Inductive tyAcc' : typ -> typ -> Prop :=
  | tyArrL : forall a b, tyAcc' a (tyArr a b)
  | tyArrR : forall a b, tyAcc' b (tyArr a b).

  Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* Instantiate the RType interface *)
  Instance RType_typ : RType typ := RType_simple typD tyAcc' typ_eq_dec.
  Instance RTypeOk_typ : RTypeOk := RTypeOk_simple _.
  Proof. prove_simple_acc. Defined.

  (* Build instances for describing functions and Prop *)
  Instance Typ2_tyArr : Typ2 RType_typ Fun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match T t tr :=
      match t as t return T (typD t) -> T (typD t) with
      | tyArr a b => fun _ => tr a b
      | _ => fun fa => fa
      end }.

  Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
  Proof. prove_TypOk. Defined.

  Instance Typ0_tyProp : Typ0 RType_typ Prop :=
  { typ0 := tyProp
  ; typ0_cast := eq_refl
  ; typ0_match T t :=
      match t with
      | tyProp => fun tr _ => tr
      | _ => fun _ fa => fa
      end }.

  Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp.
  Proof. prove_TypOk. Defined.

  (* The syntax of terms *)
  Inductive func' :=
  | Eq : typ -> func' (* polymorphic equality *)
  | Ex : typ -> func' | All : typ -> func' (* polymorphic quantification *)
  | And | Or | Impl
  | mU | mP | mR.

  Definition func'_eq_dec : forall a b : func', {a = b} + {a <> b}.
  Proof. decide equality; try eapply typ_eq_dec. Defined.

  (* The meaning of symbols *)
  Definition RSym_func' : RSym func'.
  refine (
    RSym_simple
      (fun f => Some
         match f with
         | mU => mkTypedVal tyM M.U
         | mP => mkTypedVal (tyArr tyM (tyArr tyM tyM)) M.P
         | mR => mkTypedVal (tyArr tyM (tyArr tyM tyProp)) M.R
         | Eq t => mkTypedVal (tyArr t (tyArr t tyProp)) (@eq _)
         | And => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) and
         | Or => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) or
         | Impl => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) Basics.impl
         | Ex t => mkTypedVal (tyArr (tyArr t tyProp) tyProp) (@ex _)
         | All t => mkTypedVal (tyArr (tyArr t tyProp) tyProp) _
         end)
      func'_eq_dec).
  refine (fun P : _ -> Prop => forall x : typD t, P x).
  Defined.

  Instance RSymOk_func' : RSymOk RSym_func' := _.

  Definition func : Set := sum func' SymEnv.func.

  Instance RSym_func fs : RSym func :=
    SymSum.RSym_sum RSym_func' (@SymEnv.RSym_func _ _ fs).

  Instance RSymOk_func fs : RSymOk (RSym_func fs).
  Proof.
    apply SymSum.RSymOk_sum; eauto with typeclass_instances.
  Qed.

  Definition known (f : func') : expr typ func := Inj (inl f).
  Definition other (f : SymEnv.func) : expr typ func := Inj (inr f).

  (** Reification **)
  (*****************)

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  (* Declare patterns **)
  Reify Declare Patterns patterns_monoid_typ : typ.
  Reify Declare Patterns patterns_monoid : expr typ func.

  (* Declare the syntax for the types *)
  Reify Declare Syntax reify_monoid_typ :=
    CPatterns@{Set} patterns_monoid_typ.

  Reify Declare Typed Table table_terms : BinNums.positive => typ.

  (* Declare syntax **)
  Definition reify_monoid' :=
    CFix
      (CFirst_ (CPatterns patterns_monoid ::
               CApp (CRec 0) (CRec 0) (@ExprCore.App typ func) ::
               CAbs (CCall reify_monoid_typ) (CRec 0) (@ExprCore.Abs typ func) ::
               CVar (@ExprCore.Var typ func) ::
               CMap other (CTypedTable reify_monoid_typ table_terms) :: nil)).
  Reify Declare Syntax reify_monoid := reify_monoid'.

  (* Pattern rules for reifying types *)
  Reify Pattern patterns_monoid_typ += (@RExact _ nat)  => tyNat.
  Reify Pattern patterns_monoid_typ += (@RExact _ M.M) => tyM.
  Reify Pattern patterns_monoid_typ += (@RExact _ Prop) => tyProp.
  Reify Pattern patterns_monoid_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function (CCall reify_monoid_typ)) => tyArr a b).

  (* Pattern rules for reifying terms *)
  Reify Pattern patterns_monoid += (@RExact _ M.P) => (known mP).
  Reify Pattern patterns_monoid += (@RExact _ M.U) => (known mU).
  Reify Pattern patterns_monoid += (@RExact _ M.R) => (known mR).
  Reify Pattern patterns_monoid += (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) =>
  (fun (t : function (CCall reify_monoid_typ)) => Inj (typ:=typ) (Eq t)).
  Reify Pattern patterns_monoid += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function@{Set} (CCall@{Set} reify_monoid_typ)) (b : function@{Set} (CCall@{Set} reify_monoid)) => (App (known (All t)) (Abs t b))).
  Reify Pattern patterns_monoid += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function (CCall reify_monoid)) => App (App (known Impl) a) b).

  Global Instance Reify_typ : Reify typ :=
  { reify_scheme := CCall reify_monoid_typ }.

  Global Instance Reify_expr_typ_func : Reify (expr typ func) :=
  { reify_scheme := CCall reify_monoid }.

End Syntax.
