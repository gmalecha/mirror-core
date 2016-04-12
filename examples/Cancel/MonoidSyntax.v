Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Simple.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Cancel.Monoid.
(*Require Import McExamples.Cancel.CancelTac. *)

Set Implicit Arguments.
Set Strict Implicit.

Module MonoidSyntax (Import M : Monoid).

  Inductive typ :=
  | tyArr : typ -> typ -> typ
  | tyNat | tyM
  | tyProp.

  Inductive tyAcc' : typ -> typ -> Prop :=
  | tyArrL : forall a b, tyAcc' a (tyArr a b)
  | tyArrR : forall a b, tyAcc' b (tyArr a b).


  Fixpoint typD (t : typ) : Type :=
    match t with
    | tyNat => nat
    | tyM => M
    | tyProp => Prop
    | tyArr a b => typD a -> typD b
    end.

  Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  Instance RType_typ : RType typ := RType_simple typD tyAcc' typ_eq_dec.
  Instance RTypeOk_typ : RTypeOk := RTypeOk_simple _.
  Proof. prove_simple_acc. Defined.

  Instance Typ2_tyArr : Typ2 RType_typ Fun :=
  { typ2 := tyArr
  ; typ2_cast := fun _ _ => eq_refl
  ; typ2_match T t tr :=
      match t as t return T (typD t) -> T (typD t) with
      | tyArr a b => fun _ => tr a b
      | _ => fun fa => fa
      end
  }.

  Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
  Proof. prove_TypOk. Defined.

  Instance Typ0_tyProp : Typ0 RType_typ Prop :=
  { typ0 := tyProp
  ; typ0_cast := eq_refl
  ; typ0_match T t :=
      match t with
      | tyProp => fun tr _ => tr
      | _ => fun _ fa => fa
      end
  }.

  Instance Typ0Ok_tyProp : Typ0Ok Typ0_tyProp.
  Proof. prove_TypOk. Defined.


  Inductive func' :=
  | Eq : typ -> func'
  | Ex : typ -> func' | All : typ -> func'
  | And | Or | Impl
  | mU | mP | mR.

  Definition func'_eq_dec : forall a b : func', {a = b} + {a <> b}.
  Proof. decide equality; try eapply typ_eq_dec. Defined.

  Definition RSym_func' : RSym func'.
  refine (
    RSym_simple
      (fun f => Some
         match f with
         | mU => mkTypedVal tyM U
         | mP => mkTypedVal (tyArr tyM (tyArr tyM tyM)) P
         | mR => mkTypedVal (tyArr tyM (tyArr tyM tyProp)) R
         | Eq t => mkTypedVal (tyArr t (tyArr t tyProp)) (@eq _)
         | And => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) and
         | Or => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) or
         | Impl => mkTypedVal (tyArr tyProp (tyArr tyProp tyProp)) Basics.impl
         | Ex t => mkTypedVal (tyArr (tyArr t tyProp) tyProp) (@ex _)
         | All t => mkTypedVal (tyArr (tyArr t tyProp) tyProp) _
         end)
      func'_eq_dec).
  refine (fun P : _ -> Prop => forall x, P x).
  Defined.

  Definition RSymOk_func' : RSymOk RSym_func' := _.

  Require MirrorCore.syms.SymEnv.
  Require MirrorCore.syms.SymSum.

  Definition func : Type := sum func' SymEnv.func.

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
  Require Coq.Numbers.BinNums.
  Require Import MirrorCore.Reify.Reify.

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  (** Declare patterns **)
  Reify Declare Patterns patterns_monoid_typ : typ.
  Reify Declare Patterns patterns_monoid : expr typ func.

  Reify Declare Syntax reify_monoid_typ :=
    Patterns.CPatterns patterns_monoid_typ.

  Reify Declare Typed Table table_terms : BinNums.positive => typ.

  (** Declare syntax **)
  Reify Declare Syntax reify_monoid :=
    Patterns.CFirst (Patterns.CPatterns patterns_monoid ::
                     Patterns.CApp (@ExprCore.App typ func) ::
                     Patterns.CAbs reify_monoid_typ (@ExprCore.Abs typ func) ::
                     Patterns.CVar (@ExprCore.Var typ func) ::
                     Patterns.CMap other (Patterns.CTypedTable reify_monoid_typ table_terms) :: nil).

  Reify Pattern patterns_monoid_typ += (@RExact _ nat)  => tyNat.
  Reify Pattern patterns_monoid_typ += (@RExact _ M) => tyM.
  Reify Pattern patterns_monoid_typ += (@RExact _ Prop) => tyProp.
  Reify Pattern patterns_monoid_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid_typ) => tyArr a b).

(*
  Reify Pattern patterns_monoid += (@RGet 0 RConst) => (fun (n : id nat) => known (N n)).
*)
  Reify Pattern patterns_monoid += (@RExact _ P) => (known mP).
  Reify Pattern patterns_monoid += (@RExact _ U) => (known mU).
  Reify Pattern patterns_monoid += (@RExact _ R) => (known mR).
  Reify Pattern patterns_monoid += (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) =>
  (fun (t : function reify_monoid_typ) => Inj (typ:=typ) (Eq t)).
  Reify Pattern patterns_monoid += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function reify_monoid_typ) (b : function reify_monoid) => (App (known (All t)) (Abs t b))).
  Reify Pattern patterns_monoid += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid) => App (App (known Impl) a) b).

  Require Import MirrorCore.Lemma.

  (* The Core Monoid Lemmas *)
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_unit_c : plus_unit_c.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_c1 : plus_assoc_c1.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_c2 : plus_assoc_c2.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_comm_c : plus_comm_c.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_cancel : plus_cancel.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_unit_p : plus_unit_p.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_p1 : plus_assoc_p1.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_p2 : plus_assoc_p2.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_comm_p : plus_comm_p.

  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
      lem_refl : refl.

  Require Import MirrorCore.RTac.RTac.

  Notation "'delay' x" := (fun y => x y) (at level 3).

  Require Import MirrorCore.Lambda.Expr.

  Section with_solver.
    Variable fs : @SymEnv.functions typ _.
    Let RSym_func := RSym_func fs.
    Local Existing Instance RSym_func.
    Let Expr_expr := @Expr.Expr_expr typ func RType_typ _ _.
    Local Existing Instance Expr_expr.
    Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr typ func _ _ _ _ _ _.
    Local Existing Instance ExprOk_expr.

    Variable solver : rtac typ (expr typ func).
    Hypothesis solver_ok : RtacSound solver.
    Require Import MirrorCore.Lambda.Rtac.

    Definition iter_right (n : nat) : rtac typ (expr typ func) :=
      REC n (fun rec =>
               FIRST [ EAPPLY lem_plus_unit_c
                     | EAPPLY lem_plus_assoc_c1 ;; ON_ALL rec
                     | EAPPLY lem_plus_assoc_c2 ;; ON_ALL rec
                     | EAPPLY lem_plus_cancel ;;
                              ON_EACH [ SOLVE solver | IDTAC ]
            ])
          IDTAC.

    Existing Instance RtacSound_EAPPLY.

    Instance RL_lem_plus_unit_c : ReifiedLemma lem_plus_unit_c :=
    { ReifiedLemma_proof := plus_unit_c }.
    Instance RL_lem_plus_assoc_c1 : ReifiedLemma lem_plus_assoc_c1 :=
    { ReifiedLemma_proof := plus_assoc_c1 }.
    Instance RL_lem_plus_assoc_c2 : ReifiedLemma lem_plus_assoc_c2 :=
    { ReifiedLemma_proof := plus_assoc_c2 }.
    Instance RL_lem_plus_comm_c : ReifiedLemma lem_plus_comm_c :=
    { ReifiedLemma_proof := plus_comm_c }.
    Instance RL_lem_plus_cancel : ReifiedLemma lem_plus_cancel :=
    { ReifiedLemma_proof := plus_cancel }.
    Instance RL_lem_plus_unit_p : ReifiedLemma lem_plus_unit_p :=
    { ReifiedLemma_proof := plus_unit_p }.
    Instance RL_lem_plus_assoc_p1 : ReifiedLemma lem_plus_assoc_p1 :=
    { ReifiedLemma_proof := plus_assoc_p1 }.
    Instance RL_lem_plus_assoc_p2 : ReifiedLemma lem_plus_assoc_p2 :=
    { ReifiedLemma_proof := plus_assoc_p2 }.
    Instance RL_lem_plus_comm_p : ReifiedLemma lem_plus_comm_p :=
    { ReifiedLemma_proof := plus_comm_p }.

    Instance iter_right_sound {Q} : RtacSound (iter_right Q) := _.
    Proof.
      unfold iter_right; rtac_derive_soundness_default.
    Qed.

    Section afterwards.
      Variable k : rtac typ (expr typ func).
      Definition iter_left (n : nat) : rtac typ (expr typ func) :=
        REC n (fun rec =>
                 FIRST [ EAPPLY lem_plus_unit_p
                       | EAPPLY lem_plus_assoc_p1 ;; ON_ALL rec
                       | EAPPLY lem_plus_assoc_p2 ;; ON_ALL rec
                       | k
              ])
            IDTAC.

      Hypothesis k_sound : RtacSound k.

      Lemma iter_left_sound : forall Q, RtacSound (iter_left Q).
      Proof. unfold iter_left; rtac_derive_soundness_default. Qed.
    End afterwards.
    Local Existing Instance iter_left_sound.

    Definition cancel' (n m : nat) : rtac typ (expr typ func) :=
      let k :=
          FIRST [ EAPPLY lem_plus_comm_c ;; ON_ALL (iter_right m)
                | iter_right m
                ]
      in
      FIRST [ iter_left k n
            | EAPPLY lem_plus_comm_p ;; ON_ALL (iter_left k n)
            ].

    Local Instance cancel'_sound : forall P Q, RtacSound (cancel' P Q).
    Proof.
      cbv beta delta [ cancel' ]; rtac_derive_soundness_default.
    Qed.

    Fixpoint size (e : expr typ func) : nat :=
      match e with
      | App (App _ x) y => size x + size y
      | _ => 1
      end.

    Definition cancel : rtac typ (expr typ func) :=
      AT_GOAL (fun _ _ e =>
                 let fuel := size e in
                 REPEAT fuel
                        (FIRST [ SOLVE solver
                               | (cancel' fuel fuel ;; ON_ALL (TRY solver)) ;; MINIFY
              ])).

    Theorem cancel_sound : RtacSound cancel.
    Proof.
      unfold cancel.
      rtac_derive_soundness_default; eauto with typeclass_instances.
    Qed.

  End with_solver.

End MonoidSyntax.
