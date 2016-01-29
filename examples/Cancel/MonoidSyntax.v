Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Cancel.Monoid.
(*Require Import McExamples.Cancel.CancelTac. *)

Set Implicit Arguments.
Set Strict Implicit.

Section RelDec_from_dec.
  Context {T} (R : T -> T -> Prop).
  Variable (f : forall a b : T, {R a b} + {~R a b}).
  Definition RelDec_from_dec 
  : RelDec R :=
  {| rel_dec := fun a b =>
                  match f a b with
                  | left _ => true
                  | right _ => false
                  end |}.

  Global Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_from_dec.
  Proof.
    constructor.
    intros.
    unfold rel_dec; simpl.
    destruct (f x y); intuition.
  Qed.
End RelDec_from_dec.

Section SimpleRType_ctor.
  Context {T : Type}.
  Variable TD : T -> Type.
  Variable Tacc : T -> T -> Prop.
  Variable Tdec : forall a b : T, {a = b} + {a <> b}.

  Hypothesis wf_Tacc : well_founded Tacc.

  Definition RType_simple : RType T :=
  {| typD := TD
   ; tyAcc := Tacc
   ; type_cast := fun a b => match Tdec a b with
                             | left pf => Some pf
                             | right _ => None
                             end |}.

  Theorem RTypeOk_simple : @RTypeOk T RType_simple.
  Proof.
    constructor.
    { reflexivity. }
    { eapply wf_Tacc. }
    { compute. destruct pf. reflexivity. }
    { compute. destruct pf1. destruct pf2. reflexivity. }
    { compute. intros. destruct (Tdec x x).
      { eapply Eqdep_dec.K_dec_type with (p := e); eauto. }
      { congruence. } }
    { red. eapply Tdec. }
  Defined.
End SimpleRType_ctor.

Instance RelDec_from_RType {T} (R : RType T) : RelDec (@eq T) | 900 :=
{ rel_dec a b := match type_cast a b with
                 | Some _ => true
                 | None => false
                 end }.


Arguments RTypeOk_simple {_ _ _ _} _.

Ltac prove_simple_acc :=
  try match goal with
      | |- well_founded _ => red
      end ;
  match goal with
  | |- forall x : _ , Acc _ x =>
    induction x; constructor; inversion 1; subst; auto
  end.

Ltac prove_TypOk :=
  constructor;
  try solve [ reflexivity
            | constructor
            | inversion 1; subst; unfold Rty; auto
            | match goal with
              | |- forall x, _ =>
                destruct x; simpl;
                try solve [ eauto
                          | left; repeat first [ exists eq_refl | eexists ];
                            reflexivity ]
              end
            | intros; match goal with
                      | H : Rty _ _ |- _ => destruct H ; reflexivity
                      end
            ].

(** TODO: Something like this probably already exists. *)
Record TypedValue {T : Type} {RT : RType T} : Type := mkTypedVal
{ tv_type : T
; tv_value : TypesI.typD tv_type }.
Arguments TypedValue _ {_} : clear implicits.
Arguments mkTypedVal {_ _} _ _ : clear implicits.

Section Simple_RSym.
  Context {T} {RT : RType T} {f : Type}
             (fD : f -> option (TypedValue T))
             (fdec : forall a b : f, {a = b} + {a <> b}).
  Definition RSym_simple : RSym f :=
  {| typeof_sym f := match fD f with
                     | Some l => Some l.(tv_type)
                     | None => None
                     end
   ; symD f := match fD f with
               | Some l => l.(tv_value)
               | None => tt
               end
   ; sym_eqb a b := Some match fdec a b with
                         | left _ => true
                         | right _ => false
                         end |}.

  Global Instance RSymOk_simple :  RSymOk RSym_simple.
  Proof. constructor. intros. simpl.
         destruct (fdec a b); auto.
  Qed.
End Simple_RSym.

(** TODO: Move everything above this point **)

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
