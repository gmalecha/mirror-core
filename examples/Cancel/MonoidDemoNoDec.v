(* This is a demo of developing a cancellation algorithm for
 * commutative monoids.
 *)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Rtac.
Require Import MirrorCore.Simple.
Require Import MirrorCore.Reify.Reify.

Require Import McExamples.Cancel.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Module MonoidCancel (M : Monoid).

  (** Define the reified language *)
  (********************************)

  (* The syntax of types *)
  Inductive typ :=
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

  Fixpoint typ_eq_odec (a b : typ) : option (a = b) :=
    match a , b with
    | tyNat , tyNat
    | tyM , tyM
    | tyProp , tyProp => Some eq_refl
    | tyArr a b , tyArr a' b' =>
      match typ_eq_odec a a'
          , typ_eq_odec b b'
      with
      | Some pf , Some pf' => Some match pf , pf' with
                                   | eq_refl , eq_refl => eq_refl
                                   end
      | _ , _ => None
      end
    | _ , _ => None
    end.

  Fixpoint typ_eqb (a b : typ) : bool :=
    match a , b with
    | tyNat , tyNat
    | tyM , tyM
    | tyProp , tyProp => true
    | tyArr a b , tyArr a' b' =>
      typ_eqb a a' && typ_eqb b b'
    | _ , _ => false
    end.

  (* Instantiate the RType interface *)
  Instance RType_typ : RType typ :=
  { typD := typD
  ; tyAcc := tyAcc'
  ; type_cast := typ_eq_odec }.
  Instance RTypeOk_typ : RTypeOk.
  Proof.
    constructor; try reflexivity.
    - prove_simple_acc.
    - destruct pf; reflexivity.
    - destruct pf1; destruct pf2; reflexivity.
    - induction x; simpl; try reflexivity.
      + change_rewrite IHx1.
        change_rewrite IHx2. reflexivity.
    - red. unfold equiv. unfold complement.
      intros; change (x = y -> False) with (not (x = y)).
      decide equality.
  Defined.

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

  Fixpoint func'_eqb (a b : func') : bool :=
    match a , b with
    | And , And
    | Or , Or
    | Impl , Impl
    | mU , mU
    | mP , mP
    | mR , mR => true
    | Eq t , Eq t'
    | Ex t , Ex t'
    | All t , All t' => typ_eqb t t'
    | _ , _ => false
    end.

  Definition typeof_func' (f : func') : option typ :=
    Some match f with
         | mU => tyM
         | mP => tyArr tyM (tyArr tyM tyM)
         | mR => tyArr tyM (tyArr tyM tyProp)
         | Eq t => tyArr t (tyArr t tyProp)
         | And | Or | Impl => tyArr tyProp (tyArr tyProp tyProp)
         | Ex t | All t => tyArr (tyArr t tyProp) tyProp
         end.

  Definition func'D (f : func')
  : match typeof_func' f with
    | None => unit
    | Some t => typD t
    end :=
    match f as f return match typeof_func' f with
                        | None => unit
                        | Some t => typD t
                        end
    with
    | mU => M.U
    | mP => M.P
    | mR => M.R
    | Eq t => @eq _
    | And => and
    | Or => or
    | Impl => fun (P Q : Prop) => P -> Q
    | All t => fun P => forall x : typD t, P x
    | Ex t => fun P => exists x : typD t, P x
    end.

  Instance RelDec_func'_eq : RelDec (@eq func') :=
  { rel_dec := fun (a b : func') =>
                 match a , b with
                 | mU , mU => true
                 | mP , mP => true
                 | mR , mR => true
                 | Eq a , Eq b => a ?[ eq ] b
                 | And , And
                 | Impl , Impl
                 | Or , Or => true
                 | All a , All b
                 | Ex a , Ex b => a ?[ eq ] b
                 | _ , _ => false
                 end
  }.

  (* The meaning of symbols *)
  Definition RSym_func' : RSym func' :=
  {| typeof_sym := typeof_func'
  ; symD := func'D
  ; sym_eqb := fun a b => Some (a ?[ eq ] b) |}.

  Instance RelDec_Correct_typ : @RelDec_Correct _ (@eq typ) _.
  Proof.
    constructor.
    induction x; destruct y; simpl in *;
    try solve [ split; first [ tauto | congruence ] ].
    specialize (IHx1 y1). specialize (IHx2 y2).
    unfold rel_dec in *. simpl in *.
    destruct (typ_eq_odec x1 y1).
    + destruct (typ_eq_odec x2 y2).
      - split; try tauto. intros. f_equal; eauto.
      - split. intros; f_equal; eauto.
        eapply IHx2; eauto.
        inversion 1. tauto.
    + split. inversion 1.
      intros. apply IHx1. congruence.
  Qed.

  Instance RSymOk_func' : RSymOk RSym_func'.
  Proof.
    constructor.
    destruct a; destruct b; simpl; try congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
    - consider (t ?[ eq ] t0); intros; subst; congruence.
  Qed.

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

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  (* Declare patterns **)
  Reify Declare Patterns patterns_monoid_typ := typ.
  Reify Declare Patterns patterns_monoid := (expr typ func).

  (* Declare the syntax for the types *)
  Reify Declare Syntax reify_monoid_typ :=
    (@Patterns.CFirst _ (@Patterns.CPatterns _ patterns_monoid_typ :: nil)).

  Reify Declare Typed Table table_terms : BinNums.positive => reify_monoid_typ.

  (* Declare syntax **)
  Reify Declare Syntax reify_monoid :=
    (@Patterns.CFirst _ ((@Patterns.CPatterns (expr typ func) patterns_monoid) ::
                         (@Patterns.CApp (expr typ func) (@ExprCore.App typ func)) ::
                         (@Patterns.CAbs (expr typ func) reify_monoid_typ (@ExprCore.Abs typ func)) ::
                         (@Patterns.CVar (expr typ func) (@ExprCore.Var typ func)) ::
                         (@Patterns.CTypedTable (expr typ func) _ _ table_terms other) :: nil)).

  (* Pattern rules for reifying types *)
  Reify Pattern patterns_monoid_typ += (@RExact _ nat)  => tyNat.
  Reify Pattern patterns_monoid_typ += (@RExact _ M.M) => tyM.
  Reify Pattern patterns_monoid_typ += (@RExact _ Prop) => tyProp.
  Reify Pattern patterns_monoid_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid_typ) => tyArr a b).

  (* Pattern rules for reifying terms *)
  Reify Pattern patterns_monoid += (@RExact _ M.P) => (known mP).
  Reify Pattern patterns_monoid += (@RExact _ M.U) => (known mU).
  Reify Pattern patterns_monoid += (@RExact _ M.R) => (known mR).
  Reify Pattern patterns_monoid += (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) =>
  (fun (t : function reify_monoid_typ) => Inj (typ:=typ) (Eq t)).
  Reify Pattern patterns_monoid += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function reify_monoid_typ) (b : function reify_monoid) => (App (known (All t)) (Abs t b))).
  Reify Pattern patterns_monoid += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid) => App (App (known Impl) a) b).

  (* The Core Monoid Lemmas *)
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_unit_c : M.plus_unit_c.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_c1 : M.plus_assoc_c1.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_c2 : M.plus_assoc_c2.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_comm_c : M.plus_comm_c.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_cancel : M.plus_cancel.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_unit_p : M.plus_unit_p.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_p1 : M.plus_assoc_p1.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_assoc_p2 : M.plus_assoc_p2.
  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
     lem_plus_comm_p : M.plus_comm_p.

  Reify BuildLemma < reify_monoid_typ reify_monoid reify_monoid >
      lem_refl : M.refl.

  Section with_solver.
    Variable fs : @SymEnv.functions typ _.
    Let RSym_func := RSym_func fs.
    Local Existing Instance RSym_func.
    Let Expr_expr := @Expr.Expr_expr typ func RType_typ _ _.
    Local Existing Instance Expr_expr.
    Let ExprOk_expr : ExprOk Expr_expr := @ExprOk_expr typ func _ _ _ _ _ _.
    Local Existing Instance ExprOk_expr.

    Instance RL_lem_plus_unit_c : ReifiedLemma lem_plus_unit_c :=
    { ReifiedLemma_proof := M.plus_unit_c }.
    Instance RL_lem_plus_assoc_c1 : ReifiedLemma lem_plus_assoc_c1 :=
    { ReifiedLemma_proof := M.plus_assoc_c1 }.
    Instance RL_lem_plus_assoc_c2 : ReifiedLemma lem_plus_assoc_c2 :=
    { ReifiedLemma_proof := M.plus_assoc_c2 }.
    Instance RL_lem_plus_comm_c : ReifiedLemma lem_plus_comm_c :=
    { ReifiedLemma_proof := M.plus_comm_c }.
    Instance RL_lem_plus_cancel : ReifiedLemma lem_plus_cancel :=
    { ReifiedLemma_proof := M.plus_cancel }.
    Instance RL_lem_plus_unit_p : ReifiedLemma lem_plus_unit_p :=
    { ReifiedLemma_proof := M.plus_unit_p }.
    Instance RL_lem_plus_assoc_p1 : ReifiedLemma lem_plus_assoc_p1 :=
    { ReifiedLemma_proof := M.plus_assoc_p1 }.
    Instance RL_lem_plus_assoc_p2 : ReifiedLemma lem_plus_assoc_p2 :=
    { ReifiedLemma_proof := M.plus_assoc_p2 }.
    Instance RL_lem_plus_comm_p : ReifiedLemma lem_plus_comm_p :=
    { ReifiedLemma_proof := M.plus_comm_p }.
    Instance RL_lem_refl : ReifiedLemma lem_refl :=
    { ReifiedLemma_proof := M.refl }.

    Variable solver : rtac typ (expr typ func).
    Hypothesis solver_ok : RtacSound solver.

    Definition iter_right (n : nat) : rtac typ (expr typ func) :=
      REC n (fun rec =>
               FIRST [ EAPPLY lem_plus_unit_c
                     | EAPPLY lem_plus_assoc_c1 ;; ON_ALL rec
                     | EAPPLY lem_plus_assoc_c2 ;; ON_ALL rec
                     | EAPPLY lem_plus_cancel ;;
                              ON_EACH [ SOLVE solver | IDTAC ]
            ])
          IDTAC.

    Instance iter_right_sound {Q} : RtacSound (iter_right Q).
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

  Local Existing Instance cancel_sound.
  Local Existing Instance RL_lem_refl.

  Definition the_Expr fs := (@Expr.Expr_expr typ func _ _ (RSym_func fs)).

  Definition the_tactic fs :=
    @cancel fs (EAPPLY (RSym_sym:=RSym_func fs) lem_refl).

  Theorem the_tactic_sound fs : rtac_sound (Expr_expr:=the_Expr fs) (the_tactic fs).
  Proof.
    unfold the_tactic.
    intros. eapply cancel_sound; eauto with typeclass_instances.
  Qed.

  Ltac rtac_canceler :=
    lazymatch goal with
    | |- ?trm =>
      let k tbl e :=
          let result := constr:(@Interface.runRtac typ (expr typ func) nil nil e (the_tactic tbl)) in
          let resultV := eval vm_compute in result in
          match resultV with
          | Solved _ =>
            change (@Interface.propD _ _ _ Typ0_tyProp (the_Expr tbl) nil nil e) ;
              cut (result = resultV) ;
              [ set (pf := @Interface.rtac_Solved_closed_soundness
                             _ _ _ _ _ _ (the_tactic_sound tbl)
                             nil nil e) ;
                exact pf
              | vm_cast_no_check (@eq_refl _ resultV) ]
          end
      in
      reify_expr_bind reify_monoid k
                      [[ (fun x : @mk_dvar_map _ _ _ typD table_terms (@SymEnv.F typ _) => True) ]]
                      [[ trm ]]
  end.

  Module Demo.
    Axiom N : nat -> M.M.

    Fixpoint build_plusL n : M.M :=
      match n with
      | 0 => N 0
      | S n' => M.P (N n) (build_plusL n')
      end.

    Fixpoint build_plusR n : M.M :=
      match n with
      | 0 => N 0
      | S n' => M.P (build_plusR n') (N n)
      end.

    Definition goal n := M.R (build_plusL n) (build_plusR n).

    Ltac prep := unfold goal, build_plusL, build_plusR.

    Theorem test1 : goal 120.
      prep.
      Time rtac_canceler.
    Time Qed.
    Print Assumptions test1.
  End Demo.

End MonoidCancel.
