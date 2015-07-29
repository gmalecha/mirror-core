Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.Cancel.Lang.
Require Import McExamples.Cancel.CancelTac.
Require Import MirrorCore.syms.SymEnv.

Require Import Coq.Strings.String.

Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import Charge.ModularFunc.ListType.
Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseFunc.
Require Import Charge.ModularFunc.BaseType.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ :=
| tyArr : typ -> typ -> typ | tyList : typ -> typ
| tyNat | tyM | tyBool | tyString | tyProd : typ -> typ -> typ
| tyProp.

Fixpoint typD (t : typ) : Type :=
  match t with
    | tyNat => nat
    | tyBool => bool
    | tyString => string
    | tyProd t u => prod (typD t) (typD u)
    | tyM => M
    | tyProp => Prop
    | tyList a => list (typD a)
    | tyArr a b => typD a -> typD b
  end.

Definition typ_eq_dec : forall a b : typ, {a = b} + {a <> b}.
  decide equality.
Defined.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b =>
               match typ_eq_dec a b with
                 | left _ => true
                 | right _ => false
               end }.

Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ.
Proof.
  constructor.
  intros.
  unfold rel_dec; simpl.
  destruct (typ_eq_dec x y); intuition.
Qed.

Inductive tyAcc' : typ -> typ -> Prop :=
| tyArrL : forall a b, tyAcc' a (tyArr a b)
| tyArrR : forall a b, tyAcc' b (tyArr a b).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc'
; type_cast := fun a b => match typ_eq_dec a b with
                            | left pf => Some pf
                            | _ => None
                          end
}.

Instance RTypeOk_typ : @RTypeOk typ _.
Proof.
  eapply makeRTypeOk.
  { red.
    induction a; constructor; inversion 1.
    subst; auto.
    subst; auto. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x x).
    f_equal. compute.
    uip_all. reflexivity. congruence. }
  { unfold type_cast; simpl.
    intros. destruct (typ_eq_dec x y); try congruence. }
Qed.

Instance Typ2_tyArr : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match :=
    fun T t tr =>
      match t as t return T (TypesI.typD t) -> T (TypesI.typD t) with
        | tyArr a b => fun _ => tr a b
        | _ => fun fa => fa
      end
}.

Instance Typ2Ok_tyArr : Typ2Ok Typ2_tyArr.
Proof.
  constructor.
  { reflexivity. }
  { apply tyArrL. }
  { intros; apply tyArrR. }
  { inversion 1; subst; unfold Rty; auto. }
  { destruct x; simpl; eauto.
    left; do 2 eexists; exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.

Instance Typ0_tyProp : Typ0 _ Prop :=
{| typ0 := tyProp
 ; typ0_cast := eq_refl
 ; typ0_match := fun T t =>
                   match t as t
                         return T Prop -> T (TypesI.typD t) -> T (TypesI.typD t)
                   with
                     | tyProp => fun tr _ => tr
                     | _ => fun _ fa => fa
                   end
 |}.

Inductive func' :=
| N : nat -> func' | Eq : typ -> func'
| Ex : typ -> func' | All : typ -> func'
| And | Or | Impl
| mU | mP | mR.

Definition typeof_func' (f : func') : option typ :=
  Some match f with
         | mU => tyM
         | mP => tyArr tyM (tyArr tyM tyM)
         | mR => tyArr tyM (tyArr tyM tyProp)
         | N _ => tyNat
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
    | mU => U
    | mP => P
    | mR => R
    | N n => n
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
                 | N a , N b => a ?[ eq ] b
                 | Eq a , Eq b => a ?[ eq ] b
                 | And , And
                 | Impl , Impl
                 | Or , Or => true
                 | All a , All b
                 | Ex a , Ex b => a ?[ eq ] b
                 | _ , _ => false
               end
}.

Instance RelDecCorrect_func'_eq : RelDec_Correct RelDec_func'_eq.
Proof.
  constructor. destruct x; destruct y; simpl; try solve [ split; congruence ].
  - rewrite rel_dec_correct. split; congruence.
  - rewrite rel_dec_correct. split; congruence.
  - rewrite rel_dec_correct. split; congruence.
  - rewrite rel_dec_correct. split; congruence.
Qed.


Instance RSym_func' : RSym func' :=
{ typeof_sym := typeof_func'
; symD := func'D
; sym_eqb := fun a b => Some (a ?[ eq ] b)
}.

Instance RSymOk_func' : RSymOk RSym_func'.
constructor.
intros. simpl.
consider (a ?[ eq ] b); auto.
Qed.

Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.

Instance BaseType_typ : BaseType typ := {
  tyNat := tyNat;
  tyBool := tyBool;
  tyString := tyString;
  tyProd := tyProd
}.

Lemma btProd_eq (a b c d : typ) (H : tyProd a b = tyProd c d) : a = c /\ b = d.
Proof.
  inversion H; subst.
  split; reflexivity.
Qed.

Instance BaseTypeD_typ : BaseTypeD BaseType_typ := {
	btNat := eq_refl;
	btBool := eq_refl;
	btString := eq_refl;
	btProd := fun _ _ => eq_refl;
	tyProd_inj := btProd_eq
}.

Instance ListType_typ : ListType typ := {
	tyList := tyList
}.

Lemma btList_eq (a b : typ) (H : tyList a = tyList b) : a = b.
Proof.
  inversion H; subst; reflexivity.
Qed.

Instance ListTypeD_typ : ListTypeD ListType_typ := {
	btList := fun _ => eq_refl;
	tyList_inj := btList_eq
}.


Fixpoint list_to_pmap_aux {T : Type} (lst : list T) (p : positive) : pmap T :=
  match lst with
    | nil => Empty
    | x :: xs => pmap_insert p x (list_to_pmap_aux xs (p + 1))
  end.
  
Definition list_to_pmap {T : Type} (lst : list Type) := list_to_pmap_aux lst 1.

Definition func_map : pmap Type := 
	list_to_pmap (T := Type) 
	  (func'::SymEnv.func::@list_func typ::nil).

Definition func := OneOf func_map.

Global Instance ListFunc_func : ListFunc typ func := ListFuncPMap 3 func_map eq_refl.

  Definition RSym_sub_func (p : positive) :
    RSym (match pmap_lookup' func_map p with | Some T => T | None => Empty_set end).
  Proof.
    destruct p; simpl; [| | apply _].
    destruct p; simpl; [| | apply _].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    destruct p; simpl; [| | apply RSym_func].
    induction p; simpl; intuition; apply RSym_Empty_set.
    induction p; simpl; intuition; apply RSym_Empty_set.
    apply Coq.FSets.FMapPositive.PositiveMap.Leaf.
  Defined.

  Lemma RSymOk_sub_func (p : positive) : RSymOk (RSym_sub_func p).
  Proof.
    admit.
  Admitted.

  Global Instance RSym_func : RSym func := RSymOneOf func_map RSym_sub_func.
  
  Global Instance RSymOk_func : RSymOk RSym_func := RSymOk_OneOf func_map RSym_sub_func RSymOk_sub_func.

Definition known (f : func') : expr typ func := Inj (Into (ts := func_map) f 1 eq_refl).
Definition other (f : SymEnv.func) : expr typ func := Inj (Into (ts := func_map) f 2 eq_refl).

Fixpoint mkNatList (n : nat) :=
  match n with 
    | 0 => mkNil tyNat
    | S n' => mkCons tyNat (known (N n)) (mkNatList n')
  end.

Fixpoint mkRevNatList_aux (n m : nat):=
  match n with 
    | 0 => mkNil tyNat
    | S n' => mkCons tyNat (known (N m)) (mkRevNatList_aux n' (S m))
  end.

Definition mkRevNatList n := mkRevNatList_aux n 1.

Require Import McExamples.Cancel.ListCancelTac.

(* Gregory: Here there be list demo *)

Goal True.
(* Riddle me this: remove 'Goal True' and we get a universe inconsistency. *)
Time Eval vm_compute in cancel (mkNatList 2000) (mkRevNatList 2000).
apply I.
Qed.

(** Reification **)
Require Coq.Numbers.BinNums.
Require Import MirrorCore.Reify.Reify.

(** Declare patterns **)
Reify Declare Patterns patterns_monoid_typ := typ.
Reify Declare Patterns patterns_monoid := (expr typ func).

Reify Declare Syntax reify_monoid_typ :=
  { (@Patterns.CFirst _ (@Patterns.CPatterns _ patterns_monoid_typ :: nil)) }.

Reify Declare Typed Table table_terms : BinNums.positive => reify_monoid_typ.

(** Declare syntax **)
Reify Declare Syntax reify_monoid :=
  { (@Patterns.CFirst _ ((@Patterns.CPatterns (expr typ func) patterns_monoid) ::
                         (@Patterns.CApp (expr typ func) (@ExprCore.App typ func)) ::
                         (@Patterns.CAbs (expr typ func) reify_monoid_typ (@ExprCore.Abs typ func)) ::
                         (@Patterns.CVar (expr typ func) (@ExprCore.Var typ func)) ::
                         (@Patterns.CTypedTable (expr typ func) _ _ table_terms other) :: nil))
  }.

Reify Pattern patterns_monoid_typ += (@RExact _ nat)  => tyNat.
Reify Pattern patterns_monoid_typ += (@RExact _ Lang.M) => tyM.
Reify Pattern patterns_monoid_typ += (@RExact _ Prop) => tyProp.
Reify Pattern patterns_monoid_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid_typ) => tyArr a b).

Reify Pattern patterns_monoid += (@RGet 0 RConst) => (fun (n : id nat) => known (N n)).
Reify Pattern patterns_monoid += (@RExact _ Lang.P) => (known mP).
Reify Pattern patterns_monoid += (@RExact _ Lang.U) => (known mU).
Reify Pattern patterns_monoid += (@RExact _ Lang.R) => (known mR).
Reify Pattern patterns_monoid += (RApp (@RExact _ (@eq)) (RGet 0 RIgnore)) =>
  (fun (t : function reify_monoid_typ) => Inj (typ:=typ) (Eq t)).
Reify Pattern patterns_monoid += (RPi (RGet 0 RIgnore) (RGet 1 RIgnore)) => (fun (t : function reify_monoid_typ) (b : function reify_monoid) => (App (known (All t)) (Abs t b))).
Reify Pattern patterns_monoid += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monoid) => App (App (known Impl) a) b).

Definition lem_refl : Lemma.lemma typ (expr typ func) (expr typ func) :=
{| vars := tyM :: nil
 ; premises := nil
 ; concl := App (App (known mR) (Var 0)) (Var 0)
 |}.

Definition the_tactic fs :=
  @CancelTac.cancel typ func RType_typ _ _ (RSym_func fs)
                    tyM (known mR) (known mP) (known mU)
                    (@EAPPLY typ func RType_typ Typ0_tyProp Typ2_tyArr (RSym_func fs) lem_refl).

Definition the_Expr fs := (@Expr.Expr_expr typ func _ _ (RSym_func fs)).


Theorem sound_tac : forall fs,
    @rtac_sound typ (expr typ func) RType_typ Typ0_tyProp
                 (the_Expr fs) (the_tactic fs).
Proof.
  intros. eapply CancelTac.cancel_sound; eauto with typeclass_instances.
  constructor; exact plus_unit_c.
  constructor; exact plus_assoc_c1.
  constructor; exact plus_assoc_c2.
  constructor; exact plus_comm_c.
  constructor; exact plus_cancel.
  constructor; exact plus_unit_p.
  constructor; exact plus_assoc_p1.
  constructor; exact plus_assoc_p2.
  constructor; exact plus_comm_p.
  eapply RtacSound_EAPPLY; eauto with typeclass_instances.
  constructor; compute; exact refl.
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
                       _ _ _ _ _ _ (sound_tac tbl)
                       nil nil e) ;
              exact pf
            | vm_cast_no_check (@eq_refl _ resultV) ]
      end
  in
  reify_expr_bind reify_monoid k [ (fun x : @mk_dvar_map _ _ _ typD table_terms (@SymEnv.F typ _) => True)  ] [ trm ]
  end.

Goal goal 120.
  prep.
  Time rtac_canceler.
Time Qed.