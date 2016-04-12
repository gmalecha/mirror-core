Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive eq_func (typ : Type) :=
  | pEq : typ -> eq_func typ.

Section EqFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyProp : Typ0 _ Prop}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition typeof_eq_func f :=
    match f with
      | pEq t => Some (tyArr t (tyArr t tyProp))
    end.

  Definition eq_func_eq (a b : eq_func typ) : option bool :=
    match a , b with
      | pEq t1, pEq t2 => Some (t1 ?[ eq ] t2)
    end.

  Global Instance RelDec_eq_func : RelDec (@eq (eq_func typ)) :=
  { rel_dec a b := match eq_func_eq a b with
    	  	   | Some b => b
    		   | None => false
    		   end
  }.

  Definition eqR t : typD (tyArr t (tyArr t tyProp)) :=
    castR id (Fun (typD t) (Fun (typD t) Prop)) (@eq (typD t)).

  Definition eq_func_symD lf :=
    match lf as lf return match typeof_eq_func lf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pEq t => eqR t
    end.

  Global Instance RSym_EqFunc : SymI.RSym (eq_func typ) :=
  { typeof_sym := typeof_eq_func;
    symD := eq_func_symD;
    sym_eqb := eq_func_eq
  }.

  Global Instance RSymOk_EqFunc : SymI.RSymOk RSym_EqFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t0); intuition congruence.
  Qed.

End EqFuncInst.

Section MakeEq.
  Context {typ func : Type} {FV : FuncView func (eq_func typ)}.

  Definition fEq t := f_insert (pEq t).

  Definition mkCons (t : typ) (a b : expr typ func) :=
    App (App (Inj (fEq t)) a) b.

  Definition fptrnEq {T : Type} (p : Ptrns.ptrn typ T) : ptrn (eq_func typ) T :=
    fun f U good bad =>
      match f with
        | pEq t => p t U good (fun x => bad f)
      end.

  Global Instance fptrnEq_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnEq p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok t)].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnEq {T : Type} (f : eq_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnEq p) res) :
    exists t, Succeeds t p res /\ f = pEq t.
  Proof.
    unfold Succeeds, fptrnEq in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnEq_SucceedsE {T : Type} {f : eq_func typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnEq p) res :=
  { s_result := exists t, Succeeds t p res /\ f = pEq t;
    s_elim := @Succeeds_fptrnEq T f p res pok
  }.

End MakeEq.

Section PtrnEq.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func (eq_func typ)}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkEq typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnEq {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnEq p))) a) b.

End PtrnEq.