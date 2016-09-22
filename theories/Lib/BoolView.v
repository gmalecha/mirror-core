Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive boolFunc : Type  :=
| pBool  : bool -> boolFunc.

Section BoolFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ0_tyBool : Typ0 _ bool}.

  Let tyBool : typ := @typ0 _ _ _ Typ0_tyBool.

  Definition typeofBoolFunc (nf : boolFunc) : option typ :=
    match nf with
    | pBool _ => Some tyBool
   end.

  Definition boolFuncEq (a b : boolFunc) : option bool :=
    match a , b with
      | pBool s, pBool t => Some (s ?[ eq ] t)
  end.

  Definition boolR (b : bool) : typD tyBool :=
    castR id bool b.

  Definition bool_func_symD bf :=
    match bf as bf return match typeofBoolFunc bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pBool b => boolR b
    end.

  Global Instance RSym_BoolFunc
  : SymI.RSym boolFunc :=
    {
      typeof_sym := typeofBoolFunc;
      symD := bool_func_symD ;
      sym_eqb := boolFuncEq
    }.

  Global Instance RSymOk_BoolFunc : SymI.RSymOk RSym_BoolFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try reflexivity.
    consider (b0 ?[ eq ] b); intros; subst; congruence.
  Qed.

End BoolFuncInst.

Section MakeBool.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : PartialView func boolFunc}.

  Definition fBool b := f_insert (pBool b).

  Definition mkBool (b : bool) := Inj (typ := typ) (fBool b).

  Definition fptrnBool {T : Type} (p : Ptrns.ptrn bool T) : ptrn boolFunc T :=
    fun f U good bad =>
      match f with
        | pBool s => p s U good (fun x => bad f)
      end.

  Global Instance fptrnBool_ok {T : Type} {p : ptrn bool T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnBool p).
  Proof.
    red; intros; try (right; unfold Fails; reflexivity).
    destruct x; simpl; destruct (Hok b).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnBool {T : Type} (f : boolFunc) (p : ptrn bool T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnBool p) res) :
    exists s, Succeeds s p res /\ f = pBool s.
  Proof.
    unfold Succeeds, fptrnBool in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok b).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists b; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnBool_SucceedsE {T : Type} {f : boolFunc}
         {p : ptrn bool T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnBool p) res := {
      s_result := exists s, Succeeds s p res /\ f = pBool s;
      s_elim := @Succeeds_fptrnBool T f p res pok
    }.

End MakeBool.

Section PtrnBool.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : PartialView func boolFunc}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkBool typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnBool {T : Type} (p : ptrn bool T) : ptrn (expr typ func) T :=
    inj (ptrn_view FV (fptrnBool p)).

End PtrnBool.

Require Import MirrorCore.Reify.ReifyClass.

Section ReifyBool.
  Context {typ func : Type} {FV : PartialView func boolFunc}.

  Definition reify_cbool : Command (expr typ func) :=
    CPattern (ls := (bool:Type)::nil) (RHasType nat (RGet 0 RIgnore)) (fun x => Inj (fBool x)).

  Definition reify_bool : Command (expr typ func) :=
    CFirst (reify_cbool :: nil).

End ReifyBool.

Arguments reify_bool _ _ {_}.