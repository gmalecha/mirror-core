Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Reify.ReifyView.
Require Import MirrorCore.Lib.EqView.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TCLemma.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.CTypes.CoreTypes.


Inductive my_forall (typ : Set) : Set :=
| MyForall (t : typ)
| MyEq (t : typ).

Inductive my_types : nat -> Set :=
| MyNat : my_types 0.

Section MakeILogic.
  Context {typ func : Set} {FV : PartialView func (my_forall typ)}.

  Definition fForall t := f_insert (MyForall typ t).

  Definition mkForall (t : typ) (f : expr typ func) := App (Inj (fForall t)) (Abs t f).

End MakeILogic.

(* TODO: Doesn't this exist somewhere?
Definition IgnorePatterns (ls : list RPattern) (T : Set) : Set := T.
Opaque IgnorePatterns.
Section for_ignore.
  Variable ls : list RPattern.
  Variable T : Set.

  Definition reify_IgnorePatterns {R : Reify T}
  : Command T :=
    let ignores :=
        map (fun p => CPattern (ls:=(T : Type)::nil) p (fun (a : function (CRec 0)) => a)) ls
    in
    CFix (CFirst_ (ignores ++ CCall (@reify_scheme _ R) :: nil)).

  Global Instance Reify_IgnorePatterns {R : Reify T} : Reify (IgnorePatterns ls T) :=
  { reify_scheme := @reify_IgnorePatterns R }.

End for_ignore.

Typeclasses Opaque IgnorePatterns.

Arguments reify_IgnorePatterns {_} _ {_}.
*)

Section Test.
  Context {typ func : Set}.
  Context {RType_typ : RType typ}.

  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_eq_func : RelDec (@eq func)}.
  Context {Expr_expr : Expr typ (expr typ func)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {FV1 : PartialView func (eq_func typ)}.
  Context {FV2 : PartialView func (my_forall typ)}.
  Context {FV_typ : PartialView typ (base_typ 0)}.

  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.

  Local Instance Reify_typ : Reify typ :=
    Reify_typ typ (reify_base_typ typ :: nil).

  Definition reify_pforall : Command@{Set} (expr typ func) :=
    CPattern (ls := (typ : Type) :: (expr typ func : Type) :: nil)
             (RPi (RGet 0 RIgnore) (RGet 1 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) (y : function (CRec 0)) =>
                mkForall x y).


  Local Instance Reify_expr : Reify (expr typ func) :=
    Reify_func_no_table typ func (reify_eq typ func :: reify_pforall :: nil).

  Lemma Id {A} : forall P : A, True -> P = P.
  Proof.
    reflexivity.
  Qed.

  Definition reify_poly :=
    reify_scheme@{Set}
                (tc_lemma typ (expr typ func) (expr typ func)
                          (RExact True :: nil)).
  Ltac reify_poly e :=
    let k e :=
        pose e in
    reify_expr reify_poly k
               [[ True ]]
               [[ e ]].

  Goal True.
    (* This reifies *)
    reify_poly (forall x : nat, True -> x = x).
    apply I.
  Qed.

  Definition lem_landexistsDL :
    polymorphic typ 1
                (tc_lemma typ (expr typ func)
                             (rw_concl typ func (expr typ func))
                             (RExact True :: nil)) :=
    Eval unfold Lemma.add_var , Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises, app  in
        <:: @Id ::>.

End Test.