Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Reify.ReifyView.
Require Import MirrorCore.Lib.EqView.
Require Import MirrorCore.CTypes.BaseType.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.PLemma.
Require Import MirrorCore.Polymorphic.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.CTypes.CoreTypes.

Inductive my_forall (typ : Set) : Set :=
| MyForall (t : typ)
| MyEq (t : typ)
| MyImpl
| MyTrue.

Inductive my_types : nat -> Set :=
| MyNat : my_types 0.

Section MakeILogic.
  Context {typ func : Set} {FV : PartialView func (my_forall typ)}.

  Definition fForall t := f_insert (MyForall typ t).

  Definition mkForall (t : typ) (f : expr typ func) := App (Inj (fForall t)) (Abs t f).

End MakeILogic.

Definition IgnorePatterns (ls : list RPattern) (T : Set) : Set := T.
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

Arguments reify_IgnorePatterns {_} _ {_}.

Definition typ := ctyp my_types.

Axiom RType_typ : RType typ.
Axiom Typ2_typ : Typ2 RType_typ Fun.
Print reify_func_aux.
Local Instance Reify_typ : Reify typ := 
  Reify_typ typ ((CPattern (ls := nil) (RExact nat) (tyBase0 MyNat))::nil).

Definition reify_pforall_no_sect : Command@{Set} (expr typ (my_forall typ)) :=
  CPattern (ls := (typ : Type) :: (expr typ (my_forall typ) : Type) :: nil)
           (RPi (RGet 0 RIgnore) (RGet 1 RIgnore))
           (fun (x : function (CCall (reify_scheme typ))) (y : function (CRec 0)) =>
              (App (Inj (MyForall typ x)) (Abs x y))).

Definition reify_peq_no_sect : Command@{Set} (expr typ (my_forall typ)) :=
  CPattern (ls := (typ : Type) :: nil)
           (RApp (RExact (@eq)) (RGet 0 RIgnore))
           (fun (x : function (CCall (reify_scheme typ))) =>
              (Inj (MyEq typ x))).

Definition reify_ptrue_no_sect : Command@{Set} (expr typ (my_forall typ)) :=
  CPattern (ls := nil) (RExact True) (Inj (MyTrue typ)).
  
Definition reify_pimpl_no_sect : Command@{Set} (expr typ (my_forall typ)) :=
  CPattern (ls := (expr typ (my_forall typ) : Type) :: (expr typ (my_forall typ) : Type) :: nil) 
           (RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
           (fun (x y : function (CRec 0)) =>
              (App (App (Inj (MyImpl typ)) x) y)).

Local Instance Reify_expr_no_sect : Reify (expr typ (my_forall typ)) :=
  Reify_func_no_table typ (my_forall typ) (reify_pimpl_no_sect :: reify_ptrue_no_sect :: reify_peq_no_sect :: reify_pforall_no_sect :: nil).

Definition reify_poly_no_sect := reify_scheme@{Set} (IgnorePatterns (RImpl (RExact True) (RGet 0 RIgnore)::nil) (expr typ (my_forall typ))).
  Ltac reify_poly_no_sect e :=
    let k e :=
        pose e in
    reify_expr reify_poly_no_sect k
               [[ True ]]
               [[ e ]].

  Goal True.
    (* This reifies *)
    reify_poly_no_sect (forall x : nat, True -> x = x).
    apply I.
  Qed.


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

  Definition reify_poly := reify_scheme@{Set} (IgnorePatterns (RImpl (RExact True) (RGet 0 RIgnore)::nil) (expr typ func)).
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
    polymorphic typ 1 (IgnorePatterns (RImpl (RExact True) (RGet 0 RIgnore)::nil)
                (Lemma.lemma typ (expr typ func) 
                             (rw_concl typ func (expr typ func)))) :=
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
        <:: @Id ::>.
Print lem_landexistsDL.    
