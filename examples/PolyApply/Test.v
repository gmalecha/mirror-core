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

Inductive my_forall (typ : Set) : Set :=
| MyForall (t : typ).

Section MakeILogic.
  Context {typ func : Set} {FV : PartialView func (my_forall typ)}.

  Definition fForall t := f_insert (MyForall typ t).

  Definition mkForall (t : typ) (f : expr typ func) := App (Inj (fForall t)) (Abs t f).

End MakeILogic.

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

  Lemma Id {A} : forall P : A, P = P.
  Proof.
    reflexivity.
  Qed.
 
  Ltac reify_poly e :=
    let k e :=
        pose e in
    reify_expr reify_eq k
               [[ True ]]
               [[ e ]].

  Goal True.
    (* GREGORY, This breaks *)
    reify_poly (forall P : nat, P = P).

  Definition lem_landexistsDL : 
    polymorphic typ 1
                (Lemma.lemma typ (expr typ func) 
                             (rw_concl typ func (expr typ func))).   
  Proof.
    Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
        <:: @Id ::>.
  Qed.
    
  

Definition func_map :
  OneOfType.pmap :=
  list_to_pmap
    (pcons (listOp_func typ)
           (pcons (list_func typ)
                  (pcons SymEnv.func
                         (pcons natFunc
                                pnil)))).

Definition func := OneOf func_map.

Global Instance TableView_func : PartialView func SymEnv.func :=
  PartialViewPMap 3 func_map eq_refl.
Global Instance NatView_func : PartialView func natFunc :=
  PartialViewPMap 4 func_map eq_refl.
Global Instance ListView_func : PartialView func (list_func typ) :=
  PartialViewPMap 2 func_map eq_refl.
Global Instance ListOpView_func : PartialView func (listOp_func typ) :=
  PartialViewPMap 1 func_map eq_refl.

Class Environment := { simple_env :> @SymEnv.functions typ _}.

Existing Instance RelDec_from_RType.

Section SimpleFunc.

  Context {fs : Environment}.

  Global Instance RSym_func : RSym func.
  Proof.
    apply RSymOneOf.
    repeat first [eapply RSym_All_Branch_None |
                  eapply RSym_All_Branch_Some |
                  eapply RSym_All_Empty].

    apply RSym_ListOpFunc.
    apply RSym_ListFunc.
    apply RSym_NatFunc.
    apply RSym_func; apply fs.
  Defined.

  Global Instance RSymOk_func : RSymOk RSym_func.
  apply RSymOk_OneOf.

  repeat first [eapply RSymOk_All_Branch_None |
                eapply RSymOk_All_Branch_Some; [apply _ | |] |
                eapply RSymOk_All_Empty].
  Defined.

  Global Instance Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
  Global Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := @ExprOk_expr _ _ _ _ _ _ _ _.

  Require Import MirrorCore.VariablesI.
  Require Import MirrorCore.Lambda.ExprVariables.

  Global Instance ExprVar_expr : ExprVar (expr typ func) := _.
  Global Instance ExprVarOk_expr : ExprVarOk ExprVar_expr := _.

  Global Instance ExprUVar_expr : ExprUVar (expr typ func) := _.
  Global Instance ExprUVarOk_expr : ExprUVarOk ExprUVar_expr := _.

  Definition subst : Type :=
    FMapSubst.SUBST.raw (expr typ func).
  Global Instance SS : SubstI.Subst subst (expr typ func) :=
    @FMapSubst.SUBST.Subst_subst _.
  Global Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
    @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.
Check SubstI.SubstOk.
  Global Instance SO : @SubstI.SubstOk _ _ _ _ _ SS :=
    @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _.
  Global Instance SUO : @SubstI.SubstUpdateOk _ _ _ _ _ _ SU SO :=  @FMapSubst.SUBST.SubstUpdateOk_subst typ RType_typ (expr typ func) _ _.

End SimpleFunc.

Section ReifyFunc.

  Global Instance Reify_func : Reify (expr typ func) :=
    Reify_func typ func (reify_nat typ func :: reify_list typ func :: reify_listOp typ func :: nil).

End ReifyFunc.

Definition rt := reify_scheme typ.
Definition re := reify_scheme (expr typ func).

Reify Declare Syntax patterns_simple_typ := rt.
Reify Declare Syntax patterns_simple_expr := re.



Ltac reify trm :=
  let t := fresh "t" in
  let k e := pose e as t
  in
  reify_expr patterns_simple_expr k [[ True ]] [[ trm ]]; cbv beta iota in t.

Goal True.
  reify (In 5 (5::4::3::nil)).

  apply I.
Qed.
(*
SearchAbout In.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.

Instance Reify_lemma : Reify (lemma typ (expr typ func) (expr typ func)).
Check @Reify_rlemma typ (expr typ func).
Admitted.

Definition lem_in_eq : polymorphic typ 1 (Lemma.lemma typ (expr typ func) (expr typ func)) :=
Eval unfold Lemma.add_var, Lemma.add_prem, Lemma.vars, Lemma.concl, Lemma.premises in
  <:: @in_eq ::>.

SearchAbout Reify Lemma.lemma.




unfold Lemma.mkLemma.
 :=
  Eval unfold Lemma.add_var, Lemma.add_prem , Lemma.vars , Lemma.concl , Lemma.premises in
*)