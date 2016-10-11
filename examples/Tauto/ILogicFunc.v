Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Reify.ReifyClass.

Require Import McExamples.Tauto.ILogic.
Require Import McExamples.Tauto.MSimpleTyp.

Require Import Coq.Bool.Bool.
Require Import MirrorCore.MTypes.MTypeUnify.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ilfunc : Type :=
| ilf_entails (logic : typ)
| ilf_true (logic : typ)
| ilf_false (logic : typ)
| ilf_and (logic : typ)
| ilf_or (logic : typ)
| ilf_impl (logic : typ)
| ilf_exists (arg logic : typ)
| ilf_forall (arg logic : typ).

Definition ilfunc_unify (a b : ilfunc) (s : FMapPositive.pmap typ)
: option (FMapPositive.pmap typ) :=
  match a , b with
  | ilf_entails t , ilf_entails t'
  | ilf_true t , ilf_true t'
  | ilf_false t , ilf_false t'
  | ilf_and t , ilf_and t'
  | ilf_or t , ilf_or t'
  | ilf_impl t , ilf_impl t' =>
    mtype_unify _ t t' s
  | ilf_exists t l , ilf_exists t' l'
  | ilf_forall t l , ilf_forall t' l' =>
    match mtype_unify _ t t' s with
    | Some s' => mtype_unify _ l l' s
    | None => None
    end
  | _ , _ => None
  end.

Definition ilfunc_logic (x : ilfunc) : typ :=
  match x with
    | ilf_entails t => t
    | ilf_true t => t
    | ilf_false t => t
    | ilf_and t => t
    | ilf_or t => t
    | ilf_impl t => t
    | ilf_exists _ t => t
    | ilf_forall _ t => t
  end.

Section ILogicFuncInst.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Definition logic_ops := forall (t : typ),
    poption (ILogicOps (typD t)).

  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | pSome T => @ILogic _ T
                | pNone => True
              end.

  Variable gs : logic_ops.

  Definition typeof_ilfunc (f : ilfunc) : option typ :=
    match f with
    | ilf_true t
    | ilf_false t => match gs t with
  		     | pSome _ => Some t
		     | pNone => None
  		     end
    | ilf_entails t => match gs t with
		       | pSome _ => Some (tyArr t (tyArr t tyProp))
		       | pNone => None
		       end
    | ilf_and t
    | ilf_or t
    | ilf_impl t => match gs t with
		    | pSome _ => Some (tyArr t (tyArr t t))
		    | pNone => None
		    end
    | ilf_forall a t
    | ilf_exists a t => match gs t with
			| pSome _ => Some (tyArr (tyArr a t) t)
			| pNone => None
			end
    end.

  Global Instance RelDec_ilfunc : RelDec (@eq ilfunc) :=
    { rel_dec := fun a b =>
	           match a, b with
		   | ilf_entails t, ilf_entails t'
		   | ilf_true t, ilf_true t'
		   | ilf_false t, ilf_false t'
		   | ilf_and t, ilf_and t'
		   | ilf_or t, ilf_or t'
		   | ilf_impl t, ilf_impl t' => t ?[eq] t'
		   | ilf_forall a t, ilf_forall a' t'
		   | ilf_exists a t, ilf_exists a' t' => (a ?[eq] a' && t ?[eq] t')%bool
		   | _, _ => false
	         end
    }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite Bool.andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

 Definition trueR {t : typ} {IL : ILogicOps (typD t)} := @ltrue (typD t) IL.
 Definition falseR {t : typ} {IL : ILogicOps (typD t)} := @lfalse (typD t) IL.
 Definition andR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@land (typD t) IL).
 Definition orR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@lor (typD t) IL).
 Definition implR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) (typD t))) (@limpl (typD t) IL).
 Definition entailsR {t : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (typD t) (RFun (typD t) Prop)) (@lentails (typD t) IL).
 Definition existsR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lexists (typD t) IL (typD u)).
 Definition forallR {t u : typ} {IL : ILogicOps (typD t)} :=
   castR id (RFun (RFun (typD u) (typD t)) (typD t)) (@lforall (typD t) IL (typD u)).

 Implicit Arguments trueR [[t] [IL]].
 Implicit Arguments falseR [[t] [IL]].
 Implicit Arguments andR [[t] [IL]].
 Implicit Arguments orR [[t] [IL]].
 Implicit Arguments implR [[t] [IL]].

 Definition funcD (f : ilfunc) : match typeof_ilfunc f return Type with
				     | Some t => typD t
				     | None => unit
				     end :=
   match f as f
         return match typeof_ilfunc f return Type with
		| Some t => typD t
		| None => unit
		end
   with
   | ilf_true t => match gs t as x return (match match x with
						 | pSome _ => Some t
						 | pNone => None
						 end with
				           | Some t0 => typD t0
					   | None => unit
					   end) with
		   | pSome t => @ltrue _ t
		   | pNone => tt
		   end
   | ilf_false t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some t
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => lfalse
     | pNone => tt
     end
   | ilf_entails t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t tyProp))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => entailsR
     | pNone => tt
     end
   | ilf_and t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => andR
     | pNone => tt
     end
   | ilf_impl t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => implR
     | pNone => tt
     end
   | ilf_or t =>
     match gs t as x
           return (match match x with
			 | pSome _ => Some (tyArr t (tyArr t t))
			 | pNone => None
			 end with
		   | Some t0 => typD t0
		   | None => unit
		   end) with
     | pSome t => orR
     | pNone => tt
     end
   | ilf_exists a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => existsR
     | pNone => tt
     end
   | ilf_forall a t =>
     match gs t as x return (match match x with
				   | pSome _ => Some (tyArr (tyArr a t) t)
				   | pNone => None
				   end with
			     | Some t0 => typD t0
			     | None => unit
			     end) with
     | pSome t0 => forallR
     | pNone => tt
     end
   end.

End ILogicFuncInst.


Section MakeILogic.
  Variable t u : typ.

  Definition fTrue := ilf_true t.
  Definition fFalse := ilf_false t.
  Definition fAnd := ilf_and t.
  Definition fOr := ilf_or t.
  Definition fImpl := ilf_impl t.
  Definition fEntails := ilf_entails t.
  Definition fExists := ilf_exists t u.
  Definition fForall := ilf_forall t u.

  Definition mkEntails (P Q : expr typ ilfunc) := App (App (Inj fEntails) P) Q.
  Definition mkTrue : expr typ ilfunc := Inj fTrue.
  Definition mkFalse : expr typ ilfunc := Inj fFalse.
  Definition mkAnd (P Q : expr typ ilfunc) := App (App (Inj fAnd) P) Q.
  Definition mkOr (P Q : expr typ ilfunc) := App (App (Inj fOr) P) Q.
  Definition mkImpl (P Q : expr typ ilfunc) := App (App (Inj fImpl) P) Q.
  Definition mkExists (f : expr typ ilfunc) := App (Inj fExists) (Abs t f).
  Definition mkForall (f : expr typ ilfunc) := App (Inj fForall) (Abs t f).

End MakeILogic.

Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Subst.FMapSubst.
(*
Definition gs : logic_ops :=
  fun t =>
    match t with
    | ModularTypes.tyProp => pSome _
    | _ => pNone
    end.
*)
Section ILFunc_insts.
  Variable gs : logic_ops.
  Global Instance RSym_ilfunc : SymI.RSym ilfunc :=
    { typeof_sym := typeof_ilfunc gs
      ; sym_eqb := fun a b => Some (rel_dec a b)
      ; symD := funcD gs
    }.

  Global Instance RSymOk_ilfunc : SymI.RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.


  Global Instance Expr_expr : ExprI.Expr _ (expr typ ilfunc) := @Expr_expr typ ilfunc _ _ _.

  Global Instance Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ ilfunc) Expr_expr :=
    @ExprOk_expr typ ilfunc _ _ _ _ _ _.
  
  Global Instance ExprVar_expr : ExprVar (expr typ ilfunc) := _.
  
  Global Instance ExprVarOk_expr : ExprVarOk ExprVar_expr := _.
  
  Global Instance ExprUVar_expr : ExprUVar (expr typ ilfunc) := _.
  Global Instance ExprUVarOk_expr : ExprUVarOk ExprUVar_expr := _.
  
  Definition subst : Type :=
    FMapSubst.SUBST.raw (expr typ ilfunc).
  Global Instance SS : SubstI.Subst subst (expr typ ilfunc) :=
    @FMapSubst.SUBST.Subst_subst _.
  Global Instance SU : SubstI.SubstUpdate subst (expr typ ilfunc) :=
    @FMapSubst.SUBST.SubstUpdate_subst _ _ _ _.
  Check SubstI.SubstOk.
  Global Instance SO : @SubstI.SubstOk _ _ _ _ _ SS :=
    @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ ilfunc) _.
  Global Instance SUO : @SubstI.SubstUpdateOk _ _ _ _ _ _ SU SO :=  @FMapSubst.SUBST.SubstUpdateOk_subst typ RType_typ (expr typ ilfunc) _ _.

End ILFunc_insts.