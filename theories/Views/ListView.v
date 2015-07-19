Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.TrmD.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive list_func (typ : Type) :=
  | pNil : typ -> list_func typ
  | pCons : typ -> list_func typ.

Section ListFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_tyList : Typ1 _ list}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyList : typ -> typ := @typ1 _ _ _ _.

  Definition typeof_list_func lf :=
    match lf with
      | pNil t => Some (tyList t)
      | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
    end.

  Definition list_func_eq (a b : list_func typ) : option bool :=
    match a , b with
      | pNil t1, pNil t2 => Some (t1 ?[ eq ] t2)
      | pCons t1, pCons t2 => Some (t1 ?[ eq ] t2)
      | _, _ => None
    end.

  Global Instance RelDec_list_func : RelDec (@eq (list_func typ)) := 
    {
      rel_dec a b := match list_func_eq a b with 
    	  	       | Some b => b 
    		       | None => false 
    		     end
    }.

  Definition listE {A : Type} {t : typ} (e : typD t = A) : typD (tyList t) = list A :=
    eq_ind (typD t) (fun B : Type => typD (tyList t) = list B) (typ1_cast t) A e.

  Definition listD {t : typ} (lst : typD (tyList t)) : list (typD t) :=
    trmD lst (listE eq_refl).

  Definition listR {t : typ} (lst : list (typD t)) : typD (tyList t) :=
    trmR lst (listE eq_refl).

  Definition nilD t : typD (tyList t) := listR nil.
  Definition consD t : typD (tyArr t (tyArr (tyList t) (tyList t))) :=
    tyArrR2 (fun (x : typD t) (xs : typD (tyList t)) =>
               listR (cons x (trmD xs (listE eq_refl)))).

  Lemma listD_nil t : listD (nilD t) = nil.
  Proof.
    unfold listD, nilD, listR. rewrite trmDR. reflexivity.
  Qed.

  Lemma listR_nil t : listR nil = nilD t.
  Proof.
    reflexivity.
  Qed.

  Definition list_func_symD lf :=
    match lf as lf return match typeof_list_func lf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pNil t => nilD t
      | pCons t => consD t
    end.

  Global Instance RSym_ListFunc : SymI.RSym (list_func typ) := 
    {
      typeof_sym := typeof_list_func;
      symD := list_func_symD;
      sym_eqb := list_func_eq
    }.

  Global Instance RSymOk_ListFunc : SymI.RSymOk RSym_ListFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t0); intuition congruence.
    + consider (t ?[ eq ] t0); intuition congruence.
  Qed.

End ListFuncInst.

Section MakeList.
  Context {typ func : Type} {H : FuncView func (list_func typ)}.
  
  Definition fNil t := f_insert (pNil t).
  Definition fCons t := f_insert (pCons t).

  Definition mkNil t : expr typ func := Inj (fNil t).
  Definition mkCons (t : typ) (x xs : expr typ func) := App (App (Inj (fCons t)) x) xs.

  Definition fptrnNil : ptrn func unit :=
    fun f _ good bad => 
    match f_view f with
      | Some (pNil _) => good tt
      | _ => bad f
    end.

  Definition ptrnNil : ptrn (expr typ func) unit :=
    inj (fptrnNil).

  Definition fptrnCons : ptrn func unit :=
    fun f _T good bad => 
    match f_view f with
      | Some (pCons _) => good tt
      | _ => bad f
    end.
  
  Definition ptrnCons {A B : Type} 
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun xy => match xy with (_, x, y) => (x, y) end) (app (app (inj fptrnCons) a) b).
  
End MakeList.

Section test.
  Context {typ func : Type} {LV : FuncView func (list_func typ)}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {Typ_nat : Typ0 RType_typ nat}.

  Let tyNat := @typ0 _ _ _ _.

  Definition list_nest_ptrn_test : ptrn (expr typ func) Prop :=
    (pmap (fun xy => match xy with
                       | ((x, (y, ys)), a) => a = tt
                     end) (ptrnCons (ptrnCons Ptrns.get (ptrnCons Ptrns.get Ptrns.get)) ptrnNil)).

  Definition list_case_ptrn
             {P:Type}
             (f_nil : P)
             (f_cons : expr typ func -> expr typ func -> P) : ptrn (expr typ func) P :=
    por (pmap (fun _ => f_nil) ptrnNil)
        (pmap (fun xy => match xy with
                           | (x, y) => f_cons x y
                         end) (ptrnCons Ptrns.get Ptrns.get)).
  
  Definition list_case
             {P:Type}
             (f_nil : P)
             (f_cons : expr typ func -> expr typ func -> P)
             (f_default : P) : 
    expr typ func -> P :=
    run_tptrn (pdefault (list_case_ptrn f_nil f_cons) f_default).

End test.