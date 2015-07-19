Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
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
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.TrmD.
Require Import MirrorCore.Views.Ptrns.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive natFunc :=
  | pNat  : nat -> natFunc
  | pPlus : natFunc
  | pMinus : natFunc
  | pMult : natFunc.

Section NatFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ0_tyNat : Typ0 _ nat}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyNat : typ := @typ0 _ _ _ Typ0_tyNat.

  Definition typeofNatFunc (nf : natFunc) : option typ :=
    match nf with
      | pNat _ => Some tyNat
      | pPlus => Some (tyArr tyNat (tyArr tyNat tyNat))
      | pMinus => Some (tyArr tyNat (tyArr tyNat tyNat))
      | pMult => Some (tyArr tyNat (tyArr tyNat tyNat))
   end.
  
  Definition natFuncEq (a b : natFunc) : option bool :=
    match a , b with
      | pNat n, pNat m => Some (n ?[ eq ] m)
      | pPlus, pPlus => Some true
      | pMinus, pMinus => Some true
      | pMult, pMult => Some true

      | _, _ => None
  end.
	
  Definition natR (n : nat) : typD tyNat :=
    trmR n (typ0_cast (Typ0 := Typ0_tyNat)).

  Definition natD (n : typD tyNat) : nat :=
    trmD n (typ0_cast (Typ0 := Typ0_tyNat)).

  Definition plusD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) + (natD b))).

  Definition minusD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) - (natD b))).

  Definition multD : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    tyArrR2 (fun a b => natR ((natD a) * (natD b))).

  Definition base_func_symD bf :=
    match bf as bf return match typeofNatFunc bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pNat n => natR n
      | pPlus => plusD
      | pMinus => minusD
      | pMult => multD
    end.
  
  Global Instance RSym_NatFunc
  : SymI.RSym natFunc := 
    {
      typeof_sym := typeofNatFunc;
      symD := base_func_symD ;
      sym_eqb := natFuncEq
    }.
  
  Global Instance RSymOk_NatFunc : SymI.RSymOk RSym_NatFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try reflexivity.
    consider (n ?[ eq ] n0); intros; subst; congruence.
  Qed.

End NatFuncInst.

Section MakeNat.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func natFunc}.

  Definition fNat n := f_insert (pNat n).
  Definition fPlus := f_insert pPlus.
  Definition fMinus := f_insert pMinus.
  Definition fMult := f_insert pMult.

  Definition mkNat (n : nat) := Inj (typ := typ) (fNat n).
  Definition mkPlus (m n : expr typ func) := App (App (Inj fPlus) m) n.
  Definition mkMinus (m n : expr typ func) := App (App (Inj fMinus) m) n.
  Definition mkMult (m n : expr typ func) := App (App (Inj fMult) m) n.

  Definition fptrnNat : ptrn func nat :=
    fun f _ good bad => 
    match f_view f with
      | Some (pNat n) => good n
      | _ => bad f
    end.

  Definition ptrnNat : ptrn (expr typ func) nat :=
    inj fptrnNat.

  Definition fptrnPlus : ptrn func unit :=
    fun f _T good bad => 
    match f_view f with
      | Some pPlus => good tt
      | _ => bad f
    end.

  Definition ptrnPlus {A B : Type} 
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun x => match x with | (_, a, b) => (a, b) end) (app (app (inj fptrnPlus) a) b).

  Definition fptrnMinus : ptrn func unit :=
    fun f _T good bad => 
    match f_view f with
      | Some pPlus => good tt
      | _ => bad f
    end.

  Definition ptrnMinus {A B : Type} 
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun x => match x with | (_, a, b) => (a, b) end) (app (app (inj fptrnMinus) a) b).

  Definition fptrnMult : ptrn func unit :=
    fun f _T good bad => 
    match f_view f with
      | Some pPlus => good tt
      | _ => bad f
    end.

  Definition ptrnMult {A B : Type} 
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun x => match x with | (_, a, b) => (a, b) end) (app (app (inj fptrnMult) a) b).

End MakeNat.
