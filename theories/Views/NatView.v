Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
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

Inductive natFunc : Type :=
| pNat  : nat -> natFunc
| pPlus : natFunc
| pMinus : natFunc
| pMult : natFunc.

Section NatFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
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
    castR id nat n.

  Definition natD (n : typD tyNat) : nat :=
    castD id nat n.

  Definition plusR : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    castR id (RFun nat (RFun nat nat)) plus.

  Definition minusR : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    castR id (RFun nat (RFun nat nat)) minus.

  Definition multR : typD (tyArr tyNat (tyArr tyNat tyNat)) :=
    castR id (RFun nat (RFun nat nat)) mult.

  Definition nat_func_symD bf :=
    match bf as bf return match typeofNatFunc bf return Type with
			  | Some t => typD t
			  | None => unit
			  end with
    | pNat n => natR n
    | pPlus => plusR
    | pMinus => minusR
    | pMult => multR
    end.

  Global Instance RSym_NatFunc
  : SymI.RSym natFunc :=
  { typeof_sym := typeofNatFunc;
    symD := nat_func_symD ;
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
  Context {FV : PartialView func natFunc}.

  Definition fNat n := f_insert (pNat n).
  Definition fPlus := f_insert pPlus.
  Definition fMinus := f_insert pMinus.
  Definition fMult := f_insert pMult.

  Definition mkNat (n : nat) := Inj (typ := typ) (fNat n).
  Definition mkPlus (m n : expr typ func) := App (App (Inj fPlus) m) n.
  Definition mkMinus (m n : expr typ func) := App (App (Inj fMinus) m) n.
  Definition mkMult (m n : expr typ func) := App (App (Inj fMult) m) n.

  Definition fptrnNat {T : Type} (p : Ptrns.ptrn nat T) : ptrn natFunc T :=
    fun f U good bad =>
      match f with
        | pNat n => p n U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnPlus : ptrn natFunc unit :=
    fun f U good bad =>
      match f with
        | pPlus => good tt
        | _ => bad f
      end.

  Definition fptrnMinus : ptrn natFunc unit :=
    fun f U good bad =>
      match f with
        | pMinus => good tt
        | _ => bad f
      end.

  Definition fptrnMult : ptrn natFunc unit :=
    fun f U good bad =>
      match f with
        | pMult => good tt
        | _ => bad f
      end.

  Global Instance fptrnNat_ok {T : Type} {p : ptrn nat T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnNat p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok n) | | |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnPlus_ok : ptrn_ok fptrnPlus.
  Proof.
    red; intros.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { left; exists tt; compute; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnMinus_ok : ptrn_ok fptrnMinus.
  Proof.
    red; intros.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left; exists tt; compute; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnMult_ok : ptrn_ok fptrnMult.
  Proof.
    red; intros.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left; exists tt; compute; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnNat {T : Type} (f : natFunc) (p : ptrn nat T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnNat p) res) :
    exists n, Succeeds n p res /\ f = pNat n.
  Proof.
    unfold Succeeds, fptrnNat in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok n).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists n; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnPlus (f : natFunc) (res : unit) (H : Succeeds f fptrnPlus res) :
    f = pPlus /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; simpl in H; try congruence.
  Qed.

  Lemma Succeeds_fptrnMinus (f : natFunc) (res : unit) (H : Succeeds f fptrnMinus res) :
    f = pMinus /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; simpl in H; try congruence.
  Qed.

  Lemma Succeeds_fptrnMult (f : natFunc) (res : unit) (H : Succeeds f fptrnMult res) :
    f = pMult /\ res = tt.
  Proof.
    split; [|destruct res; reflexivity].
    specialize (H bool (fun _ => true) (fun _ => false)).
    destruct f; simpl in H; try congruence.
  Qed.

  Global Instance fptrnNat_SucceedsE {T : Type} {f : natFunc}
         {p : ptrn nat T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnNat p) res :=
  { s_result := exists n, Succeeds n p res /\ f = pNat n;
    s_elim := @Succeeds_fptrnNat T f p res pok
  }.

  Global Instance fptrnPlus_SucceedsE {f : natFunc} (res : unit)
  : SucceedsE f fptrnPlus res :=
  { s_result := f = pPlus /\ res = tt;
    s_elim := @Succeeds_fptrnPlus f res
  }.

  Global Instance fptrnMinus_SucceedsE {f : natFunc} (res : unit)
  : SucceedsE f fptrnMinus res :=
  { s_result := f = pMinus /\ res = tt;
    s_elim := @Succeeds_fptrnMinus f res
  }.

  Global Instance fptrnMult_SucceedsE {f : natFunc} (res : unit)
  : SucceedsE f fptrnMult res :=
  { s_result := f = pMult /\ res = tt;
    s_elim := @Succeeds_fptrnMult f res
  }.

End MakeNat.

Section PtrnNat.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : PartialView func natFunc}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkString typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnNat {T : Type} (p : ptrn nat T) : ptrn (expr typ func) T :=
    inj (ptrn_view FV (fptrnNat p)).

  Definition ptrnPlus {A B T : Type}
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun xy => match xy with (_, a, b) => (a, b) end)
         (app (app (inj (ptrn_view FV fptrnPlus)) a) b).

  Definition ptrnMinus {A B T : Type}
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun xy => match xy with (_, a, b) => (a, b) end)
         (app (app (inj (ptrn_view FV fptrnMinus)) a) b).

  Definition ptrnMult {A B T : Type}
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun xy => match xy with (_, a, b) => (a, b) end)
         (app (app (inj (ptrn_view FV fptrnMult)) a) b).

End PtrnNat.