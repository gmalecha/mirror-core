Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
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
Require Import MirrorCore.Views.Ptrns.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive stringFunc : Type :=
  | pString  : string -> stringFunc.

Section StringFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ0_tyString : Typ0 _ string}.

  Let tyString : typ := @typ0 _ _ _ Typ0_tyString.

  Definition typeofStringFunc (nf : stringFunc) : option typ :=
    match nf with
      | pString _ => Some tyString
   end.
  
  Definition stringFuncEq (a b : stringFunc) : option bool :=
    match a , b with
      | pString s, pString t => Some (s ?[ eq ] t)
  end.
	
  Definition stringR (s : string) : typD tyString :=
    castR id string s.

  Definition string_func_symD bf :=
    match bf as bf return match typeofStringFunc bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pString s => stringR s
    end.
  
  Global Instance RSym_StringFunc
  : SymI.RSym stringFunc := 
    {
      typeof_sym := typeofStringFunc;
      symD := string_func_symD ;
      sym_eqb := stringFuncEq
    }.
  
  Global Instance RSymOk_StringFunc : SymI.RSymOk RSym_StringFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try reflexivity.
    consider (s ?[ eq ] s0); intros; subst; congruence.
  Qed.

End StringFuncInst.

Section MakeString.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func stringFunc}.

  Definition fString s := f_insert (pString s).

  Definition mkString (s : string) := Inj (typ := typ) (fString s).

  Definition fptrnString {T : Type} (p : Ptrns.ptrn string T) : ptrn stringFunc T :=
    fun f U good bad =>
      match f with
        | pString s => p s U good (fun x => bad f)
      end.

  Global Instance fptrnString_ok {T : Type} {p : ptrn string T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnString p).
  Proof.
    red; intros; try (right; unfold Fails; reflexivity).
    destruct x; simpl; destruct (Hok s).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Definition ptrnString {T : Type} (p : ptrn string T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnString p)).

  Lemma Succeeds_fptrnString {T : Type} (f : stringFunc) (p : ptrn string T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnString p) res) :
    exists s, Succeeds s p res /\ f = pString s.
  Proof.
    unfold Succeeds, fptrnString in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok s).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists s; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnString_SucceedsE {T : Type} {f : stringFunc} 
         {p : ptrn string T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnString p) res := {
      s_result := exists s, Succeeds s p res /\ f = pString s;
      s_elim := @Succeeds_fptrnString T f p res pok
    }.

End MakeString.
