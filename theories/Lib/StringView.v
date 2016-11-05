Require Import Coq.Strings.String.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
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

Inductive stringFunc : Set  :=
| pString  : string -> stringFunc%type.

Section StringFuncInst.
  Context {typ func : Set} {RType_typ : RType typ}.
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
  { typeof_sym := typeofStringFunc;
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
  Polymorphic Context {func : Set}.
  Polymorphic Context {FV : PartialView func stringFunc}.

  Polymorphic Definition fString s := f_insert (pString s).

  Polymorphic Definition fptrnString@{V L R} {T : Type@{V}} (p : Ptrns.ptrn@{Set V L R} string T)
  : ptrn@{Set V L R} stringFunc T :=
    fun f U good bad =>
      match f with
      | pString s => p s U good (fun x => bad f)
      end.

  Global Polymorphic Instance fptrnString_ok {T : Type} {p : ptrn string T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnString p).
  Proof.
    red; intros; try (right; unfold Fails; reflexivity).
    destruct x; simpl; destruct (Hok s).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Polymorphic Lemma Succeeds_fptrnString {T : Type} (f : stringFunc) (p : ptrn string T) (res : T)
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

  Global Polymorphic Instance fptrnString_SucceedsE {T : Type} {f : stringFunc}
         {p : ptrn string T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnString p) res :=
  { s_result := exists s, Succeeds s p res /\ f = pString s;
    s_elim := @Succeeds_fptrnString T f p res pok
  }.

End MakeString.

Section mkString.
  Polymorphic Context {typ func : Set}.
  Polymorphic Context {FV : PartialView func stringFunc}.

  Polymorphic Definition mkString (s : string) := Inj (typ:=typ) (fString s).

End mkString.

Section PtrnString.
  Context {typ func : Set}.
  Context {FV : PartialView func stringFunc}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkString typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnString@{V L R} {T : Type@{V}} (p : ptrn@{Set V L R} string T)
  : ptrn@{Set V L R} (expr typ func) T :=
    inj (ptrn_view FV (fptrnString p)).

End PtrnString.

Require Import MirrorCore.Reify.ReifyClass.

Section ReifyString.
  Context {typ func : Set} {FV : PartialView func stringFunc}.

  Definition reify_cstring : Command (expr typ func) :=
    CPattern (ls := (string:Type)::nil) (RHasType string (RGet 0 RIgnore)) (fun x => Inj (fString x)).

  Definition reify_string : Command (expr typ func) :=
    CFirst (reify_cstring :: nil).

End ReifyString.

Arguments reify_string _ _ {_}.