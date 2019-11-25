Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.MTypes.ModularTypes.

Require Import ExtLib.Core.RelDec.

Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Strict Implicit.

Inductive base_typ : nat -> Type :=
| tNat : base_typ 0
| tString : base_typ 0
| tBool : base_typ 0
| tProp : base_typ 0.

Definition base_typ_dec {n} (a : base_typ n) : forall b, {a = b} + {a <> b}.
  refine(
    match a as a in base_typ n
          return forall b : base_typ n, {a = b} + {a <> b}
    with
    | tNat =>
      fun b =>
        match b as b in base_typ 0 return {tNat = b} + {tNat <> b} with
        | tNat => left eq_refl
        | _ => right (fun pf => _)
        end
    | tString =>
      fun b =>
        match b as b in base_typ 0 return {tString = b} + {tString <> b} with
        | tString => left eq_refl
        | _ => right (fun pf => _)
        end
    | tBool =>
      fun b =>
        match b as b in base_typ 0 return {tBool = b} + {tBool <> b} with
        | tBool => left eq_refl
        | _ => right (fun pf => _)
        end
    | tProp =>
      fun b =>
        match b as b in base_typ 0 return {tProp = b} + {tProp <> b} with
        | tProp => left eq_refl
        | _ => right (fun pf => _)
        end
    end);  clear -pf; inversion pf.
Defined.

Definition base_typD {n} (t : base_typ n) : type_for_arity n :=
  match t with
  | tNat => nat
  | tString => string
  | tBool => bool
  | tProp => Prop
  end.

Section FuncView_base_type.
  Context {typ : Type}.
  Context {FV : PartialView typ (base_typ 0)}.

  Definition tyNat := f_insert tNat.
  Definition tyBool := f_insert tBool.
  Definition tyString := f_insert tString.
  Definition tyProp := f_insert tProp.

  Definition ptrn_tyNat : ptrn (base_typ 0) (base_typ 0) :=
    fun f U good bad =>
      match f return _ with
      | tNat => good f
      | _ => bad f
      end.

  Definition ptrn_tyBool : ptrn (base_typ 0) (base_typ 0) :=
    fun f U good bad =>
      match f return _ with
      | tBool => good f
      | _ => bad f
      end.

  Definition ptrn_tyString : ptrn (base_typ 0) (base_typ 0) :=
    fun f U good bad =>
      match f return _ with
      | tString => good f
      | _ => bad f
      end.

  Definition ptrn_tyProp : ptrn (base_typ 0) (base_typ 0) :=
    fun f U good bad =>
      match f return _ with
      | tProp => good f
      | _ => bad f
      end.

  Global Instance ptrn_tyNat_ok  : ptrn_ok ptrn_tyNat.
  Proof.
    red; intros.
    unfold ptrn_tyNat.
    destruct x; simpl.
    { left. exists tNat. unfold Succeeds. reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance ptrn_tyBool_ok  : ptrn_ok ptrn_tyBool.
  Proof.
    red; intros.
    unfold ptrn_tyBool.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. exists tBool. unfold Succeeds. reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance ptrn_tyString_ok  : ptrn_ok ptrn_tyString.
  Proof.
    red; intros.
    unfold ptrn_tyString.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { left. exists tString. unfold Succeeds. reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance ptrn_tyProp_ok  : ptrn_ok ptrn_tyProp.
  Proof.
    red; intros.
    unfold ptrn_tyProp.
    destruct x; simpl.
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. exists tProp. unfold Succeeds. reflexivity. }
  Qed.

End FuncView_base_type.

Section RelDec_base_type.

  Global Instance RelDec_base_typ (x : nat) : RelDec (@eq (base_typ x)) := {
    rel_dec a b :=
      match base_typ_dec a b with
      | left _ => true
      | right _ => false
      end
  }.

  Global Instance RelDecOk_base_typ (x : nat) : RelDec_Correct (RelDec_base_typ x).
  Proof.
    split; intros.
    unfold rel_dec; simpl.
    remember (base_typ_dec x0 y).
    destruct s; subst; intuition.
  Qed.

End RelDec_base_type.
