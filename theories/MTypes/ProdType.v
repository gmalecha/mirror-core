Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.MTypes.ModularTypes.

Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

(* This universe is only here as prod_typ otherwise is cast to nat->Prop *)
Universes T.

Inductive prod_typ : nat -> Type@{T} :=
  | tProd : prod_typ 2.
  
Definition prod_typ_dec {n} (a : prod_typ n) : forall b, {a = b} + {a <> b} :=
    match a as a in prod_typ n return forall b : prod_typ n, {a = b} + {a <> b} with
    | tProd =>
      fun b =>
        match b as b in prod_typ 2 return {tProd = b} + {tProd <> b} with
        | tProd => left eq_refl
        end
    end.

Definition prod_typD {n} (t : prod_typ n) : type_for_arity n :=
  match t with
    tProd => prod
  end.

Section FuncView_prod_type.
  Context {typ : Type}.
  Context {FV : FuncView typ (prod_typ 2 * typ * typ)}.

  Definition tyProd t u := f_insert (tProd, t, u).

  Definition ptrn_tyProd {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (prod_typ 2 * typ * typ) T :=
    fun f U good bad => p (snd (fst f), snd f) U good (fun x => bad f).

  Global Instance ptrn_tyProd_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p}
  : ptrn_ok (ptrn_tyProd p).
  Proof.
    red; intros.
    destruct x as [[q t] u]; simpl; [destruct (Hok (t, u))].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; unfold ptrn_tyProd; rewrite H; reflexivity. }
  Qed.

End FuncView_prod_type.

Section RelDec_prod_type.

  Global Instance RelDec_prod_typ (x : nat) : RelDec (@eq (prod_typ x)) := {
    rel_dec := fun a b => 
                 match x with
                 | 2 => true
                 | _ => false
                 end
  }.

  Definition prod_typ_eq (x y : prod_typ 2) : x = y :=
    match x, y with
    | tProd, tProd => eq_refl
    end.

  Global Instance RelDecOk_prod_typ (x : nat) : RelDec_Correct (RelDec_prod_typ x).
  Proof.
    split; intros.
    destruct x; simpl in *; [inversion y|].
    destruct x; simpl in *; [inversion y|].
    destruct x; simpl in *; [|inversion y].
    unfold rel_dec. simpl.
    split; intros; [|reflexivity].
    apply prod_typ_eq.
  Qed.
  
End RelDec_prod_type.