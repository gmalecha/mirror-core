Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.MTypes.ModularTypes.

Set Implicit Arguments.
Set Strict Implicit.

(* This universe is only here as prod_typ otherwise is cast to nat->Prop *)
Universes T.

Inductive prod_typ : nat -> Type@{T} :=
| tProd : prod_typ 2.

Definition prod_typ_dec {n} (a : prod_typ n) : forall b, {a = b} + {a <> b} :=
  match a as a in prod_typ n
        return forall b : prod_typ n, {a = b} + {a <> b}
  with
  | tProd =>
    fun b =>
      match b as b in prod_typ 2 return {tProd = b} + {tProd <> b} with
      | tProd => left eq_refl
      end
  end.

Definition prod_typD {n} (t : prod_typ n) : type_for_arity n :=
  match t with
  | tProd => prod
  end.

Section FuncView_prod_type.
  Context {typ : Type}.
  Context {FV : PartialView typ (prod_typ 2 * typ * typ)}.

  Definition tyProd t u := f_insert (tProd, t, u).

  Definition ptrn_tyProd {T : Type} (p : Ptrns.ptrn (typ * typ) T)
  : ptrn (prod_typ 2 * typ * typ) T :=
    fun f U good bad => p (snd (fst f), snd f) U good (fun x => bad f).

  Global Instance ptrn_tyProd_ok {T : Type} {p : ptrn (typ * typ) T}
         {Hok : ptrn_ok p}
  : ptrn_ok (ptrn_tyProd p).
  Proof.
    red; intros.
    destruct x as [[q t] u]; simpl; [destruct (Hok (t, u))].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl;
      unfold ptrn_tyProd; rewrite H; reflexivity. }
  Qed.

End FuncView_prod_type.