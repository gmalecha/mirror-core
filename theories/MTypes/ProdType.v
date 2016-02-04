Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.MTypes.ModularTypes.

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

End FuncView_prod_type.