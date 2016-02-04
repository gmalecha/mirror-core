Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.MTypes.ModularTypes.

Set Implicit Arguments.
Set Strict Implicit.

(* This universe is only here as list_typ otherwise is cast to nat->Prop *)
Universes T.
  
Inductive list_typ : nat -> Type@{T} :=
| tList : list_typ 1.

Definition list_typ_dec {n} (a : list_typ n) : forall b, {a = b} + {a <> b} :=
    match a as a in list_typ n return forall b : list_typ n, {a = b} + {a <> b} with
    | tList =>
      fun b =>
        match b as b in list_typ 1 return {tList = b} + {tList <> b} with
        | tList => left eq_refl
        end
    end.

Definition list_typD {n} (t : list_typ n) : type_for_arity n :=
  match t with
	tList => list
  end.

Section FuncView_list_type.
  Context {typ : Type}.
  Context {FV : FuncView typ (list_typ 1 * typ)}.

  Definition tyList t := f_insert (tList, t).

End FuncView_list_type.

