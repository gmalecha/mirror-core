Require Import ExtLib.Data.Positive.
Require Import MirrorCore.CTypes.CoreTypes.

Inductive VType : nat -> Type :=
| tVar : positive -> VType 0.

Definition VType_dec n (a : VType n) : forall b : VType n, {a = b} + {a <> b} :=
  match a as a in VType n return forall b, {a = b} + {a <> b} with
  | tVar n => fun b =>
    match b as b in VType 0 return {tVar n = b} + {tVar n <> b} with
    | tVar n' => match Pos.eq_dec n n' with
                 | left pf => left (f_equal _ pf)
                 | right pf =>
                   right (fun pf' : tVar n = tVar n' =>
                            pf match eq_sym pf' in _ = t
                                     return match t with
                                            | tVar x => x
                                            end = n'
                               with
                               | eq_refl => eq_refl
                               end)
                 end
    end
  end.

Instance TSym_VType : TSym VType :=
{ symbolD n x := match x with
                 | tVar _ => Empty_set
                 end
; symbol_dec := VType_dec }.