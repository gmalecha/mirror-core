Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section symbols_sum.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable func1 func2 : Type.

  Variable RSym_func1 : RSym func1.
  Variable RSym_func2 : RSym func2.

  Instance RSym_sum : RSym (func1 + func2) :=
  { typeof_sym := fun f => match f with
                             | inl f => typeof_sym f
                             | inr f => typeof_sym f
                           end
  ; symD := fun f => match f as f
                              return match match f with
                                             | inl f => typeof_sym f
                                             | inr f => typeof_sym f
                                           end with
                                       | None => unit
                                       | Some t => typD t
                                     end
                        with
                          | inl f => symD f
                          | inr f => symD f
                        end
  ; sym_eqb := fun x y =>
                 match x , y with
                   | inl x , inl y => sym_eqb x y
                   | inr x , inr y => sym_eqb x y
                   | _ , _ => Some false
                 end
  }.

  Hypothesis RSymOk_func1 : RSymOk RSym_func1.
  Hypothesis RSymOk_func2 : RSymOk RSym_func2.

  Instance RSymOk_sum : RSymOk RSym_sum.
  Proof.
    constructor.
    intros.
    destruct a; destruct b; simpl; try congruence.
    { generalize (sym_eqbOk f f0).
      destruct (sym_eqb f f0); auto.
      destruct b; congruence. }
    { generalize (sym_eqbOk f f0).
      destruct (sym_eqb f f0); auto.
      destruct b; congruence. }
  Qed.
End symbols_sum.