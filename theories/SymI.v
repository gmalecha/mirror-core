Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section symbols.
  Variable typ : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Variable func : Type.

  Class RSym : Type :=
  { typeof_sym : func -> option typ
    (** TODO(gmalecha): This could be problematic if
     ** any of any [func] denotes to a term that contains
     ** a unification variable.
     **)
  ; symD : forall f : func,
             match typeof_sym f with
               | None => unit
               | Some t => typD nil t
             end
  ; sym_eqb : func -> func -> option bool
  }.

  Class RSymOk (R : RSym) : Type :=
  { sym_eqbOk : forall a b, match sym_eqb a b with
                              | None => True
                              | Some true => a = b
                              | Some false => a <> b
                            end
  }.

  Context {RSym_func : RSym}.

  Definition symAs (f : func) (t : typ) : option (typD nil t) :=
    match typeof_sym f as ft
          return match ft with
                   | None => unit
                   | Some t => typD nil t
                 end -> option (typD nil t)
    with
      | None => fun _ => None
      | Some ft => fun val =>
        match type_cast nil t ft with
          | None => None
          | Some pf => Some (Relim (fun x => x) pf val)
        end
    end (symD f).

  Theorem symAs_Some : forall f t (pf : typeof_sym f = Some t),
    symAs f t =
    Some match pf in _ = z return match z with
                                    | None => unit
                                    | Some z => typD nil z
                                  end with
           | eq_refl => symD f
         end.
  Proof.
    intros. unfold symAs.
    generalize (symD f).
    rewrite pf. intros.
    rewrite (type_cast_refl); eauto.
  Qed.

  (** This helper function makes it a little bit easier to construct
   ** [RSym] instances by not requiring the split. It is a little bit less
   ** efficient in some instances in some cases where type checking can
   ** be done independently of determining the denotation function.
   **)
  Definition RSym_from
             (fd : func -> option {t : typ & typD nil t})
             (eqb : func -> func -> option bool) : RSym :=
  {| typeof_sym := fun f =>
                    match fd f with
                      | None => None
                      | Some (existT t _) => Some t
                    end
   ; symD := fun f =>
               match fd f as F return match match F with
                                              | None => None
                                              | Some (existT t _) => Some t
                                            end
                                      with
                                        | None => unit
                                        | Some t => typD nil t
                                      end
               with
                 | None => tt
                 | Some (existT t d) => d
               end
   ; sym_eqb := eqb
   |}.

End symbols.

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
                                    | Some t => typD nil t
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