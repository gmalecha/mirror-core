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
  ; symD : forall ts (f : func),
             match typeof_sym f with
               | None => unit
               | Some t => typD ts t
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

  Definition symAs ts (f : func) (t : typ) : option (typD ts t) :=
    match typeof_sym f as ft
          return match ft with
                   | None => unit
                   | Some t => typD ts t
                 end -> option (typD ts t)
    with
      | None => fun _ => None
      | Some ft => fun val =>
        match type_cast ts t ft with
          | None => None
          | Some pf => Some (Relim (fun x => x) pf val)
        end
    end (symD ts f).

  Theorem symAs_Some : forall ts f t (pf : typeof_sym f = Some t),
    symAs ts f t =
    Some match pf in _ = z return match z with
                                    | None => unit
                                    | Some z => typD ts z
                                  end with
           | eq_refl => symD ts f
         end.
  Proof.
    intros. unfold symAs.
    generalize (symD ts f).
    rewrite pf. intros.
    rewrite (type_cast_refl); eauto.
  Qed.

  (** This helper function makes it a little bit easier to construct
   ** [RSym] instances by not requiring the split. It is a little bit less
   ** efficient in some instances in some cases where type checking can
   ** be done independently of determining the denotation function.
   **)
  Definition RSym_from
             (fd : func -> option {t : typ & forall ts, typD ts t})
             (eqb : func -> func -> option bool) : RSym :=
  {| typeof_sym := fun f =>
                    match fd f with
                      | None => None
                      | Some (existT t _) => Some t
                    end
   ; symD := fun ts f =>
               match fd f as F return match match F with
                                              | None => None
                                              | Some (existT t _) => Some t
                                            end
                                      with
                                        | None => unit
                                        | Some t => typD ts t
                                      end
               with
                 | None => tt
                 | Some (existT t d) => d ts
               end
   ; sym_eqb := eqb
   |}.

End symbols.
