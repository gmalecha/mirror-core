Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section symbols.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable func : Type.

  Class RSym : Type :=
  { typeof_sym : func -> option typ
  ; symD : forall f : func, match typeof_sym f with
                               | None => unit
                               | Some t => typD nil t
                             end
  }.

  Context {RType_typ : RType typD}.
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
        match type_cast (fun x => x) nil ft t with
          | None => None
          | Some cast => Some (cast val)
        end
    end (symD f).

  Context {RTypeOk_typ : RTypeOk RType_typ}.

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
    destruct (typ_cast_refl nil t (fun x => x)).
    intuition.
    match goal with
      | H : ?Y = _ |- match ?X with _ => _ end = _ =>
        change X with Y ; rewrite H
    end; intros.
    f_equal. eauto.
  Qed.

  (** This helper function makes it a little bit easier to construct
   ** [RSym] instances by not requiring the split. It is a little bit less
   ** efficient in some instances in some cases where type checking can
   ** be done independently of determining the denotation function.
   **)
  Definition RSym_from (fd : func -> option {t : typ & typD nil t}) : RSym :=
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
   |}.

End symbols.
