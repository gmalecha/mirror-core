Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.

Record TypedValue {T : Type} {RT : RType T} : Type := mkTypedVal
{ tv_type : T
; tv_value : TypesI.typD tv_type }.
Arguments TypedValue _ {_} : clear implicits.
Arguments mkTypedVal {_ _} _ _ : clear implicits.

Section Simple_RSym.
  Context {T} {RT : RType T} {f : Type}
             (fD : f -> option (TypedValue T))
             (fdec : forall a b : f, {a = b} + {a <> b}).
  Definition RSym_simple : RSym f :=
  {| typeof_sym f := match fD f with
                     | Some l => Some l.(tv_type)
                     | None => None
                     end
   ; symD f := match fD f with
               | Some l => l.(tv_value)
               | None => tt
               end
   ; sym_eqb a b := Some match fdec a b with
                         | left _ => true
                         | right _ => false
                         end |}.

  Global Instance RSymOk_simple :  RSymOk RSym_simple.
  Proof. constructor. intros. simpl.
         destruct (fdec a b); auto.
  Qed.
End Simple_RSym.
