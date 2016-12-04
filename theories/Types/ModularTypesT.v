Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.

Require Import MirrorCore.Util.PolyAcc.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.TypeView.
Require Import MirrorCore.Util.PositivePolyMap.

Universes Ukind.
Universes Usmall Ularge.

Lemma dec_refl
  : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a : T),
    dec a a = left eq_refl.
Proof using.
  intros. destruct (dec a a).
  - uip_all. reflexivity.
  - exfalso; tauto.
    Unshelve. assumption.
Qed.

Class TSym {k : Set} (kindD : k -> Type@{Ukind}) (symbol : k -> Set) : Type :=
{ symbolD : forall {k}, symbol k -> kindD k
; symbol_dec : forall {k} (a b : symbol k), {a = b} + {a <> b}
}.

Arguments symbolD {_} _ {_ _ _} _.
Arguments symbol_dec {_} _ {_ _ _} _ _.

Module Type TypeLang.
  Parameter kind : Set.
  Parameter Kstar : kind.
  Parameter kind_eq_dec : forall a b : kind, {a = b} + {a <> b}.
  Parameter kindD : kind -> Type@{Ukind}.

  Parameter type : (kind -> Set) -> kind -> Set.

  Parameter tyVar : forall tsym k (p : positive), type tsym k.

  Section with_symbols.
    Variable symbol : kind -> Set.

    Parameter RType_type : TSym kindD symbol -> RType (type symbol Kstar).
    Parameter RTypeOk_type : forall ts : TSym kindD symbol, @RTypeOk _ (RType_type ts).

    Parameter type_eq_dec : TSym kindD symbol -> forall {k} (a b : type symbol k),
          {a = b} + {a <> b}.

  End with_symbols.

End TypeLang.


(** For expediancy sake, it might be better to include this in the above. *)
Module Type TypeLangUnify.
  Declare Module RT : TypeLang.
  Import RT.

  Section with_symbols.
    Variable symbol : kind -> Set.

    Parameter type_unify : forall k, type symbol k -> type symbol k ->
                           pmap { k : kind & type symbol k } ->
                           option (pmap { k : kind & type symbol k }).
  End with_symbols.
End TypeLangUnify.
