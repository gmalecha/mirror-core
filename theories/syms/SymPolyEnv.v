(** This file defines a Symbol instantiation that
 ** supports a polymorphic function environment
 ** but references must be fully instantiated.
 **)
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Generic.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RTypeOk_typD : RTypeOk.

  Inductive func : Type :=
  | FRef (fi : positive) (ts : list typ).

  Fixpoint list_Rty (x y : list typ) : bool :=
    match x , y with
      | nil , nil => true
      | x :: xs , y :: ys =>
        if x ?[ Rty ] y then list_Rty xs ys else false
      | _ , _ => false
    end.

  Record function := F
  { fenv : nat
  ; ftype : quant typ fenv
  ; fdenote : paraquant typD fenv ftype
  }.

  Definition functions := PositiveMap.t function.
  Variable fs : functions.

  Definition func_typeof_sym (f : func) : option typ :=
    match f with
      | FRef i ts =>
        match PositiveMap.find i fs with
          | None => None
          | Some ft =>
            qapply _ ts ft.(ftype)
        end
    end.

  Definition symD_sym (f : func)
  : match func_typeof_sym f with
      | None => unit:Type
      | Some t => typD t
    end :=
    match f as f
          return match func_typeof_sym f with
                   | None => unit:Type
                   | Some t => typD t
                 end
    with
      | FRef i ts' =>
        match PositiveMap.find i fs as x
              return match
                match x with
                  | Some ft =>
                    qapply _ ts' ft.(ftype)
                  | None => None
                end
              with
                | Some t => typD t
                | None => unit
              end
        with
          | Some {| fenv := fenv ; ftype := ftype ; fdenote := fd |} =>
            paraquant_apply _ _ ts' _ fd
          | None => tt
        end
    end.

  (** TODO: This is pretty ugly, it is because it doesn't
   ** match up well with [func_typeof_func].
   **)
  Global Instance RSym_func : RSym func :=
  { sym_eqb := fun l r =>
                 match l , r with
                   | FRef il al , FRef ir ar =>
                     if il ?[ eq ] ir then
                       Some (list_Rty al ar)
                     else
                       Some false
                 end
  ; typeof_sym := func_typeof_sym
  ; symD := symD_sym
  }.

  Lemma list_Rty_eq : forall a b, list_Rty a b = true <-> a = b.
  Proof.
    induction a; destruct b; simpl.
    { intuition. }
    { intuition congruence. }
    { intuition congruence. }
    { specialize (IHa b).
      match goal with
        | |- ((if ?X then _ else _) = _) <-> _ =>
          consider X; intros
      end.
      { red in H. subst. rewrite IHa.
        split. intros; subst; reflexivity.
        inversion 1; auto. }
      { unfold Rty in *.
        split; intros; congruence. } }
  Qed.


  Global Instance RSymOk_func : RSymOk RSym_func.
  Proof.
    constructor.
    unfold sym_eqb. simpl.
    destruct a; destruct b.
    consider (fi ?[ eq ] fi0); intros; subst; try congruence.
    generalize (list_Rty_eq ts ts0).
    destruct (list_Rty ts ts0).
    clear. intuition. f_equal; auto.
    clear. intuition.
    inversion H0. apply H2 in H3. congruence.
  Qed.

  Definition from_list {T} (ls : list T) : PositiveMap.t T :=
    (fix from_list ls : positive -> PositiveMap.t T :=
       match ls with
         | nil => fun _ => PositiveMap.empty _
         | l :: ls => fun p =>
                        PositiveMap.add p l (from_list ls (Pos.succ p))
       end) ls 1%positive.

End typed.
