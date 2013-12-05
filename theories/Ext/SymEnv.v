(** This file defines a Symbol instantiation that
 ** has a special case for [eq] and [not] and supports
 ** other symbols through a polymorphic function
 ** environment.
 **
 ** NOTE
 **  It is not generic because it builds on top of Ext.Types
 **)
Require Import BinPos Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.

Set Implicit Arguments.
Set Strict Implicit.

Inductive func : Type :=
| Equal (t : typ)
| Not
| FRef (fi : positive) (ts : list typ).

Global Instance RelDec_eq_func : RelDec (@eq func) :=
{ rel_dec := fun l r =>
               match l , r with
                 | Equal a , Equal b => a ?[ eq ] b
                 | Not , Not => true
                 | FRef l ls , FRef r rs =>
                   if l ?[ eq ] r then ls ?[ eq ] rs else false
                 | _ , _ => false
               end
}.

Global Instance RelDec_Correct_eq_func : RelDec_Correct RelDec_eq_func.
Proof.
  constructor.
  destruct x; destruct y; simpl; try rewrite rel_dec_correct;
  intuition; subst; auto; try congruence.
  consider (fi ?[ eq ] fi0); intros.
  consider (ts ?[ eq ] ts0); intros. subst; auto.
  inversion H; clear H; subst.
  consider (fi0 ?[ eq ] fi0); try congruence.
  consider (ts0 ?[ eq ] ts0); try congruence.
Qed.

Section RSym.
  Variable ts : types.

  Record function := F
  { fenv : nat
  ; ftype : typ
  ; fdenote : parametric fenv nil (fun env => typD ts env ftype)
  }.

  Definition functions := PositiveMap.t function.
  Variable fs : functions.

  Definition func_typeof_sym (f : func) : option typ :=
    match f with
      | Equal t => Some (tyArr t (tyArr t tyProp))
      | Not => Some (tyArr tyProp tyProp)
      | FRef i ts =>
        match PositiveMap.find i fs with
          | None => None
          | Some ft =>
            if ft.(fenv) ?[ eq ] length ts then
              Some (instantiate_typ ts ft.(ftype))
            else
              None
        end
    end.

  (** TODO: This is pretty ugly, it is because it doesn't
   ** match up well with [func_typeof_func].
   ** - One option is to make the return value of the denotation
   **   function be an option which allows us to encode the
   **   same information.
   **   - The annoying piece about this is that it doesn't
   **     ensure that [func] is sensible (at least definitionally)
   **)
  Global Instance RSym_func : RSym (typD ts) func :=
  { sym_eqb := fun l r => Some (l ?[ eq ] r)
  ; typeof_sym := func_typeof_sym
  ; symD := fun f =>
               match f as f
                     return match func_typeof_sym f with
                              | None => unit
                              | Some t => typD ts nil t
                            end
               with
                 | Equal t => @eq (typD ts nil t)
                 | Not => not
                 | FRef i ts' =>
                   match PositiveMap.find i fs as x
                     return match
                       match x with
                         | Some ft =>
                           if fenv ft ?[ eq ] length ts'
                           then Some (instantiate_typ ts' (ftype ft))
                           else None
                         | None => None
                       end
                     with
                       | Some t => typD ts nil t
                       | None => unit
                     end
                   with
                     | Some {| fenv := fenv ; ftype := ftype ; fdenote := fd |} =>
                       match fenv ?[ eq ] length ts' as zz
                             return fenv ?[ eq ] length ts' = zz ->
                                    match
                                      (if zz
                                       then
                                         Some
                                           (instantiate_typ ts'
                                                            ftype)
                                       else None)
                                    with
                                      | Some t => typD ts nil t
                                      | None => unit
                                    end
                       with
                         | true => fun pf =>
                           match type_apply _ _ ts' nil _ fd as xx
                                 return type_apply _ _ ts' nil _ fd = xx -> _
                           with
                             | None => fun pf' => match _ : False with end
                             | Some z => fun _ => z
                           end eq_refl
                         | false => fun pf => tt
                       end eq_refl
                     | None => tt
                   end
               end
  }.
  abstract (rewrite rel_dec_correct in pf;
            destruct (type_apply_length_equal ts ftype0 _ nil fd (eq_sym pf));
            match type of H with
              | ?X = _ =>
                match type of pf' with
                  | ?Y = _ =>
                    change Y with X in pf' ; congruence
                end
            end).
  Defined.

  Definition from_list {T} (ls : list T) : PositiveMap.t T :=
    (fix from_list ls : positive -> PositiveMap.t T :=
       match ls with
         | nil => fun _ => PositiveMap.empty _
         | l :: ls => fun p =>
                        PositiveMap.add p l (from_list ls (Pos.succ p))
       end) ls 1%positive.

End RSym.