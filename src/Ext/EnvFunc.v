Require Import BinPos.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.

Set Implicit Arguments.
Set Strict Implicit.

Inductive func : Type :=
| Equal (t : typ)
| Not
| FRef (fi : positive) (ts : list typ).

Section RFunc.
  Variable ts : types.

  Record function := F
  { fenv : nat
  ; ftype : typ
  ; fdenote : parametric fenv nil (fun env => typD ts env ftype)
  }.

  Definition functions := PositiveMap.t function.
  Variable fs : functions.

  Definition func_typeof_func (f : func) : option typ :=
    match f with
      | Equal t => Some (tvArr t (tvArr t tvProp))
      | Not => Some (tvArr tvProp tvProp)
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
  Global Instance RFunc_func : RFunc (typD ts) func :=
  { typeof_func := func_typeof_func
  ; funcD := fun f =>
               match f as f
                     return match func_typeof_func f with
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
End RFunc.