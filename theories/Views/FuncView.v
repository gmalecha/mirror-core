Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Class FuncView (func A : Type) := {
  f_insert : A -> func;
  f_view : func -> option A
}.

Class FuncViewOk (func A : Type) (FV : FuncView func A) := {
  fv_ok : forall f a, f_view f = Some a <-> f_insert a = f
}.                                               

Section FuncViewSumN.
  Context {A func : Type}.

  Global Instance FuncViewPMap (p : positive) (m : FMapPositive.pmap Type) 
	 (pf : Some A = pmap_lookup' m p) :
    FuncView (OneOf m) A := 
    {
      f_insert f := Into f p pf;
      f_view f :=
	match f with
	  | Build_OneOf _ p' pf1 =>
	    match Pos.eq_dec p p' with
	      | left Heq =>
	       Some (eq_rect_r (fun o => match o with 
                                           | Some T => T 
                                           | None => Empty_set
                                         end) pf1 
	                       (eq_rect _ (fun p => Some A = pmap_lookup' m p) pf _ Heq))
	      | right _ => None
	    end
	end

    }.

  Global Instance FuncViewOkPMap (p : positive) (m : FMapPositive.pmap Type) 
	 (pf : Some A = pmap_lookup' m p) :
    FuncViewOk (FuncViewPMap p m pf) := _.
  Proof.
    admit.
  Admitted.

End FuncViewSumN.