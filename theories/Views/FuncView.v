Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import MirrorCore.Views.Ptrns.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section FuncView.
  Variables func A : Type.

  Class FuncView : Type :=
  { f_insert : A -> func
  ; f_view : func -> option A
  }.

  Variable FV : FuncView.

  Class FuncViewOk : Type :=
  { fv_ok : forall f a, f_view f = Some a <-> f_insert a = f
  }.

  Definition ptrn_view {T} (p : ptrn A T) : ptrn func T :=
    fun e _T good bad =>
      match f_view e with
      | None => bad e
      | Some f => p f _T good (fun _ => bad e)
      end.

  Theorem ptrn_view_ok T (p : ptrn A T) : ptrn_ok p -> ptrn_ok (ptrn_view p).
  Proof.
    unfold ptrn_view, ptrn_ok, Succeeds, Fails.
    intros.
    destruct (f_view x).
    { specialize (H a).
      destruct H.
      { left. destruct H. exists x0.
        setoid_rewrite H. reflexivity. }
      { right. setoid_rewrite H. reflexivity. } }
    { eauto. }
  Qed.

  Variable FVO : FuncViewOk.

  Theorem Succeeds_ptrn_view {T} (p : ptrn A T) x res (H : ptrn_ok p)
  : Succeeds x (ptrn_view p) res ->
    exists f, f_insert f = x /\ Succeeds f p res.
  Proof.
    unfold Succeeds, ptrn_view. intros.
    destruct (f_view x) eqn:Heq.
    { eapply fv_ok in Heq.
      eexists; split; eauto.
      destruct (H a).
      { destruct H1. red in H1. setoid_rewrite H1 in H0.
        setoid_rewrite H1. eauto. }
      { red in H1. setoid_rewrite H1 in H0.
        specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. } }
    { exfalso.
      specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
  Qed.
End FuncView.


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