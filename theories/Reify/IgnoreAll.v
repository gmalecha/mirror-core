Require Import Coq.Lists.List.
Require Import MirrorCore.Reify.ReifyClass.

Definition IgnorePatterns (ls : list RPattern) (T : Set) : Set := T.

Section for_ignore.
  Variable ls : list RPattern.
  Variable T : Set.

  Definition reify_IgnorePatterns {R : Reify T}
  : Command T :=
    let ignores :=
        map (fun p => CPattern (ls:=(T : Type)::nil) p (fun (a : function (CRec 0)) => a)) ls
    in
    CFix (CFirst_ (ignores ++ @reify_scheme _ R :: nil)).

  Global Instance Reify_IgnorePatterns {R : Reify T} : Reify (IgnorePatterns ls T) :=
  { reify_scheme := @reify_IgnorePatterns R }.
End for_ignore.

Arguments reify_IgnorePatterns {_} _ {_}.

Require Import MirrorCore.Reify.Reify.

Local Instance Reify_nat : Reify nat :=
{ reify_scheme := CPattern (ls := nil) RIgnore 0 }.

Goal True.
  pose (<<: True -> False -> nat :>> : IgnorePatterns ((RImpl RIgnore (RGet 0 RIgnore)) :: nil) nat).
  exact I.
Defined.