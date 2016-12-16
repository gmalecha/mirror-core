Require Import MirrorCore.Lemma.
Require Import MirrorCore.Reify.ReifyClass.

Section rlemma_tc.
  Context {ty pr c : Set}.
  Context {rT : Reify ty}.
  Context {rU : Reify pr}.
  Context {rV : Reify c}.

  Definition tc_lemma (ignores : list RPattern) : Set :=
    lemma ty pr c.

  Variable ignores : list RPattern.

  Definition reify_tc_lemma : Command@{Set} (tc_lemma ignores) :=
    Eval unfold CPattern in
    CFix
      (CFirst (   (** Reify type classes, note each one is ignored *)
                  map (fun p =>
                         CPattern (ls:=(lemma ty pr c : Type)::nil)
                           (RPi p (RGet 0 RIgnore))
                           (fun (y : function (CRec 0)) => y))
                      ignores
               ++ (** Reifies premises *)
                  CPattern (ls:=(pr : Type)::(lemma ty pr c : Type)::nil)
                           (RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
                           (fun (x : function (CCall (reify_scheme _)))
                              (y : function (CRec 0)) => add_prem x y)
               :: CPattern (ls:=(ty : Type)::(lemma ty pr c : Type)::nil)
                           (RPi (RGet 0 RIgnore) (RGet 1 RIgnore))
                           (fun (x : function (CCall (reify_scheme _)))
                              (y : function (CRec 0)) => add_var x y)
               :: CMap (fun x => {| vars := nil
                                  ; premises := nil
                                  ; concl := x |}) (reify_scheme _)
               :: nil)).

  Global Instance Reify_tc_lemma : Reify (tc_lemma ignores) :=
  { reify_scheme := CCall reify_tc_lemma }.

End rlemma_tc.

Arguments tc_lemma ty pr c ignores : clear implicits, rename.


Typeclasses Opaque tc_lemma.