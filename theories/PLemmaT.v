Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.PolymorphicF.

Section PolyLemma.
  Context {kind : Set}.
  Variable Kstar : kind.
  Variable typ : kind -> Set.

  Context {expr conclusion : Set}.

  Record PolyLemma :=
  { p_n : list kind
  ; p_lem : polymorphic typ p_n (lemma (typ Kstar) expr conclusion)
  ; p_tc : polymorphic typ p_n bool
  }.

  Context {RType_typ : RType (typ Kstar)}.
  Context {Expr_expr : Expr _ expr}.

  Context {Typ0_Prop : Typ0 RType_typ Prop}.

  Variable conclusionD : forall us vs, conclusion -> option (exprT us vs Prop).

  Definition with_typeclasses {T : Type} (TD : T -> Prop) {n}
             (tc : polymorphic typ n bool) (pc : polymorphic typ n T)
  : polymorphic typ n Prop :=
    make_polymorphic (fun args =>
                        if inst tc args
                        then TD (inst pc args)
                        else True).

  Definition PolyLemmaD plem :=
    polymorphicD (fun x => x)
                 (with_typeclasses (lemmaD conclusionD nil nil)
                                   (p_tc plem)
                                   (p_lem plem)).

End PolyLemma.

Arguments p_n {_ _ _ _ _} _.
Arguments p_lem {_ _ _ _ _} _.
Arguments p_tc {_ _ _ _ _} _.
Arguments PolyLemmaD {kind Kstar typ expr conclusion _ _ _} _ _.