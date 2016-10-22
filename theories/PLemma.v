Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Polymorphic.

Section PolyLemma.
  Context {typ expr conclusion : Set}.

  Record PolyLemma := {
    p_n : nat;                    
    p_lem : polymorphic typ p_n (lemma typ expr conclusion);
    p_tc : polymorphic typ p_n bool
  }.

End PolyLemma.

Arguments PolyLemma : clear implicits.

Section PolyLemmaD.
  Context {typ expr conclusion : Set}.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.

  Context {Typ0_Prop : Typ0 RType_typ Prop}.
 
  Variable conclusionD : forall us vs, conclusion -> option (exprT us vs Prop).

  Definition with_typeclasses {T : Set} (TD : T -> Prop) {n}
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

End PolyLemmaD.
