Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
(** TODO(mario): After the fixes below, none of these
 ** imports will be necessary.
 **)
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.

(** Interface for semi-deciders (that use the RelDec typeclass)
**)
Section SemiDec.

  Variable T : Type.
  Variable equ : T -> T -> Prop.
  Variable SD : RelDec equ.

  Class RelDecSemiOk (SD : RelDec equ) : Prop :=
  { semi_dec_ok : forall (x y : T), rel_dec x y = true -> equ x y
  }.

  Section RelDec.

    Variable RD : RelDec equ.
    Variable RDC : RelDec_Correct RD.

    Instance RelDecSemiOk_RelDec : RelDecSemiOk RD :=
    { semi_dec_ok :=
        fun x y => proj1 (@rel_dec_correct T equ RD RDC x y) }.
  End RelDec.
End SemiDec.

(** TODO(mario): This should be moved to SymI.v
 **)
Section SemiDec_RSym.

  (* need to have a typ *)
  Variable typ : Type.
  Variable typ_Rt : RType typ.
  Variable func : Type.
  Variable Rs : @RSym typ typ_Rt func.
  Variable RsOk : RSymOk Rs.

  Instance RelDecSemi_RSym : @RelDec func eq :=
  { rel_dec x y :=
      match @sym_eqb _ _ _ Rs x y with
      | Some b => b
      | _ => false
      end
  }.

  Instance RelDecSemiOk_Rsym : RelDecSemiOk func _ RelDecSemi_RSym.
  Proof.
    destruct RsOk.
    constructor. intros.
    specialize (sym_eqbOk x y).
    unfold rel_dec in H. simpl in H.
    destruct (sym_eqb x y); subst; auto; congruence.
  Qed.
End SemiDec_RSym.

(** TODO(mario): This should be moved to somewhere in Lambda, probably
 ** Lambda/ExprCore.v
 **)
Section SemiDec_expr.

  Variable typ : Type.
  Variable typ_Rt : RType typ.
  Variable typ_RtOk : @RTypeOk typ typ_Rt.
  Variable func : Type.
  Variable func_Rs : @RSym typ typ_Rt func.
  Variable func_RsOk : RSymOk func_Rs.

  (* put SemiDec typeclass in util for now.
     in the longer run,
     Lambda/ExprCore.v should change to use SemiDec *)
  Instance RelDecSemi_expr : RelDec (@eq (expr typ func)) :=
  { rel_dec :=
      expr_eq_dec (@ExprFacts.RelDec_eq_typ typ typ_Rt)
                  (@RelDecSemi_RSym typ typ_Rt func func_Rs)
  }.

  Lemma expr_semi_dec_eq :
    forall x y, expr_eq_dec ExprFacts.RelDec_eq_typ (RelDecSemi_RSym typ _ func func_Rs) x y = true ->
           x = y.
  Proof.
    induction x; destruct y; try solve [intros; simpl in *; congruence].
    { intros. simpl in *.
      apply EqNat.beq_nat_true in H. subst. reflexivity. }
    { intros. simpl in *.
      unfold rel_dec in H. simpl in H.
      eapply sym_eqbOk with (a := f) (b := f0) in func_RsOk.
      destruct (sym_eqb f f0) eqn:Heqb.
      { subst; subst; reflexivity. }
      { congruence. } }
    { simpl.
      specialize (IHx1 y1).
      specialize (IHx2 y2).
      destruct (expr_eq_dec ExprFacts.RelDec_eq_typ
       (RelDecSemi_RSym typ typ_Rt func func_Rs) x1 y1); try congruence.
      intros; f_equal; eauto. }
    { simpl.
      match goal with
      | |- context [ match ?X with true => _ | _ => _ end ] =>
        consider X
      end; intros.
      subst.
      f_equal; eauto. }
    { intros. simpl in *. apply EqNat.beq_nat_true in H. subst. reflexivity. }
  Qed.

  (* put SemiDec inside of theories/Util *)
  (* Do this: make a copy of Lambda that only uses MTypes *)
  Instance SemiDecOk_expr : RelDecSemiOk (expr typ func) _ RelDecSemi_expr.
  Proof.
    constructor. intros.
    unfold rel_dec in H. simpl in H.
    apply expr_semi_dec_eq in H; auto.
  Qed.
End SemiDec_expr.

Lemma RelDec_semidec {T} (rT : T -> T -> Prop)
      (RDT : RelDec rT) (RDOT : RelDec_Correct RDT)
: forall a b : T, a ?[ rT ] b = true -> rT a b.
Proof. intros. consider (a ?[ rT ] b); auto. Qed.
