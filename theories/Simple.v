Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Export MirrorCore.syms.SymSimple.

Set Implicit Arguments.
Set Strict Implicit.

Section SimpleRType_ctor.
  Context {T : Type}.
  Variable TD : T -> Type.
  Variable Tacc : T -> T -> Prop.
  Variable Tdec : forall a b : T, {a = b} + {a <> b}.

  Hypothesis wf_Tacc : well_founded Tacc.

  Definition RType_simple : RType T :=
  {| typD := TD
   ; tyAcc := Tacc
   ; type_cast := fun a b => match Tdec a b with
                             | left pf => Some pf
                             | right _ => None
                             end |}.

  Theorem RTypeOk_simple : @RTypeOk T RType_simple.
  Proof.
    constructor.
    { reflexivity. }
    { eapply wf_Tacc. }
    { compute. destruct pf. reflexivity. }
    { compute. destruct pf1. destruct pf2. reflexivity. }
    { compute. intros. destruct (Tdec x x).
      { eapply Eqdep_dec.K_dec_type with (p := e); eauto. }
      { congruence. } }
    { red. eapply Tdec. }
  Defined.
End SimpleRType_ctor.

Instance RelDec_from_RType {T} (R : RType T) : RelDec (@eq T) | 900 :=
{ rel_dec a b := match type_cast a b with
                 | Some _ => true
                 | None => false
                 end }.


Arguments RTypeOk_simple {_ _ _ _} _.

Ltac prove_simple_acc :=
  try match goal with
      | |- well_founded _ => red
      end ;
  match goal with
  | |- forall x : _ , Acc _ x =>
    induction x; constructor; inversion 1; subst; auto
  end.

Ltac prove_TypOk :=
  constructor;
  try solve [ reflexivity
            | constructor
            | inversion 1; subst; unfold Rty; auto
            | match goal with
              | |- forall x, _ =>
                destruct x; simpl;
                try solve [ eauto
                          | left; repeat first [ exists eq_refl | eexists ];
                            reflexivity ]
              end
            | intros; match goal with
                      | H : Rty _ _ |- _ => destruct H ; reflexivity
                      end
            ].
