Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.

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
    { compute. intros. subst.
      destruct (Tdec y y); congruence. }
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

(** TODO: Something like this probably already exists. *)
Record TypedValue {T : Type} {RT : RType T} : Type := mkTypedVal
{ tv_type : T
; tv_value : TypesI.typD tv_type }.
Arguments TypedValue _ {_} : clear implicits.
Arguments mkTypedVal {_ _} _ _ : clear implicits.

Section Simple_RSym.
  Context {T} {RT : RType T} {f : Type}
             (fD : f -> option (TypedValue T))
             (fdec : forall a b : f, {a = b} + {a <> b}).
  Definition RSym_simple : RSym f :=
  {| typeof_sym f := match fD f with
                     | Some l => Some l.(tv_type)
                     | None => None
                     end
   ; symD f := match fD f with
               | Some l => l.(tv_value)
               | None => tt
               end
   ; sym_eqb a b := Some match fdec a b with
                         | left _ => true
                         | right _ => false
                         end |}.

  Global Instance RSymOk_simple :  RSymOk RSym_simple.
  Proof. constructor. intros. simpl.
         destruct (fdec a b); auto.
  Qed.
End Simple_RSym.
