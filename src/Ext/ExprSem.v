Require Import RelationClasses.
Require Import Morphisms Relations.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section sem.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Definition Sem_equiv (t : typ) (R : relation (typD ts nil t))
  : relation (expr sym) :=
    fun x y =>
      forall us tvs,
        match exprD' us tvs x t , exprD' us tvs y t with
          | None , None => True
          | Some l , Some r => forall vs,
                                 R (l vs) (r vs)
          | _ , _ => False
        end.

  Local Instance Reflexive_Sem_equiv t Rt (Refl_Rt : Reflexive Rt)
  : Reflexive (Sem_equiv t Rt).
  Proof.
    red. red; intros. destruct (exprD' us tvs x t); auto.
  Qed.

  Local Instance Symmetric_Sem_equiv t Rt (Refl_Rt : Symmetric Rt)
  : Symmetric (Sem_equiv t Rt).
  Proof.
    red. unfold Sem_equiv. intros.
    specialize (H us tvs).
    destruct (exprD' us tvs x t);
    destruct (exprD' us tvs y t); intuition.
  Qed.

  Local Instance Transitive_Sem_equiv t Rt (Refl_Rt : Transitive Rt)
  : Transitive (Sem_equiv t Rt).
  Proof.
    red. unfold Sem_equiv; red; intros.
    specialize (H us tvs). specialize (H0 us tvs).
    destruct (exprD' us tvs x t);
      destruct (exprD' us tvs y t);
      destruct (exprD' us tvs z t); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_ext (t : typ) (P : typD ts nil t -> Prop) (Q : Prop)
  : expr sym -> Prop :=
    fun e =>
      forall us tvs,
        match exprD' us tvs e t with
          | Some val =>
            forall vs, P (val vs)
          | None => Q
        end.

(**
  Definition Sem_respectful
  : forall t u
           (Rt : relation (typD ts nil t))
           (Ru : relation (typD ts nil u)) e,
      (forall us vs val,
         exprD us vs e (tyArr t u) = Some val ->
         Proper (Rt ==> Ru)%signature val) ->
      Proper (Sem_equiv _ Rt ==> Sem_equiv _ Ru) (App e).
**)
End sem.