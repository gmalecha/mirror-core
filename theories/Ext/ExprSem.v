Require Import RelationClasses.
Require Import Morphisms Relations.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section sem.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Definition Sem_equiv' (t : typ) (R : relation (typD ts nil t)) (tus tvs : tenv typ)
  : relation (expr sym) :=
    fun x y =>
      forall us : hlist (typD ts nil) tus,
        match exprD' (join_env us) tvs x t , exprD' (join_env us) tvs y t with
          | None , None => True
          | Some l , Some r => forall vs,
                                 R (l vs) (r vs)
          | _ , _ => False
        end.

  Instance Reflexive_Sem_equiv' t Rt (Refl_Rt : Reflexive Rt) tus tvs
  : Reflexive (Sem_equiv' t Rt tus tvs).
  Proof.
    red. red; intros. destruct (exprD' (join_env us) tvs x t); auto.
  Qed.

  Instance Symmetric_Sem_equiv' t Rt (Refl_Rt : Symmetric Rt) tus tvs
  : Symmetric (Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'. intros.
    specialize (H us).
    destruct (exprD' (join_env us) tvs x t);
    destruct (exprD' (join_env us) tvs y t); intuition.
  Qed.

  Instance Transitive_Sem_equiv' t Rt (Refl_Rt : Transitive Rt) tus tvs
  : Transitive (Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'; red; intros.
    specialize (H us). specialize (H0 us).
    destruct (exprD' (join_env us) tvs x t);
      destruct (exprD' (join_env us) tvs y t);
      destruct (exprD' (join_env us) tvs z t); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_equiv (t : typ) (R : relation (typD ts nil t)) (us vs : env (typD ts))
  : relation (expr sym) :=
    fun x y =>
      match exprD us vs x t , exprD us vs y t with
        | None , None => True
        | Some l , Some r => R l r
        | _ , _ => False
      end.

  Instance Reflexive_Sem_equiv t Rt (Refl_Rt : Reflexive Rt) us vs
  : Reflexive (Sem_equiv t Rt us vs).
  Proof.
    red. red; intros.
    destruct (exprD us vs x t); auto.
  Qed.

  Instance Symmetric_Sem_equiv t Rt (Refl_Rt : Symmetric Rt) us vs
  : Symmetric (Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv. intros.
    destruct (exprD us vs x t);
    destruct (exprD us vs y t); intuition.
  Qed.

  Instance Transitive_Sem_equiv t Rt (Refl_Rt : Transitive Rt) us vs
  : Transitive (Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv.
    intros.
    destruct (exprD us vs x t);
      destruct (exprD us vs y t);
      destruct (exprD us vs z t); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_ext (t : typ) (P : typD ts nil t -> Prop) (Q : Prop) us vs
  : expr sym -> Prop :=
    fun e =>
      match exprD us vs e t with
        | Some val => P val
        | None => Q
      end.

  Definition Sem_ext' (t : typ) (P : typD ts nil t -> Prop) (Q : Prop) tus tvs
  : expr sym -> Prop :=
    fun e =>
      forall us : hlist (typD ts nil) tus,
        match exprD' (join_env us) tvs e t with
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