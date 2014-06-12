Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section sem.
  Variable RType_typ : RType.
  Variable expr : Type.
  Variable Expr_expr : Expr _ expr.

  Definition Sem_equiv' (t : typ) (R : relation (typD nil t))
             (tus tvs : tenv)
  : relation expr :=
    fun x y =>
        match exprD' tus tvs x t , exprD' tus tvs y t with
          | None , None => True
          | Some l , Some r =>
            forall us vs, R (l us vs) (r us vs)
          | _ , _ => False
        end.

  Instance Reflexive_Sem_equiv' t Rt (Refl_Rt : Reflexive Rt) tus tvs
  : Reflexive (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. red; intros. destruct (exprD' tus tvs x t); auto.
  Qed.

  Instance Symmetric_Sem_equiv' t Rt (Refl_Rt : Symmetric Rt) tus tvs
  : Symmetric (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'. intros.
    destruct (exprD' tus tvs x t);
    destruct (exprD' tus tvs y t); intuition.
  Qed.

  Instance Transitive_Sem_equiv' t Rt (Refl_Rt : Transitive Rt) tus tvs
  : Transitive (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'; simpl; intros.
    destruct (exprD' tus tvs x t);
      destruct (exprD' tus tvs y t);
      destruct (exprD' tus tvs z t); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_equiv (t : typ) (R : relation (typD nil t)) (us vs : env)
  : relation expr :=
    fun x y =>
      match exprD us vs x t , exprD us vs y t with
        | None , None => True
        | Some l , Some r => R l r
        | _ , _ => False
      end.

  Instance Reflexive_Sem_equiv t Rt (Refl_Rt : Reflexive Rt) us vs
  : Reflexive (@Sem_equiv t Rt us vs).
  Proof.
    red. red; intros.
    destruct (exprD us vs x t); auto.
  Qed.

  Instance Symmetric_Sem_equiv t Rt (Refl_Rt : Symmetric Rt) us vs
  : Symmetric (@Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv. intros.
    destruct (exprD us vs x t);
    destruct (exprD us vs y t); intuition.
  Qed.

  Instance Transitive_Sem_equiv t Rt (Refl_Rt : Transitive Rt) us vs
  : Transitive (@Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv.
    intros.
    destruct (exprD us vs x t);
      destruct (exprD us vs y t);
      destruct (exprD us vs z t); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_ext (t : typ) (P : typD nil t -> Prop) (Q : Prop) us vs
  : expr -> Prop :=
    fun e =>
      match exprD us vs e t with
        | Some val => P val
        | None => Q
      end.

  Definition Sem_ext' (t : typ) (P : typD nil t -> Prop) (Q : Prop) tus tvs
  : expr -> Prop :=
    fun e =>
        match exprD' tus tvs e t with
          | Some val =>
            forall us vs, P (val us vs)
          | None => Q
        end.

End sem.