Require Import Coq.Relations.Relations.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section sem.
  Variable typ : Set.
  Variable RType_typ : RType typ.
  Variable expr : Set.
  Variable Expr_expr : Expr _ expr.

  Definition Sem_equiv' (t : typ) (R : relation (typD t))
             (tus tvs : tenv typ)
  : relation expr :=
    fun x y =>
      match exprD tus tvs t x , exprD tus tvs t y with
      | None , None => True
      | Some l , Some r =>
        forall us vs, R (l us vs) (r us vs)
      | _ , _ => False
      end.

  Instance Reflexive_Sem_equiv' t Rt (Refl_Rt : Reflexive Rt) tus tvs
  : Reflexive (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. red; intros. destruct (exprD tus tvs t x); auto.
  Qed.

  Instance Symmetric_Sem_equiv' t Rt (Refl_Rt : Symmetric Rt) tus tvs
  : Symmetric (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'. intros.
    destruct (exprD tus tvs t x);
    destruct (exprD tus tvs t y); intuition.
  Qed.

  Instance Transitive_Sem_equiv' t Rt (Refl_Rt : Transitive Rt) tus tvs
  : Transitive (@Sem_equiv' t Rt tus tvs).
  Proof.
    red. unfold Sem_equiv'; simpl; intros.
    destruct (exprD tus tvs t x);
      destruct (exprD tus tvs t y);
      destruct (exprD tus tvs t z); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_equiv (t : typ) (R : relation (typD t)) (us vs : env)
  : relation expr :=
    fun x y =>
      match env_exprD us vs t x , env_exprD us vs t y with
      | None , None => True
      | Some l , Some r => R l r
      | _ , _ => False
      end.

  Instance Reflexive_Sem_equiv t Rt (Refl_Rt : Reflexive Rt) us vs
  : Reflexive (@Sem_equiv t Rt us vs).
  Proof.
    red. red; intros.
    destruct (env_exprD us vs t x); auto.
  Qed.

  Instance Symmetric_Sem_equiv t Rt (Refl_Rt : Symmetric Rt) us vs
  : Symmetric (@Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv. intros.
    destruct (env_exprD us vs t x);
    destruct (env_exprD us vs t y); intuition.
  Qed.

  Instance Transitive_Sem_equiv t Rt (Refl_Rt : Transitive Rt) us vs
  : Transitive (@Sem_equiv t Rt us vs).
  Proof.
    red. unfold Sem_equiv.
    intros.
    destruct (env_exprD us vs t x);
      destruct (env_exprD us vs t y);
      destruct (env_exprD us vs t z); auto.
    { intros. etransitivity. eapply H. eauto. }
    { intuition. }
  Qed.

  Definition Sem_ext (t : typ) (P : typD t -> Prop) (Q : Prop) us vs
  : expr -> Prop :=
    fun e =>
      match env_exprD us vs t e with
        | Some val => P val
        | None => Q
      end.

  Definition Sem_ext' (t : typ) (P : typD t -> Prop) (Q : Prop) tus tvs
  : expr -> Prop :=
    fun e =>
        match exprD tus tvs t e with
          | Some val =>
            forall us vs, P (val us vs)
          | None => Q
        end.

End sem.
