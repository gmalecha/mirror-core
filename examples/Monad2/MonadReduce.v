Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.SymEnv.
Require Import McExamples.Monad2.MonadExpr.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "'BIND' [ a ,  b ]" := (ExprCore.Inj (inr (MonadSym.mBind a b))) (at level 20).
Local Notation "'RETURN' [ a ]" := (ExprCore.Inj (inr (MonadSym.mReturn a))) (at level 20).
Local Notation "a @ b" := (ExprCore.App a b) (at level 18, left associativity).

Definition smart_app (a b : mexpr) : mexpr :=
  a @ b.

Definition smart_bind (a b : typ) (c d : mexpr) : mexpr :=
  match d with
    | RETURN [ _ ] => c
    | _ => match c with
             | ExprCore.Abs _ (RETURN [ _ ] @ c) =>
               smart_app d c
             | _ => BIND [ a , b ] @ c @ d
           end
  end.

Lemma bind_smart_bind
: forall a b c d,
    BIND [ a , b ] @ c @ d = smart_bind a b c d.
(** TODO: This is not true, it is only an equivalence! **)
Admitted.

(**
The rules are the following
1) (fun x => f x) = f
2) bind (ret x) f = f x
3) bind x ret = x
4) bind (bind a b) c = bind a (fun x => bind (b x) c)
**)

Fixpoint reduce_arrow (d r : typ) (e : mexpr) {struct e} : mexpr :=
  match e with
    | ExprCore.Abs t (ExprCore.App x (ExprCore.Var 0)) =>
      match lower 0 1 x with
        | None => e
        | Some e => e
      end
    | ExprCore.Abs t e' =>
      match r with
        | tyM m => ExprCore.Abs t (reduce_m m e')
        | _ => e
      end
    | _ => e
  end
with reduce_m (t : typ) (e : mexpr) {struct e} : mexpr :=
  match e with
    | BIND [ _ , _ ] @ e @ RETURN [ _ ] => reduce_m t e
    | BIND [ t' , _ ] @ (RETURN [ _ ] @ e) @ e' =>
      let e' := reduce_arrow t' (tyM t) e' in
      let e := match t' with
                 | tyM z => reduce_m z e
                 | tyArr a b => reduce_arrow a b e
                 | _ => e
               end in
      smart_app e' e
    | BIND [ t' , _ ] @ (BIND [ t'' , _ ] @ a @ b) @ c =>
      let a := reduce_m t'' a in
      let b := reduce_arrow t'' (tyM t') b in
      let c := reduce_arrow t' (tyM t) c in
      smart_bind t' t a (ExprCore.Abs t'' (smart_bind t' t (smart_app b (ExprCore.Var 0)) c))
    | _ => e
  end.

Definition reduce t (e : mexpr) : mexpr :=
  match t with
    | tyM z => reduce_m z e
    | tyArr a b => reduce_arrow a b e
    | _ => e
  end.

(*
Eval compute in reduce (tyM demo.tNat) demo.t1.
Eval compute in reduce (tyM demo.tNat) demo.t2.
Eval compute in reduce (tyM demo.tNat) demo.t3.
*)

Section soundness.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable tys : types.
  Let typD := typD m tys.
  Variable fs : functions typD.

  Let exprD' :=
    @exprD' _ (RType_typ m tys) (Typ2_tyArr m tys) (@RSym_mext m Monad_m tys fs).

  Ltac by_refl :=
    intros;
    match goal with
      | |- match ?X with _ => _ end => destruct X; solve [ auto ]
    end.

  Ltac more_cases :=
    match goal with
      | |- context [ exprD' _ _ _ _ match ?X with _ => _ end ] =>
        destruct X; try by_refl
    end.

  Lemma reduce_m_arr
  : forall tus e tvs,
      (forall tm,
         match exprD' nil tus tvs (tyM tm) e with
           | None => True
           | Some v => match exprD' nil tus tvs (tyM tm) (reduce_m tm e) with
                         | None => False
                         | Some v' => forall us vs, v us vs = v' us vs
                       end
         end) /\
      (forall t t',
         match exprD' nil tus tvs (tyArr t t') e with
           | None => True
           | Some v => match exprD' nil tus tvs (tyArr t t') (reduce_arrow t t' e) with
                         | None => False
                         | Some v' => forall us vs, v us vs = v' us vs
                       end
         end).
  Proof.
    Opaque reduce_m.
    induction e using ExprCore.expr_strong_ind;
    simpl; intros; try solve [ split; by_refl ].
    { Transparent reduce_m.
      split; intros; simpl;
      match goal with
        | |- match ?X with _ => _ end =>
          destruct X; auto
      end.
      Opaque reduce_m. }
    { Transparent reduce_m.
      split; intros; simpl;
      match goal with
        | |- match ?X with _ => _ end =>
          destruct X; auto
      end.
      Opaque reduce_m. }
    { Transparent reduce_m.
      split; intros; simpl;
      match goal with
        | |- match ?X with _ => _ end =>
          destruct X; auto
      end.
      Opaque reduce_m. }
    { admit. }
    { split; auto.
      admit. }
  Qed.

  Theorem reduceOk (me : mexpr)
  : forall us vs t me',
      reduce t me = me' ->
      match @exprD m _ tys fs nil us vs t me with
        | Some val => match @exprD m _ tys fs nil us vs t me' with
                        | Some val' => val = val'
                        | None => False
                      end
        | None => True
      end.
  Admitted.

  Definition Conclusion_reduce_eq us vs t a b : Prop :=
    match @exprD m _ tys fs nil us vs t a
        , @exprD m _ tys fs nil us vs t b
    with
      | Some val , Some val' => val = val'
      | _ , _ => True
    end.

  Definition Premise_reduce_eq us vs t ab : Prop :=
    match @exprD m _ tys fs nil us vs t (fst ab)
          , @exprD m _ tys fs nil us vs t (snd ab)
    with
      | Some val , Some val' => val = val'
      | _ , _ => False
    end.

  Theorem reduce_eq (a b : mexpr)
  : forall us vs t a'_b',
      (reduce t a, reduce t b) = a'_b' ->
      Premise_reduce_eq us vs t a'_b' ->
      Conclusion_reduce_eq us vs t a b.
  Proof.
    red. unfold Premise_reduce_eq.
    intros. forward. subst. simpl in *.
    remember (reduce t b). symmetry in Heqm0.
    remember (reduce t a). symmetry in Heqm1.
    eapply reduceOk with (us := us) (vs := vs) in Heqm0.
    eapply reduceOk with (us := us) (vs := vs) in Heqm1.
    revert Heqm0 Heqm1.
    repeat match goal with
             | H : ?X = _ |- context [ ?Y ] =>
               change Y with X ; rewrite H
           end.
    intros; subst; reflexivity.
  Qed.

End soundness.