Require Import List.
Require Import MirrorCore.Prover.
Require Import MirrorCore.Subst.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable types : Types.types.
  Variable funcs : functions types.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : SubstOk (Expr_expr funcs) Subst_subst.

  Section nested.
    (** n is the number of binders that we have gone under **)
  Variable exprUnify : forall (under : nat) (s : subst) (l r : expr), option subst.

  (** TODO: This algorithm is very weak, in particular it breaks down
   ** because functions are first-class which means that there are multiple
   ** representations of [f x y], e.g.
   **   (((f nil) (a :: nil)) (b :: nil)),
   **   (f (a :: b :: nil))
   **   etc.
   **)
  Fixpoint exprUnify' (n : nat) (s : subst) (e1 e2 : expr) {struct e1}
  : option subst.
  refine (
    match e1 , e2 with
      | UVar u1 , UVar u2 =>
        if EqNat.beq_nat u1 u2 then Some s
        else
          match Subst.set u1 (UVar u2) s with
            | None => Subst.set u2 (UVar u1) s
            | x => x
          end
      | UVar u1 , _ =>
        match Subst.lookup u1 s with
          | None =>
            match lower n n e2 with
              | None => None
              | Some e2 => Subst.set u1 e2 s
            end
          | Some e1' => exprUnify n s e1' e2
        end
      | _ , UVar u2 =>
        match Subst.lookup  u2 s with
          | None =>
            match lower n n e1 with
              | None => None
              | Some e2 => Subst.set u2 e1 s
            end
          | Some e2' => exprUnify n s e1 e2'
        end
      | Var v1 , Var v2 =>
        if EqNat.beq_nat v1 v2 then Some s else None
      | Func f1 ts1 , Func f2 fs2 =>
        if EqNat.beq_nat f1 f2 then Some s else None
      | App e1 es1 , App e2 es2 =>
        (** TODO: This case is not correct, it is drastically simplified by
         ** having a canonical representation of application for example:
         **   [App e1 e2]  rather than [App e es]
         **)
        match exprUnify' n s e1 e2 with
          | None => None
          | Some s' =>
            (fix unifyArgs (s : subst) (es1 es2 : list expr) {struct es1}
             : option subst :=
              match es1 , es2 with
                | nil , nil => Some s
                | e1 :: es1 , e2 :: es2 =>
                  match exprUnify' n s e1 e2 with
                    | None => None
                    | Some s' => unifyArgs s' es1 es2
                  end
                | _ , _ => None
              end) s es1 es2
        end
      | Abs t1 e1 , Abs t2 e2 =>
        (* t1 = t2 since both terms have the same type *)
        exprUnify' (S n) s e1 e2
      | _ , _ => None
    end).
  Defined.
  End nested.

  Fixpoint exprUnify (fuel : nat) (under : nat) (s : subst) (e1 e2 : expr)
  : option subst :=
    match fuel with
      | 0 => None
      | S fuel =>
        exprUnify' (exprUnify fuel) under s e1 e2
    end.

  Require Import ExtLib.Tactics.Consider.
  Require Import ExtLib.Tactics.Injection.

  Definition unify_sound (unify : forall (under : nat) (s : subst) (l r : expr), option subst) : Prop := forall e1 e2 under s s' t u v,
    exprD funcs u v e1 t <> None ->
    exprD funcs u v e2 t <> None ->
    unify under s e1 e2 = Some s' ->
    substD (SubstOk := SubstOk_subst) u v s' ->
       exprD funcs u v e1 t = exprD funcs u v e2 t
    /\ substD (SubstOk := SubstOk_subst) u v s.

  Lemma exprUnify'_sound : forall unify,
                             unify_sound unify ->
                             unify_sound (exprUnify' unify).
  Proof.
    red. induction e1; simpl; intros.
    { destruct e2; try congruence.
      { consider (EqNat.beq_nat v v1); intros; try congruence. subst.
        inv_all; subst. intuition. }
      { admit. } }
    { destruct e2; try congruence.
      { consider (EqNat.beq_nat f f0); try congruence; intros; subst.
        inv_all; subst. split; auto.
        admit. }
      { admit. } }
    { admit. }
    { destruct e2; try congruence.
      { consider (exprUnify' unify under s e1 e2); try congruence; intros.
        { consider (typeof funcs u (map (@projT1 _ _) v) e1); intros.
          specialize (IHe1 e2 under s s0 t0 u v).
          repeat rewrite exprD_App in *.
          repeat match goal with
                   | |- _ => progress (inv_all; subst)
                   | [ _ : not (match ?X with _ => _ end = None) |- _ ] =>
                     (consider X; try congruence); [ intros ]
                 end.

  Admitted.

  Theorem exprUnify_sound : forall fuel, unify_sound (exprUnify fuel).
  Proof.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

  Theorem exprUnify_var : forall fuel under s v e2,
    exprUnify fuel under s (Var v) e2 =
    match e2 with
      | Var v' => None
      | _ => None
    end.
  Abort.

End typed.

(*
  Definition exprUnify : unifier ts.
  red.
  refine (fun Subst Subst_Subst Prover Facts =>
    (** TODO: Use the prover in places where I return [None] **)
    (fix exprUnify (n : nat) : Subst -> expr ts -> expr ts -> option Subst :=
      match n with
        | 0 => fun _ _ _ => None
        | S n =>
          (fix unify s (e1 e2 : expr ts) {struct e1} : option Subst :=
            match e1 , e2 with
              | Const t1 v1 , Const t2 v2 =>
                match const_seqb ts _ t1 t2 v1 v2 with
                  | Some true => Some s
                  | _ => None
                end
              | UVar u1 , UVar u2 =>
                if EqNat.beq_nat u1 u2 then Some s
                else
                  match Subst.set _ _ u1 (UVar u2) s with
                    | None => Subst.set _ _ u2 (UVar u1) s
                    | x => x
                  end
              | UVar u1 , _ =>
                match Subst.lookup _ _ u1 s with
                  | None => Subst.set _ _ u1 e2 s
                  | Some e1' => exprUnify n s e1' e2
                end
              | _ , UVar u2 =>
                match Subst.lookup _ _ u2 s with
                  | None => Subst.set _ _ u2 e1 s
                  | Some e2' => exprUnify n s e1 e2'
                end
              | Var v1 , Var v2 =>
                if EqNat.beq_nat v1 v2 then Some s else None
              | Func f1 ts1 , Func f2 fs2 =>
                if EqNat.beq_nat f1 f2 then Some s else None
              | App e1 es1 , App e2 es2 =>
                match unify s e1 e2 with
                  | None => None
                  | Some s' =>
                    (fix unifyArgs (s : Subst) (es1 es2 : exprs ts) {struct es1} : option Subst :=
                      match es1 , es2 with
                        | nil , nil => Some s
                        | e1 :: es1 , e2 :: es2 =>
                          match unify s e1 e2 with
                            | None => None
                            | Some s' => unifyArgs s' es1 es2
                          end
                        | _ , _ => None
                      end) s es1 es2
                end
              | Abs t1 e1 , Abs t2 e2 =>
                (* t1 = t2 since both terms have the same type *)
                (** TODO: I have to handle the change in binding structure.
                 ** For example,
                 ** (fun x => x) ~ (fun x => ?1) doesn't work
                 ** because the ?1 isn't going to have x in scope
                 **)
                unify s e1 e2
              | _ , _ => None
            end)
      end) 10).
  Defined.

End typed.
*)
