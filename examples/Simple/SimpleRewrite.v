Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.STac.STac.
Require Import McExamples.Simple.Simple.

Set Implicit Arguments.
Set Strict Implicit.

Definition E := expr typ func.
Instance RType_typ : RType typ := _.
Instance Expr_E : Expr _ E := Expr_expr.

Definition subst : Type := FMapSubst.SUBST.raw E.
Instance Subst_subst : Subst subst E := FMapSubst.SUBST.Subst_subst _.
Instance SubstUpdate_subst : SubstUpdate subst E := FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).

Notation "a @ b" := (App a b) (at level 30).
Let eq_nat (a b : E) : E := Inj (Eq tyNat) @ a @ b.
Let plus (a b : E) : E := Inj Plus @ a @ b.
Let n (n : nat) : E := Inj (N n).

(* forall n, 0 + n = n *)
Definition RW1 : RW typ E subst :=
{| lem := {| Lemma.vars := tyNat :: nil
           ; Lemma.premises := nil
           ; Lemma.concl := (tyNat, plus (n 0) (Var 0), Var 0) |}
 ; side_solver := use_list nil
 |}.

(* forall n, n + 0 = n *)
Definition RW2 : RW typ E subst :=
{| lem := {| Lemma.vars := tyNat :: nil
           ; Lemma.premises := nil
           ; Lemma.concl := (tyNat, plus (Var 0) (n 0), Var 0) |}
 ; side_solver := use_list nil
 |}.

Definition rewrite (rw : RW typ E subst) tus tvs (t : typ) (e : E) : option E :=
  match
    @rewrite_here typ E _ subst _ _ (@vars_to_uvars typ func)
                  (fun tus tvs u e1 e2 t s =>
                     @ExprUnify_simul.exprUnify subst typ func _ _ _ _ _ 10 nil tus tvs u s e1 e2 t)
                  (@instantiate typ func) rw tus tvs t nil e (@empty _ _ _) 0
  with
    | None => None
    | Some (e',_) => Some e'
  end.

Definition rewrite_top (rw : RW typ E subst) : stac typ E subst :=
  fun tus tvs sub hyps goal =>
    match
      @rewrite_here typ E _ subst _ _ (@vars_to_uvars typ func)
                    (fun tus tvs u e1 e2 t s =>
                       @ExprUnify_simul.exprUnify subst typ func _ _ _ _ _ 10 nil tus tvs u s e1 e2 t)
                    (@instantiate typ func) rw tus tvs tyProp hyps goal sub 0
    with
      | None => Fail
      | Some (g',s') => More nil nil s' hyps g'
    end.

Section above_binders.
  Variable rw : tenv typ -> tenv typ -> typ -> E -> nat -> subst -> option (E * subst).

  (** NOTE: There should still be room to optimize this b/c the option monad is
   ** pretty inefficient
   **)
  Fixpoint bottom_up' (under : nat) (tus tvs : tenv typ)
           (t : typ) (e : E) (s : subst) {struct e}
  : (E * subst) :=
    match e with
      | Var n => match rw tus tvs t e under s with
                   | None => (e,s)
                   | Some x => x
                 end
      | UVar _ => (e,s)
      | Inj _ => match rw tus tvs t e under s with
                   | None => (e,s)
                   | Some x => x
                 end
      | App a b =>
        match bottom_up_simul' under tus tvs a s with
          | None => (e,s)
          | Some (tyArr td t,(a',s')) =>
            let (b',s'') := bottom_up' under tus tvs td b s' in
            match rw tus tvs t (App a' b') under s'' with
              | None => (App a' b', s'')
              | Some x => x
            end
          | _ => (e,s)
        end
      | Abs _ _ => match rw tus tvs t e under s with
                     | None => (e,s)
                     | Some x => x
                   end
    end
  with bottom_up_simul' (under : nat) (tus tvs : tenv typ)
                        (e : E) (s : subst) {struct e}
  : option (typ * (E * subst)) :=
    match e with
      | Var n =>
        match nth_error tvs n with
          | None => None
          | Some t => Some match rw tus tvs t e under s with
                             | None => (t,(e,s))
                             | Some x => (t,x)
                           end
        end
      | UVar n =>
        match nth_error tus n with
          | None => None
          | Some t => Some (t,(e,s))
        end
      | Inj _ =>
        match typeof_expr nil tus tvs e with
          | None => None
          | Some t => Some match rw tus tvs t e under s with
                             | None => (t,(e,s))
                             | Some x => (t,x)
                           end
        end
      | App a b =>
        match bottom_up_simul' under tus tvs a s with
          | None => None
          | Some (tyArr td t,(a',s')) =>
            let (b',s'') := bottom_up' under tus tvs td b s' in
            Some match rw tus tvs t (App a' b') under s'' with
                   | None => (t,(App a' b', s''))
                   | Some x => (t,x)
                 end
          | _ => None
        end
      | Abs _ _ =>
        match typeof_expr nil tus tvs e with
          | None => None
          | Some t =>
            Some match rw tus tvs t e under s with
                   | None => (t,(e,s))
                   | Some x => (t,x)
                 end
        end
    end.
  Definition bottom_up tus tvs t e s :=
    Some (bottom_up' 0 tus tvs t e s).

End above_binders.

Definition autorewrite : RWs typ E subst -> stac typ E subst :=
  @rewrite_bottom_up typ E RType_typ _ subst _ _ (@vars_to_uvars typ func)
                    (fun tus tvs u e1 e2 t s =>
                       @ExprUnify_simul.exprUnify subst typ func _ _ _ _ _ 10 nil tus tvs u s e1 e2 t)
                    (@instantiate typ func)
                    bottom_up.

Let all := fun t => match t with
                      | tyNat => RW1 :: RW2 :: nil
                      | _ => nil
                    end.

(*
Eval vm_compute in
    (rewrite RW1) nil (tyNat :: nil) tyNat (Inj Plus @ Inj (N 0) @ Var 0).
*)

(*
Time Eval vm_compute in
    let goal := eq_nat (plus (n 0) (plus (Var 0) (n 0))) (plus (plus (plus (n 0) (Var 0)) (n 0)) (n 0)) in
    autorewrite all nil (tyNat :: nil) (@empty _ _ _) nil goal.

Eval cbv beta iota zeta delta - [ plus n ] in (big_plus_ignore (Var 0) 2).
*)


Fixpoint big_plus_ignore acc n' : E :=
  match n' with
    | 0 => acc
    | S n' => plus (big_plus_ignore (n 0) n') (plus (big_plus_ignore acc n') (big_plus_ignore (n 0) n'))
  end.


Time Eval vm_compute in
    let goal := eq_nat (big_plus_ignore (Var 0) 10) (big_plus_ignore (Var 0) 10) in
    autorewrite all nil (tyNat :: nil) (@empty _ _ _) nil goal.

Fixpoint big_plus_ignore_sem acc n' : nat :=
  match n' with
    | 0 => acc
    | S n' => (big_plus_ignore_sem 0 n') + ((big_plus_ignore_sem acc n') + (big_plus_ignore_sem 0 n'))
  end.

Create HintDb plus_rw.
Hint Rewrite plus_O_n : plus_rw.
Hint Rewrite <- plus_n_O : plus_rw.

Goal forall x, (big_plus_ignore_sem x 10) = (big_plus_ignore_sem x 10).
  intro.
  Opaque Peano.plus.
  simpl.
  Time autorewrite with plus_rw.
  reflexivity.
Qed.