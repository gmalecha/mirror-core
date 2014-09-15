Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.Continuation.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SU : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify :
    tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Let eapplicable :=
    @eapplicable typ _ expr _ subst vars_to_uvars
                 exprUnify.

  Section fm2.
    Variable T U V : Type.
    Variable f : T -> U -> option V.
    Fixpoint filter_map2 (ls : list T) (ls' : list U) : option (list V) :=
      match ls , ls' with
        | nil , nil => Some nil
        | l :: ls , l' :: ls' =>
          match f l l' with
            | None => filter_map2 ls ls'
            | Some x => match filter_map2 ls ls' with
                          | None => None
                          | Some xs => Some (x :: xs)
                        end
          end
        | _ , _ => None
      end.
  End fm2.

  Fixpoint all_success (f : expr -> subst -> option (Goal typ expr subst))
           (sub : _) (ls : list expr)
  : option (Goal typ expr subst) :=
    match ls with
      | nil => Some (GGoal sub None)
      | l :: ls =>
        match f l sub with
          | None => None
          | Some (GGoal sub' None) => all_success f sub' ls
          | Some x =>
            match ls with
              | nil => Some x
              | _ :: _ => None
            end
        end
    end.

  Definition APPLY
             (lem : Lemma.lemma typ expr expr)
             (tacC : rtac_cont typ expr subst)
  : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun gl =>
      let '(ctx,sub,goal) := openGoal gl in
      match goal with
        | None => Some gl
        | Some goal =>
          let '(tus,tvs) := getEnvs ctx in
          match eapplicable sub tus tvs lem goal with
            | None => None
            | Some sub' =>
              let len_uvars := length tus in
              match pull (expr := expr) (SU := SU) len_uvars len_vars sub' with
                | Some sub'' =>
                  let premises :=
                      map (fun e => instantiate (fun u => lookup u sub') 0
                                                (vars_to_uvars 0 len_uvars e))
                          lem.(premises)
                  in
                  (** Solve the side conditions **)
                  tacC ctx sub premises
                | None => None
              end
          end
      end.

End parameterized.
