Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SU : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Let eapplicable :=
    @eapplicable typ _ expr _ subst vars_to_uvars
                 exprUnify.

  Definition EAPPLY
             (lem : Lemma.lemma typ expr expr)
  : rtac typ expr subst :=
    let len_vars := length lem.(vars) in
    fun ctx sub gl =>
      let '(tus,tvs) := getEnvs ctx in
      match eapplicable sub tus tvs lem gl with
        | None => Fail
        | Some sub' =>
          let len_uvars := length tus in
          match pull (expr := expr) len_uvars len_vars sub' with
            | Some sub'' =>
              (** If we have instantiated everything then we can be a little
               ** bit more efficient
               **)
              let premises :=
                  map (fun e => GGoal (instantiate (fun u => lookup u sub') 0
                                                   (vars_to_uvars 0 len_uvars e)))
                      lem.(premises)
              in
              more_list CTop sub'' premises
            | None =>
              let premises := map (fun x => GGoal (vars_to_uvars 0 len_uvars x)) lem.(premises) in
              more_list (fold_right (fun a b => @CEx _ _ b a) ctx lem.(vars)) sub' premises
          (*
              with
                | None => None
                | Solved tus' tvs' sub'' =>
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' => @Solved _ _ _ nil nil sub'''
                  end
                | More tus tvs sub'' hyps'' e =>
                  (** TODO: In this case it is not necessary to pull everything
                   ** I could leave unification variables in place
                   **)
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' =>
                      More (firstn len_uvars tus) tvs sub''' hyps'' e
                  end
              end
           *)
          end
      end.

End parameterized.
