Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Export McExamples.Monad.MonadTypes.
Require Import McExamples.Monad.MonadSym.

Set Implicit Arguments.
Set Strict Implicit.

Definition mext : Type := (SymEnv.func + mfunc)%type.

Definition mexpr := expr typ mext.

Section mext.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable tys : types.
  Variable fs : functions (RType_typ m tys).

  Instance RSym_mext : @RSym _ (RType_typ m tys) mext.
  apply RSym_sum.
  eapply SymEnv.RSym_func. apply fs.
  apply RSym_mfunc. assumption.
  Defined.

  Definition exprD (us vs : @EnvI.env _ (RType_typ m tys)) (t : typ) (e : mexpr)
  : option (typD m tys t) :=
    let (tus,us) := EnvI.split_env us in
    let (tvs,vs) := EnvI.split_env vs in
    match @exprD' typ mext
                  (RType_typ _ _) _ RSym_mext
                  tus tvs t e
    with
      | None => None
      | Some val => Some (val us vs)
    end.

End mext.
