Require Import List Bool.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.TypesExt.
Require Import MirrorCore.ExprExt.
Require Import MirrorCore.ExprExtDemo.
Require Import MirrorCore.MonadReduceApprox.

Set Implicit Arguments.
Set Strict Implicit.

Module demo.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Context {RTypeOk_typ : RTypeOk RType_typ}.
  Context {typ_arr : TypInstance2 typD Fun}.
  Context {typ_m : TypInstance1 typD m}.
  Context {typ_nat : TypInstance0 typD nat}.

  Definition mr : mexpr typ -> mexpr typ := 
    @monad_run m typ typD (mexpr typ) _ typ_arr typ_m
        (@SApp_bind2 m _ typ typD _ typ_arr typ_m typ_nat)
        (@SApp_ret1 m _ typ typD _ typ_arr typ_m typ_nat) 
        (@gen_app m _ typ typD _ typ_arr typ_m typ_nat)
        (@Lambda_abs m _ _ typD _ typ_arr typ_m typ_nat).

  Time Eval vm_compute in fun t => mr (Bind t t (Ret t (Const _ 3)) (Abs t (Ret t (Plus (Var _ 0) (Var _ 0))))).

End demo.
