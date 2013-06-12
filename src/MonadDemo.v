Require Import List Bool.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.TypesExt.
Require Import MirrorCore.ExprExt.
Require Import MirrorCore.ExprExtDemo.
Require Import MirrorCore.MonadReduce.

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

  Definition mr : mexpr typ -> mexpr typ := 
    @monad_run m typ typD (mexpr typ) typ_arr typ_m
        (@SApp_bind2 m typ typD typ_arr typ_m)
        (@SApp_ret1 m typ typD typ_m) 
        (@gen_app _ typD typ_arr)
        (@Lambda_abs _).

  Eval compute in fun t => mr (Bind t t (Ret t (Const _ 3)) (Abs t (Ret t (Plus (Var _ 0) (Var _ 0))))).

End demo.
