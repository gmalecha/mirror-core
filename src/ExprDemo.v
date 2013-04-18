Require Import List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Expr.

(** Demo **)
Section Demo.
  Definition types' : types.
  refine ({| Impl := nat ; Eqb := fun _ _ => None |} :: 
          {| Impl := list nat ; Eqb := fun _ _ => None |} :: nil); auto.
  Defined.

  Definition all (T : Type) (P : T -> Prop) : Prop :=
    forall x, P x.

  Definition funcs' : functions types'.
  refine (@F types' 0
             (tvArr (tvType 0) (tvArr (tvType 0) (tvType 0)))
             plus :: 
          @F types' 1
             (tvArr (tvArr (tvVar 0) tvProp) tvProp) 
             ex :: 
          @F types' 1
             (tvArr (tvArr (tvVar 0) tvProp) tvProp) 
             all :: 
          @F types' 1
             (tvArr (tvVar 0) (tvArr (tvVar 0) tvProp))
             (fun T : Type => @eq T) :: 
          nil).
  Defined.

  Goal
    let e := @App _ (@Func _ 1 (tvType 0 :: nil))
                    ((@Abs _ (tvType 0) (@App _ (@Func _ 3 (tvType 0 :: nil))
                                                ((Var 0) :: @Const types' (tvType 0) 0 :: nil))) :: nil) in
    match @exprD _ funcs' nil nil e tvProp with 
      | None => False
      | Some p => p
    end.
  Proof.
    simpl. exists 0. reflexivity.
  Qed.
End Demo.
