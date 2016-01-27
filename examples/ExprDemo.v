Require Import Coq.PArith.BinPos.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.syms.SymPolyEnv.

(** Demo **)
Section Demo.
  Definition types' : types :=
    list_to_types (@Some Type nat :: @Some Type (list nat) :: nil).

  Definition all (T : Type) (P : T -> Prop) : Prop :=
    forall x, P x.

  Definition typD := typD types'.

  Let tyNat := tyType 1.

  Definition funcs' : functions typD.
  refine (from_list (
          F typD 0
             (tyArr tyNat (tyArr tyNat tyNat))
             plus ::
          F _ 1
             (tyArr (tyArr (tyVar 0) tyProp) tyProp)
             (fun x : Type => @ex x) ::
          F _ 1
             (tyArr (tyArr (tyVar 0) tyProp) tyProp)
             all ::
          F _ 1
             (tyArr (tyVar 0) (tyArr (tyVar 0) tyProp))
             (fun T : Type => @eq T) ::
          F typD 0 (tyType 1) 0 ::
          nil)).
  Defined.

  Definition App_list (f : expr (func typ)) (args : list (expr (func typ)))
  : expr (func typ) :=
    List.fold_left App args f.

  Goal
    let e :=
        @App_list (Inj (FRef 2%positive (tyType 1 :: nil)))
                  ((Abs tyNat (@App_list (Inj (FRef 4%positive (tyType 1 :: nil)))
                                         ((Var 0) :: Inj (FRef 5%positive nil) :: nil))) :: nil)
    in
    let rsym := RSym_func _ funcs' instantiate_typ (@type_apply _) (@type_apply_length_equal _) in
    match exprD (Expr := Expr_expr rsym) nil nil e tyProp with
      | None => False
      | Some p => p
    end.
  Proof.
    simpl. exists 0. reflexivity.
  Qed.

End Demo.
