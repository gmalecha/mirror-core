Require Import BinPos.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.SymEnv.

(** Demo **)
Section Demo.
  Definition types' : types :=
    list_to_types (@Some Type nat :: @Some Type (list nat) :: nil).

  Definition all (T : Type) (P : T -> Prop) : Prop :=
    forall x, P x.

  Definition typD := typD types'.

  Let tyNat := tyType 1.

  Definition funcs' : functions types'.
  refine (from_list (
          F types' 0
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
          F types' 0 (tyType 1) 0 ::
          nil)).
  Defined.

  Definition App_list (f : expr func) (args : list (expr func)) : expr func :=
    List.fold_left App args f.

  Goal
    let e := @App_list (Inj (FRef 2%positive (tyType 1 :: nil)))
                    ((Abs tyNat (@App_list (Inj (FRef 4%positive (tyType 1 :: nil)))
                                                ((Var 0) :: Inj (FRef 5%positive nil) :: nil))) :: nil) in
    match exprD (E := Expr_expr (RSym_func funcs')) nil nil e tyProp with
      | None => False
      | Some p => p
    end.
  Proof.
    simpl. exists 0. reflexivity.
  Qed.
End Demo.
