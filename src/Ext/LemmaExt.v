Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section with_expr.
  Variable ts : types.
  Variable fs : functions ts.
  Variable conclusion : Type.
  Variable conclusionD : env (typD ts) -> forall vs : list typ,
                                            conclusion ->
                                            option (hlist (typD ts nil) vs -> Prop).

  Record lemma : Type :=
  { vars : list typ
  ; premises : list expr
  ; concl : conclusion
  }.

  Global Instance Injective_lemma a b c d e f
  : Injective ({| vars := a ; premises := b ; concl := c |} =
               {| vars := d ; premises := e ; concl := f |}) :=
  { result := a = d /\ b = e /\ c = f }.
  Proof. abstract (inversion 1; auto). Defined.

  Fixpoint foralls (ls : list typ) : (hlist (typD ts nil) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (typD ts nil) ls -> Prop) -> Prop with
      | nil => fun P => P Hnil
      | l :: ls => fun P => forall x : typD ts nil l,
                              foralls (fun z => P (Hcons x z))
    end.

  Fixpoint impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> impls ls P
    end.

  Definition lemmaD (us vs : env (typD ts)) (l : lemma) : Prop :=
    let (tvs,vs) := split_env vs in
    match mapT (fun e =>
                  ExprD.exprD' fs us (l.(vars) ++ tvs) e tvProp) l.(premises)
        , conclusionD us (l.(vars) ++ tvs) l.(concl)
    with
      | Some prems , Some concl =>
        @foralls l.(vars) (fun h =>
          let h := hlist_app h vs in
          List.fold_right
            (fun (x : hlist (typD ts nil) (l.(vars) ++ tvs) -> Prop) (y : Prop) =>
               (x h) -> y)
            (concl h)
            prems)

      | _ , _ => False
    end.

End with_expr.

Section demo.
  Notation funcForall := 1%positive.
  Notation funcImpl := 2%positive.

  Local Notation "'FORALL' t , x" :=
    (App (Func funcForall (t :: nil)) (Abs t x)) (at level 60).
  Local Notation "x ==> y" :=
    (App (App (Func funcImpl nil) x) y) (at level 50).


  Let lem_x_impl_x : @lemma expr :=
  {| vars := tvProp :: nil
   ; premises := Var 0 :: nil
   ; concl := Var 0
  |}.

  Let Plus x y := App (App (Func 1%positive nil) x) y.

  Let lem_plus_comm : @lemma expr :=
  {| vars := tvType 0 :: tvType 0 :: nil
   ; premises := nil
   ; concl := Equal (tvType 0)
                    (Plus (Var 0) (Var 1))
                    (Plus (Var 1) (Var 0))
  |}.

  Let lem_mp : @lemma expr :=
  {| vars := tvProp :: tvProp :: nil
   ; premises := Var 0 :: (Var 0 ==> Var 1) :: nil
   ; concl := Var 1
  |}.

  Let t_nat : type :=
    {| Impl := nat
     ; Eqb := fun _ _ => None
     ; Eqb_correct := fun _ _ => I
     |}.

  Let ts : types := t_nat :: nil.

  Let f_plus : function ts :=
    @F ts 0 (tvArr (tvType 0) (tvArr (tvType 0) (tvType 0)))
       plus.

  Let fs : functions ts := from_list (f_plus :: nil).

  Goal @lemmaD ts fs expr
       (fun us vs e =>
          @ExprD.exprD' ts fs us vs e tvProp) nil nil lem_plus_comm.
  Proof.
    unfold lemmaD; simpl; clear. eapply Plus.plus_comm.
  Qed.

End demo.