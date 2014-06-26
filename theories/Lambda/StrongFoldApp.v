Require Import Coq.Arith.Compare_dec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.

Set Implicit Arguments.
Set Strict Implicit.

Definition Lazy T := unit -> T.

Section app_full.
  Variable typ : Type.
  Variable sym : Type.

  Variable T : expr typ sym -> Type. (** The return type **)

  Variable do_var : forall v : var, Lazy (T (Var v)).
  Variable do_uvar : forall u : uvar, Lazy (T (UVar u)).
  Variable do_opaque : forall s : sym, Lazy (T (Inj s)).
  Variable do_app : forall f : expr typ sym, Lazy (T f) ->
    forall args : list { e : expr typ sym & Lazy (T e) },
      (forall y,
         rightTrans (@expr_acc _ _) y (apps f (map (@projT1 _ _) args)) -> T y) ->
      Lazy (T (apps f (map (@projT1 _ _) args))).
  Variable do_abs : forall (t : typ) (e : expr typ sym),
      Lazy (T e) ->
      (forall y, rightTrans (@expr_acc _ _) y (Abs t e) -> T y) ->
      Lazy (T (Abs t e)).

  Fixpoint gather_app (e : expr typ sym) {struct e}
  : forall (E : Lazy (T e))
           (args : list { e : expr typ sym & Lazy (T e) })
           (rec : forall y, rightTrans (@expr_acc _ _) y e -> T y)
           (rec : forall y, rightTrans (@expr_acc _ _) y (apps e (map (@projT1 _ _) args)) -> T y),
      Lazy (T (apps e (map (@projT1 _ _) args))).
    refine
      (match e as e
             return forall (E : Lazy (T e))
                           (args : list { e : expr typ sym & Lazy (T e) })
                           (rec' : forall y, rightTrans (@expr_acc _ _) y e -> T y)
                           (rec : forall y, rightTrans (@expr_acc _ _) y (apps e (map (@projT1 _ _) args)) -> T y),
                      Lazy (T (apps e (map (@projT1 _ _) args)))
       with
         | Var _ => fun E args _ rec => @do_app _ E args rec
         | UVar _ => fun E args _ rec => @do_app _ E args rec
         | Inj _ => fun E args _ rec => @do_app _ E args rec
         | Abs _ _ => fun E args _ rec => @do_app _ E args rec
         | App l r => fun _ args rec rec' =>
           gather_app l
                      (fun z =>
                         @rec l (@RTFin _ _ _ _ (acc_App_l l r)))
                      (@existT _ _ r (fun z => @rec r (@RTFin _ _ _ _ (acc_App_r l r))) :: args)
                      (fun y pf => @rec y (@RTStep _ _ _ _ _ pf (acc_App_l l r)))
                      rec'
       end).
  Defined.

  Definition wffold_app : forall (e : expr typ sym), Lazy (T e).
  refine
    (@Fix _ (rightTrans (@expr_acc _ _)) (Relation.wf_rightTrans (@wf_expr_acc _ _))
          (fun e => Lazy (T e))
          (fun e => 
             match e as e
                   return (forall y, rightTrans (@expr_acc _ _) y e -> Lazy (T y)) -> Lazy (T e)
             with
               | Var v => fun _ => do_var v
               | UVar u => fun _ => do_uvar u
               | Inj f => fun _ => do_opaque f
               | Abs t' e' => fun rec =>
                 @do_abs t' e'
                         (fun z => rec e' (@RTFin _ _ _ _ (acc_Abs _ _)) z)
                         (fun y pf => rec y pf tt)
               | App l r => fun rec =>
                 @gather_app l (fun z => @rec l (@RTFin _ _ _ _ (acc_App_l l r)) tt)
                     (@existT _ _ r (@rec r (@RTFin _ _ _ _ (acc_App_r l r))) :: nil)
                     (fun y pf => @rec y (@RTStep _ _ _ _ _ pf (acc_App_l l r)) tt)
                     (fun y pf => @rec y pf tt)
             end)).
  Defined.

End app_full.

Section with_args.
  Variable typ : Type.
  Variable sym : Type.

  Variable T : expr typ sym -> Type. (** The return type **)

  Unset Elimination Schemes.

  Record AppFullArgs : Type :=
  { do_var : forall v : var, Lazy (T (Var v))
  ; do_uvar : forall u : uvar, Lazy (T (UVar u))
  ; do_opaque : forall s : sym, Lazy (T (Inj s))
  ; do_app : forall f : expr typ sym, Lazy (T f) ->
      forall args : list { e : expr typ sym & Lazy (T e) },
      (forall y, rightTrans (@expr_acc _ _) y (apps f (map (@projT1 _ _) args)) -> T y) ->
      Lazy (T (apps f (map (@projT1 _ _) args)))
  ; do_abs : forall (t : typ) (e : expr typ sym),
               Lazy (T e) ->
               (forall y, rightTrans (@expr_acc _ _) y (Abs t e) -> T y) ->
               Lazy (T (Abs t e))
  }.

  Set Elimination Schemes.

  Definition wf_app_fold_args (args : AppFullArgs) : forall e, Lazy (T e) :=
    match args with
      | {| do_var := do_var
         ; do_uvar := do_uvar
         ; do_opaque := do_opaque
         ; do_app := do_app
         ; do_abs := do_abs |} =>
        @wffold_app typ sym T do_var do_uvar do_opaque do_app do_abs
    end.
End with_args.