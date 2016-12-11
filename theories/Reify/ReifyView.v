Require Import Coq.Lists.List.

Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Data.SumN.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.View.


Section ReifyType.
  Universe U.

  Context {typ : Set} {RType_typ : RType typ}.
  Context {Typ2_typ : Typ2 _ Fun}.

  Let tyArr : typ -> typ -> typ := @typ2 typ RType_typ Fun Typ2_typ.

  Definition reify_typ (rt : list (Command typ)) : Command typ :=
  (@Patterns.CFix _
      (@Patterns.CFirst_ _
          ((@CPattern _ ((typ : Type) :: (typ : Type) :: nil)
                     (@RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
                     (fun (a b : function (CRec 0)) => tyArr a b)) :: rt))).

  Instance Reify_typ (rt : list (Command typ)) : Reify typ := {
    reify_scheme := reify_typ rt
  }.

End ReifyType.

Arguments reify_typ _ {_ _} _.
Arguments Reify_typ _ {_ _} _.

Require Import MirrorCore.syms.SymEnv.

Section ReifyFunc.
  Universe U V.

  Polymorphic Context {typ : Set} {func : Set}.
  Polymorphic Context {rt : Reify typ}.
  Polymorphic Context {PV : PartialView func (SymEnv.func)}.

  Polymorphic Definition term_table := a_typed_table BinNums.positive typ.

  Polymorphic Let Ext (x : SymEnv.func) := @ExprCore.Inj typ func (f_insert x).

  Polymorphic Definition reify_func (rf : list (Command (expr typ func))) : Command (expr typ func) :=
    @Patterns.CFix (expr typ func)
      (@Patterns.CFirst_ _
        (rf ++
         ((Patterns.CVar (@ExprCore.Var typ func)) ::
          (Patterns.CApp (Patterns.CRec 0) (Patterns.CRec 0) (@ExprCore.App typ func)) ::
	  (Patterns.CAbs (CCall (reify_scheme typ)) (CRec 0) (@ExprCore.Abs typ func)) ::
	  (Patterns.CMap Ext (Patterns.CTypedTable (reify_scheme typ) term_table))::nil))).

  Polymorphic Instance Reify_func (rf : list (Command (expr typ func))) : Reify (expr typ func) := {
    reify_scheme := reify_func rf
  }.

  Polymorphic Definition reify_func' (rf : list (Command (expr typ func))) : Command (expr typ func) :=
    @Patterns.CFix (expr typ func)
      (@Patterns.CFirst_ _
        (rf ++
         ((Patterns.CVar (@ExprCore.Var typ func)) ::
          (Patterns.CApp (Patterns.CRec 0) (Patterns.CRec 0) (@ExprCore.App typ func)) ::
	  (Patterns.CAbs (CCall (reify_scheme typ)) (CRec 0) (@ExprCore.Abs typ func)) :: nil))).

  Polymorphic Instance Reify_func' (rf : list (Command (expr typ func))) : Reify (expr typ func) := {
    reify_scheme := reify_func' rf
  }.

End ReifyFunc.

Arguments reify_func _ _ {_ _} _.
Arguments Reify_func _ _ {_ _} _.

Arguments reify_func' _ _ {_} _.
Arguments Reify_func' _ _ {_} _.
