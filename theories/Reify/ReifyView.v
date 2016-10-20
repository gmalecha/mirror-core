Require Import Coq.Lists.List.

Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Data.SumN.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.View.


Section ReifyType.
  Universe U.

  Context {typ : Type@{U}} {RType_typ : RType typ}.
  Context {Typ2_typ : Typ2 _ Fun}.

  Let tyArr : typ -> typ -> typ := @typ2 typ RType_typ Fun Typ2_typ.

  Definition reify_typ (rt : list (Command typ)) : Command typ :=
    CFix (CFirst_
            ((CPattern (@RImpl (RGet 0 RIgnore) (RGet 1 RIgnore))
                       (RDo (RCmd (CRec 0))
                            (RDo (RCmd (CRec 0))
                                 (RRet (fun a b => tyArr a b))))) :: rt)).

  Instance Reify_typ (rt : list (Command typ)) : Reify typ := {
    reify_scheme := reify_typ rt
  }.

End ReifyType.

Arguments reify_typ _ {_ _} _.
Arguments Reify_typ _ {_ _} _.

Require Import MirrorCore.syms.SymEnv.

Section ReifyFunc.
  Universe U V.

  Polymorphic Context {typ : Type@{U}} {func : Type@{V}}.
  Polymorphic Context {rt : Reify typ}.
  Polymorphic Context {PV : PartialView func (SymEnv.func)}.

  Polymorphic Definition term_table := a_typed_table BinNums.positive typ.

  Polymorphic Let Ext (x : SymEnv.func) := @ExprCore.Inj typ func (f_insert x).

  Polymorphic Definition reify_func (rf : list (Command (expr typ func)))
  : Command (expr typ func) :=
    CFix
      (CFirst_
        (rf ++
       ((CVar (@ExprCore.Var typ func)) ::
        (CApp (CRec 0) (CRec 0) (@ExprCore.App typ func)) ::
	(CAbs (CCall (reify_scheme typ)) (CRec 0) (@ExprCore.Abs typ func)) ::
	(CMap Ext (CTypedTable (reify_scheme typ) term_table))::nil))).

  Polymorphic Instance Reify_func (rf : list (Command (expr typ func))) : Reify (expr typ func) := {
    reify_scheme := reify_func rf
  }.

End ReifyFunc.

Arguments reify_func _ _ {_ _} _.
Arguments Reify_func _ _ {_ _} _.
