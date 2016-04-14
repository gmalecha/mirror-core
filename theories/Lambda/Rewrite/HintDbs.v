Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.ExprSubstitute.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Rewrite.Core.
Require Import MirrorCore.Lambda.Polymorphic.
Require Import MirrorCore.Lambda.PolyInst.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.MTypes.MTypeUnify.
Require Import MirrorCore.Lib.TypeVar.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {tsym : nat -> Type}.
  Let typ := mtyp tsym.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (* TODO(gmalecha): Wrap all of this up in a type class?
   * Why should it be different than Expr?
   *)
  Variable Rbase : Type.
  Variable Rbase_eq : Rbase -> Rbase -> bool.
  Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

  Local Notation "'R'" := (R typ Rbase).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  Inductive HintRewrite : Type :=
  | PRw : forall n,
      polymorphic typ n (rw_lemma typ func Rbase) ->
      rtacK typ (expr typ func) ->
      HintRewrite
  | Rw : rw_lemma typ func Rbase -> rtacK typ (expr typ func) ->
         HintRewrite.

  Definition RewriteHintDb : Type :=
    list HintRewrite.

  Context {PV_vtype : PartialView (tsym 0) (VType 0)}.

  Local Definition view_update :=
    (mtype_unify tsym (FMapPositive.pmap typ)
                 (fun a b c => Some (FMapPositive.pmap_insert a b c))).

  Let local_view : PartialView typ (VType 0) :=
    PartialView_trans TypeView_sym0 PV_vtype.
  Local Existing Instance local_view.

  Local Definition get_lemma {n : nat}
        (p : polymorphic typ n (rw_lemma typ func Rbase))
        (e : expr typ func)
  : option (rw_lemma typ func Rbase) :=
    match get_inst view_update (fmap (fun x => x.(concl).(lhs)) p) e with
    | None => None
    | Some args => Some (inst p args)
    end.

  Fixpoint CompileHints (hints : RewriteHintDb)
           (e : expr typ func)
           (r : R)
  : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)) :=
    match hints with
    | nil => nil
    | Rw lem tac :: hints =>
      (lem, tac) :: CompileHints hints e r
    | PRw n plem tac :: hints =>
      match get_lemma plem e with
      | None => CompileHints hints e r
      | Some lem => (lem, tac) :: CompileHints hints e r
      end
    end.

End setoid.
