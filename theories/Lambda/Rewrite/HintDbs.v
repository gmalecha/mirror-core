(** The implementation of rewriting hint databases
 **)
Require Import ExtLib.Structures.Functor.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Lambda.Polymorphic.
Require Import MirrorCore.Lambda.PolyInst.
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
    | PRw_tc : forall {n : nat},
        polymorphic typ n (rw_lemma typ func Rbase) ->
        polymorphic typ n bool ->
        CoreK.rtacK typ (expr typ func) ->
        HintRewrite.

  (* TODO - change to RewriteDb for consistency? *)
  Definition RewriteHintDb : Type := list HintRewrite.

  (*
  Inductive HintRewrite : Type :=
  | PRw : forall n,
      polymorphic typ n (rw_lemma typ func Rbase) ->
      rtacK typ (expr typ func) ->
      HintRewrite
  | Rw : rw_lemma typ func Rbase -> rtacK typ (expr typ func) ->
         HintRewrite.
   *)

  (* TODO(mario): this is duplicated in Respectful.v. We should find a long-term home for it *)
  (* TODO(mario): convert this so it uses rw_concl instead of rw_lemma? *)
  (* no-op typeclass, used to construct polymorphic types without constraints *)
  Definition tc_any (n : nat) : polymorphic typ n bool :=
    make_polymorphic (fun _ => true).

  Definition with_typeclasses {T : Type} (TD : T -> Prop) {n}
             (tc : polymorphic typ n bool) (pc : polymorphic typ n T)
    : polymorphic typ n Prop :=
    make_polymorphic (fun args =>
                        if inst tc args
                        then TD (inst pc args)
                        else True).

  (* TODO(mario): end duplicated code *)

  (* TODO(mario): implement this, which requires figuring out a suitable
       meaning for rw_lemmaP (the analogue of Proper_conclP) *)
  (*
  Definition RewriteHintOk (hr : HintRewrite) : Prop :=
    match hr with
    | PRw_tc pc tc tac =>
      polymorphicD (fun x => x) (with_typeclasses (rw_lemmaP tac) tc pc)
    end.
   *)


  (** Convenience constructors for building lemmas that do not use
   ** polymorphism.
   **)
  (* not all of these have been updated yet *)
  Definition Rw (rw : rw_lemma typ func Rbase) :=
    @PRw_tc 0 rw true.

  (*
  Theorem Rw_sound (rw : rw_lemma typ func Rbase)
    : Proper_conclP pc ->
      RewriteHintOk (Pr pc).
*)

  (** polymorphic proper hint without typeclass constraints *)
  Definition PRw {n : nat} (pc : polymorphic typ n (rw_lemma typ func Rbase)) :=
    PRw_tc (n:=n) pc (tc_any n).

  (*
  Theorem PRw_sound {n : nat} (pc : polymorphic typ n Proper_concl)
    : polymorphicD Proper_conclP pc ->
      RewriteHintOk (PRw pc).
   *)

  (*
  Theorem PRw_tc_sound {n : nat} (pc : polymorphic typ n Proper_concl) tc
    : polymorphicD (fun x => x) (with_typeclasses Proper_conclP tc pc) ->
      ProperHintOk (PPr_tc pc tc).
  Proof using.
    clear. simpl. tauto.
  Qed.
*)


  Local Definition view_update :=
    (mtype_unify tsym (FMapPositive.pmap typ)
                 (fun a b c => Some (FMapPositive.pmap_insert a b c))).

  Let local_view : PartialView typ (VType 0) :=
  {| f_insert := fun x => match x with
                         | tVar p => tyVar p
                         end
  ; f_view := fun x => match x with
                       | tyVar x => POption.pSome (tVar x)
                       | _ => POption.pNone
                       end |}.
  Local Existing Instance local_view.

  Local Definition get_lemma {n : nat}
        (p : polymorphic typ n (rw_lemma typ func Rbase))
        (e : expr typ func)
    : option (rw_lemma typ func Rbase) :=
    match get_inst _ view_update (fmap (fun x => x.(concl).(lhs)) p) e with
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
