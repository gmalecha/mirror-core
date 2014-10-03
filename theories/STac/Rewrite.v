Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.EProverI.
Require Import MirrorCore.ExprProp.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.Util.Iteration.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Is it possible to do this with setoids and morphisms **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Context {RType_typ : RType typ}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  Variable subst : Type.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : SubstOk Subst_subst}.
  Context {SU : SubstUpdate subst expr}.
  Context {SubstUpdateOk : SubstUpdateOk SU _}.

  Let tyProp : typ := @typ0 _ _ _ _.

  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  Record RW :=
  { lem   : lemma typ expr (typ * expr * expr)
  ; side_solver : stac_cont typ expr subst
  }.

  Definition Hints : Type := list RW.

  Let provable (P : typD tyProp) : Prop :=
    match typ0_cast (F:=Prop) in _ = T return T with
      | eq_refl => P
    end.

  Let lemmaD :=
    @lemmaD _ _ _ Expr_expr (typ * expr * expr)
            (fun tus tvs g =>
               let '(t,l,r) := g in
               match @exprD' _ _ _ _ tus tvs l t
                   , @exprD' _ _ _ _ tus tvs r t
               with
                 | Some l , Some r =>
                   Some (fun us vs => l us vs = r us vs)
                 | _ , _ => None
               end)
            tyProp
            provable.

  Let lemmaD' :=
    @lemmaD' _ _ _ Expr_expr (typ * expr * expr)
            (fun tus tvs g =>
               let '(t,l,r) := g in
               match @exprD' _ _ _ _ tus tvs l t
                   , @exprD' _ _ _ _ tus tvs r t
               with
                 | Some l , Some r =>
                   Some (fun us vs => l us vs = r us vs)
                 | _ , _ => None
               end)
            tyProp
            provable.

  Definition HintsOk (h : Hints) : Type :=
    Forall (fun rw => lemmaD nil nil rw.(lem) /\ stac_cont_sound rw.(side_solver)) h.

  Variable hints : Hints.
  Hypothesis hintsOk : HintsOk hints.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Hypothesis exprUnify_sound : unify_sound exprUnify.
  Context {NormlizedSubst : NormalizedSubstOk _}.

  Let eapplicable :=
    @eapplicable typ _ expr Typ0_Prop subst vars_to_uvars exprUnify.

  Section rewrite.
    Variable rw : RW.

    Definition rewrite_here (tus tvs : tenv typ) (t : typ) (hyps : list expr)
               (e : expr) (s : subst) (under : nat)
    : option (expr * subst) :=
      let lem := rw.(lem) in
      let '(lem_t, lem_l, lem_r) := lem.(concl) in
      if t ?[ Rty ] lem_t then (** TODO: This could be ensured outside **)
        let len_tus := length tus in
        let open_leml := vars_to_uvars 0 len_tus lem_l in
        match exprUnify tus tvs under e open_leml t s with
          | None => None
          | Some s' =>
            let new_tus := tus ++ lem.(vars) in
            let len_new_tus := length lem.(vars) in
            let prems := List.map (vars_to_uvars 0 len_tus) lem.(premises) in
            (** check that all of the premises are satisfied **)
            match rw.(side_solver) new_tus tvs s' hyps prems with
              | Solved nil nil s'' =>
                (** pull any new unification variables **)
                match pull len_tus len_new_tus s'' with
                  | None => None
                  | Some s''' =>
                    Some (instantiate (fun u => lookup u s'') under (vars_to_uvars 0 len_tus lem_r), s''')
                end
              | _ => None
            end
        end
      else
        None.
  End rewrite.

  (** I need a fold to actually rewrite **)
  Variable rewriter_fold
  : (tenv typ -> tenv typ -> typ -> expr -> nat -> subst -> option (expr * subst))
    -> tenv typ -> tenv typ -> typ -> expr -> subst -> option (expr * subst).

  Section rewrite_with_all.
    Definition RWs := typ -> list RW.
    Variable rws : RWs.

    Definition rewrite_bottom_up : stac typ expr subst.
      red.
      refine (
      fun tus tvs sub hyps goal =>
        match
          rewriter_fold
            (fun tus' tvs' t e under s =>
               let the_hyps := hyps in
               first_success
                 (fun rw =>
                    rewrite_here rw tus' tvs' t the_hyps e s under)
                 (rws t))
            tus tvs tyProp goal sub
        with
          | None => Fail
          | Some (sub',goal') => More tus tvs goal' hyps sub'
        end).
    Defined.
  End rewrite_with_all.


(*
  Hypothesis vars_to_uvars_sound : forall (tus0 : tenv typ) (e : expr) (tvs0 : list typ)
     (t : typ) (tvs' : list typ)
     (val : hlist (typD nil) tus0 ->
            hlist (typD nil) (tvs0 ++ tvs') -> typD nil t),
   exprD' tus0 (tvs0 ++ tvs') e t = Some val ->
   exists
     val' : hlist (typD nil) (tus0 ++ tvs') ->
            hlist (typD nil) tvs0 -> typD nil t,
     exprD' (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
       t = Some val' /\
     (forall (us : hlist (typD nil) tus0) (vs' : hlist (typD nil) tvs')
        (vs : hlist (typD nil) tvs0),
      val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      eapplicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        lemmaD' nil nil l0 = Some lD ->
        substD tus tvs s = Some sD ->
        exprD' tus tvs g tyProp = Some gD ->
        exists s1D,
          substD (tus ++ l0.(vars)) tvs s1 = Some s1D /\
          forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            exprD (join_env us) (join_env us' ++ join_env vs) l0.(concl) tyProp =
            Some (gD us vs)
            /\ sD us vs.
  Proof.
    intros. unfold eapplicable in H.
    eapply eapplicable_sound with (tyProp := tyProp) in H;
      eauto with typeclass_instances.
    forward_reason. split; eauto.
  Qed.

  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.
*)

End parameterized.
