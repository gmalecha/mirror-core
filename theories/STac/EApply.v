Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.STac.Core.
Require Import MirrorCore.STac.Continuation.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section apply.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Let eapplicable :=
      @eapplicable typ expr tyProp subst vars_to_uvars
                   exprUnify.

    (** Think of this like:
     **   apply lem ; cont
     ** i.e. first apply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition EAPPLY
               (lem : lemma typ expr expr)
               (tacC : stac_cont typ expr subst)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun tus tvs sub hs e =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let len_uvars := length tus in
          match pull (expr := expr) len_uvars len_vars sub' with
            | Some sub'' =>
              (** If we have instantiated everything then we can be a little
               ** bit more efficient
               **)
              let premises :=
                  map (fun e => instantiate (fun u => lookup u sub') 0
                                            (vars_to_uvars 0 len_uvars e))
                      lem.(premises)
              in
              tacC tus tvs sub'' hs premises
            | None =>
              let premises := map (vars_to_uvars 0 len_uvars) lem.(premises) in
              match
                tacC (tus ++ lem.(vars)) tvs sub' hs premises
              with
                | Fail => @Fail _ _ _
                | Solved tus' tvs' sub'' =>
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' => @Solved _ _ _ nil nil sub'''
                  end
                | More tus tvs sub'' hyps'' e =>
                  (** TODO: In this case it is not necessary to pull everything
                   ** I could leave unification variables in place
                   **)
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' =>
                      More (firstn len_uvars tus) tvs sub''' hyps'' e
                  end
              end
          end
      end.
  End apply.

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.
  Variable UnifySound_exprUnify : unify_sound _ exprUnify.
  Variable NormalizedSubst : NormalizedSubstOk SubstOk_subst.

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

  Hypothesis exprD'_instantiate : exprD'_instantiate _ _ instantiate.

  Hypothesis instantiate_mentionsU : instantiate_mentionsU _ _ instantiate.

  Theorem EAPPLY_sound
  : forall lem tacC,
      @lemmaD typ _ expr _ expr (@propD _ _ _ _ _ ) (@typ0 _ _ _ _)
              (fun P => match typ0_cast nil in _ = T return T
                        with
                          | eq_refl => P
                        end)
              nil nil lem ->
      stac_cont_sound tacC ->
      stac_sound (EAPPLY _ _ lem tacC).
  Admitted.

End parameterized.