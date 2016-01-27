Require Import ExtLib.Data.HList.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.CtxLogic.

Section definitions.
  Variables typ expr : Type.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  (** instantiate **)
  Variable instantiate : (uvar -> option expr) -> nat -> expr -> expr.

  Definition sem_preserves_if_ho tus tvs
             (P : exprT tus tvs Prop -> Prop)
             (f : nat -> option expr) : Prop :=
    forall u e t get,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD' tus tvs e t = Some eD /\
        P (fun us vs => get us = eD us vs).

  Definition sem_preserves_if tus tvs
             (P : hlist _ tus -> hlist _ tvs -> Prop)
             (f : nat -> option expr) : Prop :=
    forall u e t get,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      exists eD,
        exprD' tus tvs e t = Some eD /\
        forall us vs,
          P us vs ->
          get us = eD us vs.

(*
  Definition instantiate_mentionsU : Prop :=
    forall f n e u,
      mentionsU u (instantiate f n e) = true <-> (** do i need iff? **)
      (   (f u = None /\ mentionsU u e = true)
       \/ exists u' e',
            f u' = Some e' /\
            mentionsU u' e = true/\
            mentionsU u e' = true).

  Definition exprD'_instantiate : Prop :=
    forall tus tvs f e tvs' t eD P,
      sem_preserves_if tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) t = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).

  Definition sem_instantiate_ho {T TD} (R : TD -> TD -> Prop)
             (exprD' : forall tus tvs, T -> option (exprT tus tvs TD))
             (instantiate : (nat -> option expr) -> nat -> T -> T)
  : Prop :=
    forall tus tvs f e tvs' eD P (App : ExprTApplicative P),
      sem_preserves_if_ho tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f (length tvs') e) = Some eD' /\
        P (fun us vs => forall vs',
                          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs)).
*)

(*
  Goal (forall t : typ, @sem_instantiate_ho expr (typD t) (@eq _)
                                            (fun tus tvs e => exprD' tus tvs e t)
                                            instantiate) ->
  exprD'_instantiate.
  Proof.
    unfold exprD'_instantiate, sem_instantiate_ho.
    intuition.
    specialize (@H t tus tvs f e tvs' eD
                   (fun (P' : exprT tus tvs Prop) => forall us vs,
                                P us vs ->
                                P' us vs)).
    destruct H.
    - clear. constructor; firstorder.
    - red. red in H0. intros.
      eapply H0 in H; eauto.
    - eauto.
    - exists x. intuition.
  Qed.
*)

End definitions.

Arguments sem_preserves_if {typ expr RType Expr} _ _ _ _ : rename.
Arguments sem_preserves_if_ho {typ expr RType Expr} tus tvs C f : rename.
