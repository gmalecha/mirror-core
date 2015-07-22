Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadTrans.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.RTac.Ctx.

Set Implicit Arguments.
Set Strict Implicit.

Section with_instantiation.
  Variable typ expr : Type.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Definition InContext (ctx : Ctx typ expr) (T : Type) : Type :=
    ctx_subst ctx -> m (ctx_subst ctx * T).


  Global Instance Monad_InContext ctx : Monad (InContext ctx) :=
  { bind := fun _T _U c k ctx =>
      bind (c ctx)
           (fun ctx_r => let '(ctx',r') := ctx_r in
                         k r' ctx')
  ; ret := fun _T v ctx => ret (ctx, v) }.

  Global Instance MonadT_InContext ctx : MonadT (InContext ctx) m :=
  { lift := fun _T x ctx => bind x (fun x => ret (ctx, x)) }.


  Definition assume {T} (m : option T) (k : T -> Prop) : Prop :=
    match m with
    | None => True
    | Some x => k x
    end.

  Definition assert {T} (m : option T) (k : T -> Prop) : Prop :=
    match m with
    | None => False
    | Some x => k x
    end.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.

  Definition env_of_Ctx (c : Ctx typ expr) : Type :=
    hlist typD (getUVars c) * hlist typD (getVars c).

  Definition env_of_exprT {T} c (e : exprT (getUVars c) (getVars c) T)
             (env : env_of_Ctx c) : T :=
    e (fst env) (snd env).

  Definition exprT_of_env {T} c (env : env_of_Ctx c -> T)
  : exprT (getUVars c) (getVars c) T :=
    fun us vs => env (us,vs).

  SearchAbout ctx_subst.

  Let WFi := @WellFormed_ctx_subst typ expr _ _.

  Require Import Morphisms.

  Class MonadLogic : Type :=
  { MLogic : Type := Prop
  ; Mentails : MLogic -> MLogic -> Prop := fun x y => x -> y (** This should be a charge logic **)
  ; ltrue : MLogic := True
  ; limpl : MLogic -> MLogic -> MLogic := fun x y => x -> y
  ; Pred : forall {T}, (T -> MLogic) -> m T -> Prop
  ; Pred_ret : forall T (x : T) (P : T -> MLogic), Mentails ltrue (P x) -> Pred P (Monad.ret x)
  ; Pred_bind : forall T U (c : m T) (k : T -> m U) (P : T -> MLogic) (Pu : U -> MLogic),
      Pred P c ->
      (forall x, Pred (fun y => limpl (P x) (Pu y)) (k x)) ->
      Pred Pu (Monad.bind c k)
  ; Proper_Pred : forall {T}, Proper ((pointwise_relation _ Mentails) ==> eq ==> Basics.impl)%signature (@Pred T)
  }.

  Variable (ML : MonadLogic).

  Definition InContext_spec
             {T}
             (K : Prop)
             (WFg : T -> Prop)
             (c : Ctx typ expr)
             (TD : T -> option (env_of_Ctx c -> Prop))
             (t : InContext c T) : Prop :=
    forall (i : ctx_subst c),
      Pred (fun i_g => let '(i',g') := i_g in
                        K -> WFi i -> WFg g' /\ WFi i' /\
                        assume (pctxD i) (fun C =>
                        assert (pctxD i') (fun I' =>
                        assert (TD g') (fun G' =>
                                          SubstMorphism i i' /\
                                          forall us vs,
                                            I' (exprT_of_env G') us vs))))
            (t i).

  Require Import ExtLib.Tactics.

  Lemma InContext_spec_ret
  : forall ctx {T} (val : T)
           (wfGoal : _ -> Prop) (goalD : T -> option (env_of_Ctx ctx -> Prop)),
      (forall i cD,
          pctxD (ctx:=ctx) i = Some cD ->
          wfGoal val /\
          exists gD,
            goalD val = Some gD /\
            forall us vs, cD (fun us vs => gD (us, vs)) us vs) ->
      InContext_spec (c:=ctx) (wfGoal val) wfGoal goalD (Monad.ret val).
  Proof.
    simpl. intros. red. intros.
    specialize (H i).
    destruct (pctxD i) eqn:Heq.
    { simpl.
      eapply Pred_ret.
      red. intros.
      specialize (H _ eq_refl).
      forward_reason.
      split; auto. split; eauto.
      rewrite Heq. simpl.
      rewrite H3. simpl. split; eauto. reflexivity. }
    { simpl. eapply Pred_ret. red. tauto. }
  Qed.

  Lemma InContext_spec_bind
  : forall ctx {T U} (K : Prop)
           (wfGoalT : _ -> Prop) (goalDT : T -> option (env_of_Ctx ctx -> Prop))
           (wfGoalU : _ -> Prop) (goalDU : U -> option (env_of_Ctx ctx -> Prop))
           (c : InContext ctx T) (k : T -> InContext ctx U),
      InContext_spec (c:=ctx) K wfGoalT goalDT c ->
      (forall x,
          InContext_spec (c:=ctx) (K /\ wfGoalT x)
                         wfGoalU
                         (fun y => match goalDU y with
                                   | None => None
                                   | Some Q =>
                                     Some (fun e => wfGoalT x ->
                                                    forall P,
                                                      goalDT x = Some P ->
                                                      P e -> Q e)
                                   end) (k x)) ->
      InContext_spec (c:=ctx) K wfGoalU goalDU (Monad.bind c k).
  Proof.
    simpl. intros. red. intros.
    specialize (H i).
    simpl in *.
    eapply Pred_bind.
    { eapply H. }
    { simpl. destruct x. clear H.
      specialize (H0 t c0).
      revert H0.
      eapply Proper_Pred; [ | reflexivity ].
      { red. intros.
        destruct a. red. unfold limpl. intros.
        forward_reason.
        split; auto. split; auto.
        destruct (pctxD i) eqn:Heq; simpl in *; auto.
        destruct (pctxD c0) eqn:Heq'; simpl in *; try contradiction.
        destruct (pctxD c1) eqn:Heq''; simpl in *; try contradiction.
        destruct (goalDT t); simpl in *; try contradiction.
        destruct (goalDU u); simpl in *; try contradiction.
        forward_reason.
        split.
        { etransitivity; eauto. }
        { intros.
          specialize (H7 us vs).
          specialize (H8 us vs).
          gather_facts.
          eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
          gather_facts.
          eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
          eapply Pure_pctxD; eauto.
          unfold exprT_of_env.
          intros.
          forward_reason.
          specialize (H8 _ eq_refl).
          tauto. } } }
  Qed.

  Lemma Proper_InContext_spec
  : forall T ctx,
      Proper (Basics.impl -->
              pointwise_relation _ Basics.impl ==>
              pointwise_relation _ (Option.Roption (pointwise_relation _ Basics.impl)) ==>
              eq ==>
              Basics.impl)
             (fun A B => @InContext_spec T A B ctx).
  Proof.
    intros.
    unfold Basics.impl.
    red. red. red. red. red.
    unfold InContext_spec.
    intros. subst.
    specialize (H3 i).
    revert H3.
    eapply Proper_Pred; [ | reflexivity ].
    red. intros.
    red. destruct a.
    intros. red in H.
    forward_reason.
    split; eauto.
    split; eauto.
    destruct (pctxD i) eqn:Heq; simpl; auto.
    simpl in H6.
    destruct (pctxD c) eqn:Heq'; simpl in *; try contradiction.
    unfold assert in *.
    red in H0. specialize (H1 t).
    destruct H1; auto.
    forward_reason.
    split; eauto.
    intros.
    specialize (H7 us vs).
    gather_facts.
    eapply Pure_pctxD; eauto.
    intros.
    eapply H1. eapply H7.
  Qed.

  (** Probably do not want to expose this *)
  Definition getInst ctx : InContext ctx (ctx_subst ctx) :=
    fun ctx => ret (ctx, ctx).

  Definition setInst ctx (s : ctx_subst ctx) : InContext ctx unit :=
    fun _ => ret (s, tt).

  (** TODO: How do you update the instantiation? *)
  Definition underVar {T} ctx (tv : typ) (c : InContext (CAll ctx tv) T)
  : InContext ctx T :=
    fun s =>
      bind (c (AllSubst s))
           (fun sr => let '(s,r) := sr in
                      ret (fromAll s, r)).
(*
  Definition underUVars {T} (tus : list (typ * option expr)) (c : InContext T)
  : InContext T.
  Admitted.

  Variable uvar : Type.

  Definition freshUVar {T} (t : typ) (c : uvar -> InContext T) : InContext T.
  Admitted.
*)

  Definition unify ctx (e1 e2 : expr) (t : typ) : InContext ctx bool.
  Admitted.

End with_instantiation.
