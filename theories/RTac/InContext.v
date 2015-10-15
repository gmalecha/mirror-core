Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadTrans.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
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

  Global Instance MonadPlus_InContext ctx {Mp : MonadPlus.MonadPlus m}
  : MonadPlus.MonadPlus (InContext ctx) :=
  { mplus := fun _A _B ml mr ctx =>
               Monad.bind (MonadPlus.mplus (ml ctx) (mr ctx))
                          (fun x =>
                             Monad.ret match x with
                                       | inl (a,b) => (a, inl b)
                                       | inr (a,b) => (a, inr b)
                                       end) }.

  Global Instance MonadZero_InContext ctx {Mz : MonadZero.MonadZero m}
  : MonadZero.MonadZero (InContext ctx) :=
  { mzero := fun _ => lift MonadZero.mzero }.

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
  Variable Expr_expr : Expr typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.

  Definition env_of_Ctx (c : Ctx typ expr) : Type :=
    hlist typD (getUVars c) * hlist typD (getVars c).

  Definition env_of_exprT {T} c (e : exprT (getUVars c) (getVars c) T)
             (env : env_of_Ctx c) : T :=
    e (fst env) (snd env).

  Definition exprT_of_env {T} c (env : env_of_Ctx c -> T)
  : exprT (getUVars c) (getVars c) T :=
    fun us vs => env (us,vs).

  Let WFi := @WellFormed_ctx_subst typ expr _ _.

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

  Variable ML : MonadLogic.

  (** NOTE; This does not quite form a monad logic b/c of the well-formedness
   ** conditions.
   **)
  Definition InContext_spec
             {T}
             (WFg : T -> Prop)
             (c : Ctx typ expr)
             (TD : T -> option (env_of_Ctx c -> Prop))
             (t : InContext c T) : Prop :=
    forall (i : ctx_subst c),
      Pred (fun i_g => let '(i',g') := i_g in
                        WFi i -> WFg g' /\ WFi i' /\
                        assume (pctxD i) (fun C =>
                        assert (pctxD i') (fun I' =>
                        assert (TD g') (fun G' =>
                                          SubstMorphism i i' /\
                                          forall us vs,
                                            I' (exprT_of_env G') us vs))))
            (t i).

  Lemma InContext_spec_ret
  : forall ctx {T} (val : T)
           (wfGoal : _ -> Prop) (goalD : T -> option (env_of_Ctx ctx -> Prop)),
      wfGoal val ->
      (forall i cD,
          pctxD (ctx:=ctx) i = Some cD ->
          wfGoal val /\
          exists gD,
            goalD val = Some gD /\
            forall us vs, cD (fun us vs => gD (us, vs)) us vs) ->
      InContext_spec (c:=ctx) wfGoal goalD (Monad.ret val).
  Proof.
    simpl. intros. red. intros.
    specialize (H0 i).
    destruct (pctxD i) eqn:Heq.
    { simpl.
      eapply Pred_ret.
      red. intros.
      specialize (H0 _ eq_refl).
      forward_reason.
      split; auto. split; eauto.
      rewrite Heq. simpl.
      rewrite H3. simpl. split; eauto. reflexivity. }
    { simpl. eapply Pred_ret. red. tauto. }
  Qed.

  Lemma InContext_spec_bind
  : forall ctx {T U}
           (wfGoalT : _ -> Prop) (goalDT : T -> option (env_of_Ctx ctx -> Prop))
           (wfGoalU : _ -> Prop) (goalDU : U -> option (env_of_Ctx ctx -> Prop))
           (c : InContext ctx T) (k : T -> InContext ctx U),
      InContext_spec (c:=ctx) wfGoalT goalDT c ->
      (forall x,
          InContext_spec (c:=ctx)
                         (fun y => wfGoalT x -> wfGoalU y)
                         (fun y => match goalDT x with
                                   | None => Some (fun _ => True)
                                   | Some P =>
                                     match goalDU y with
                                     | None => None
                                     | Some Q =>
                                       Some (fun e => wfGoalT x -> P e -> Q e)
                                     end
                                   end) (k x)) ->
      InContext_spec (c:=ctx) wfGoalU goalDU (Monad.bind c k).
  Proof.
    simpl. intros. red. intros.
    specialize (H i).
    simpl in *.
    eapply Pred_bind.
    { eapply H; auto. }
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
          gather_facts.
          eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
          gather_facts.
          eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
          eapply Pure_pctxD; eauto.
          unfold exprT_of_env.
          intros.
          forward_reason.
          eassumption. } } }
  Qed.

  (** TODO: Move to ExtLib **)
  Inductive Roption_impl {T} (R : T -> T -> Prop) : option T -> option T -> Prop :=
  | Roption_impl_None : forall x, Roption_impl R None x
  | Roption_impl_Some : forall x y, R x y -> Roption_impl R (Some x) (Some y).

  Lemma Proper_InContext_spec
  : forall T ctx,
      Proper (pointwise_relation _ Basics.impl ==>
              pointwise_relation _ (Roption_impl (pointwise_relation _ Basics.impl)) ==>
              eq ==>
              Basics.impl)
             (fun B => @InContext_spec T B ctx).
  Proof.
    intros.
    unfold Basics.impl.
    red. red. red. red. red.
    unfold InContext_spec.
    intros. subst.
    specialize (H2 i).
    revert H2.
    eapply Proper_Pred; [ | reflexivity ].
    red. intros.
    red. destruct a.
    intros. red in H.
    forward_reason.
    split; eauto.
    split; eauto.
    destruct (pctxD i) eqn:Heq; simpl; auto.
    simpl in H4.
    destruct (pctxD c) eqn:Heq'; simpl in *; try contradiction.
    unfold assert in *.
    red in H0. specialize (H0 t).
    destruct H0; auto. contradiction.
    forward_reason.
    split; eauto.
    intros.
    specialize (H5 us vs).
    gather_facts.
    eapply Pure_pctxD; eauto.
    intros.
    eapply H0. eapply H5.
  Qed.

  (* If I expose these, then I need the logic to expose properties about
   * the substitution
   *)
  Definition getInst ctx : InContext ctx (ctx_subst ctx) :=
    fun ctx => ret (ctx, ctx).

  Definition setInst ctx (s : ctx_subst ctx) : InContext ctx unit :=
    fun _ => ret (s, tt).

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

  Section unify.
    Require Import MirrorCore.UnifyI.
    Require Import MirrorCore.SubstI.

    Variable exprUnify
    : forall subst, Subst subst expr -> SubstUpdate subst expr ->
                    unifier typ expr subst.

    Variable exprUnify_sound
    : forall subst (S : Subst subst expr) (SO : SubstOk subst typ expr) SU (SUO : SubstUpdateOk subst typ expr),
        unify_sound (@exprUnify subst S SU).

    Variable ctx : Ctx typ expr.

    Definition unify (e1 e2 : expr) (t : typ) : InContext ctx bool :=
      fun s =>
        match @exprUnify _ _ _ (getUVars ctx) (getVars ctx) 0 e1 e2 t s with
        | None => Monad.ret (s, false)
        | Some s' => Monad.ret (s', true)
        end.

    Theorem unify_sound
    : forall e1 e2 t,
        InContext_spec
          (fun _ => True)
          (fun res : bool =>
             if res then
               match exprD' (getUVars ctx) (getVars ctx) e1 t
                   , exprD' (getUVars ctx) (getVars ctx) e2 t
               with
               | Some e1D , Some e2D =>
                 Some (fun env =>
                         env_of_exprT e1D env = env_of_exprT e2D env)
               | _ , _ => None
               end
             else
               Some (fun _ => True))
          (unify e1 e2 t).
    Proof. Admitted.

  End unify.

End with_instantiation.
