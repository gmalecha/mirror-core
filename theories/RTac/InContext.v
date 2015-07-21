Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadTrans.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.RTac.Ctx.

Set Implicit Arguments.
Set Strict Implicit.

Section with_instantiation.
(*  Variable inst : Type. *)
  Variable typ expr : Type.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Definition InContext (ctx : Ctx typ expr) (T : Type) : Type :=
    ctx_subst ctx -> m (ctx_subst ctx * T).

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

  Variable mPred : forall {T}, (T -> Prop) -> m T -> Prop.

  (* NOTE: The problem with this definition is that it leaves too much
   * exposed.
   * -
   *)
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

  Definition InContext_spec (WFi : forall ctx, ctx_subst ctx -> Prop)
             {T}
             (WFg : T -> Prop)
             (TD : forall ctx, T -> option (env_of_Ctx ctx -> Prop))
             (c : Ctx typ expr) (t : InContext c T) : Prop :=
    forall (i : ctx_subst c), WFi c i ->
    assume (pctxD i) (fun C =>
      mPred (fun i_g => let '(i',g') := i_g in
                        WFg g' /\ WFi c i' /\
                        assert (pctxD i') (fun I' =>
                        assert (TD c g') (fun G' =>
                                            SubstMorphism i i' /\
                                            forall us vs,
                                              I' (exprT_of_env G') us vs)))
            (t i)).

(*
  Definition lift {T} (x : m T) : InContext T :=
    fun _ ctx => bind (m:=m) x (fun x => ret (m:=m) (ctx, x)).
*)

  Global Instance Monad_InContext ctx : Monad (InContext ctx) :=
  { bind := fun _T _U c k ctx =>
      bind (c ctx)
           (fun ctx_r => let '(ctx',r') := ctx_r in
                         k r' ctx')
  ; ret := fun _T v ctx => ret (ctx, v) }.

  Global Instance MonadT_InContext ctx : MonadT (InContext ctx) m :=
  { lift := fun _T x ctx => bind x (fun x => ret (ctx, x)) }.

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

  (** TODO: This should really be with respect to an underlying exception monad *)
  Definition unify (e1 e2 : expr) (t : typ) : InContext bool.
  Admitted.
*)
End with_instantiation.

Require Import Morphisms.

(*
Section with_error.
  Definition Error (T : Type) : Type := option T.

  Definition PredError {T} (P : T -> Prop) (m : Error T) : Prop :=
    match m with
    | None => True
    | Some x => P x
    end.

  Definition Error_bind {T U} (m : Error T) (k : T -> Error U) : Error U :=
    match m with
    | None => None
    | Some x => k x
    end.

  Theorem Error_bind_sound
  : forall {T U} (P : _ -> Prop) (Q : _ -> _ -> Prop) m k,
      PredError P m ->
      (forall x, PredError (fun z => P x -> Q x z) (k x)) ->
      PredError (fun z => exists x, P x /\ Q x z) (@Error_bind T U m k).
  Proof.
    compute. intros.
    destruct m; auto.
    specialize (H0 t).
    destruct (k t); auto.
    eauto.
  Qed.

  Theorem Error_ret_sound {T} (v : T) : PredError (eq v) (Some v).
  Proof.
    reflexivity.
  Qed.

End with_error.
*)

Section with_error.
  Definition Error (T : Type) : Type := option T.

  Definition PredError {T} (P : (T -> Prop) -> Prop) (m : Error T) : Prop :=
    match m with
    | None => True
    | Some x => P (eq x)
    end.

  Definition Error_bind {T U} (m : Error T) (k : T -> Error U) : Error U :=
    match m with
    | None => None
    | Some x => k x
    end.

  Theorem Error_bind_sound
  : forall {T U} (P : (T -> Prop) -> Prop) (Q : _ -> Prop) m k,
      PredError P m ->
      (forall x, PredError (fun kP => P (eq x) -> Q kP) (k x)) ->
      PredError Q (@Error_bind T U m k).
  Proof.
    compute. intros.
    destruct m; auto.
    specialize (H0 t).
    destruct (k t); auto.
  Qed.

  Theorem Error_ret_sound {T} (v : T) : PredError (fun kP => kP v) (Some v).
  Proof.
    reflexivity.
  Qed.

  Theorem Error_fail_sound {T} : PredError (fun kP => False) (@None T).
  Proof.
    exact I.
  Qed.

  Theorem Proper_PredError_iff {T}
  : Proper (((eq ==> iff) ==> iff) ==> eq ==> iff)%signature
           (@PredError T).
  Proof.
    cbv beta iota zeta delta - [ iff ].
    intros. subst.
    destruct y0; try tauto.
    eapply H. intros; subst; tauto.
  Qed.

  Theorem Proper_PredError_impl {T}
  : Proper (((eq ==> iff) ==> Basics.impl) ==> eq ==> Basics.impl)%signature
           (@PredError T).
  Proof.
    cbv beta iota zeta delta - [ iff ].
    intros. subst.
    destruct y0; try tauto.
    revert H1. eapply H.
    intros. subst. tauto.
  Qed.

  Opaque PredError.

  Goal PredError (fun kP => kP 3) (Error_bind (Some 3) (@Some _)).
  Proof.
    eapply Error_bind_sound.
    eapply Error_ret_sound.
    simpl.
    intros.
    eapply Proper_PredError_impl.
    2: reflexivity.
    2: eapply Error_ret_sound.
    cbv beta iota zeta delta - [ iff ].
    intros; subst. eapply H; eauto.
  Qed.

  Goal PredError (T:=nat) (fun kP => False) (Error_bind None (@Some _)).
  Proof.
    eapply Error_bind_sound.
    eapply Error_fail_sound.
    simpl.
    intros.
    eapply Proper_PredError_impl.
    2: reflexivity.
    2: eapply Error_ret_sound.
    cbv beta iota zeta delta - [ iff ].
    intros; subst.
    inversion H1.
  Qed.

End with_error.

(*
Section with_error.
  Definition Error (T : Type) : Type :=
    forall _T, (T -> _T) -> _T -> _T.

  Definition PredError {T} (P : T -> Prop) (m : Error T) : Prop :=
    @m Prop P True.

  Definition Error_bind {T U} (m : Error T) (k : T -> Error U) : Error U :=
    fun _T good bad =>
      @m _T (fun x => @k x _T good bad) bad.

  Theorem Error_bind_sound
  : forall {T U} P Q R m k,
      PredError Q m ->
      (forall x, PredError (fun z => Q x -> R x z) (k x)) ->
      PredError P (@Error_bind T U m k).
  Proof.
    compute. intros.

End with_error.
*)

Section with_nd.
  Inductive lazy_choice (T : Type) : Type :=
  | Done
  | Choice : T -> (unit -> lazy_choice T) -> lazy_choice T.

  Inductive PredChoice {T} (P : T -> Prop) : lazy_choice T -> Prop :=
  | PredChoice_Done : PredChoice P (Done T)
  | PredChoice_Choice : forall t rest,
      P t ->
      PredChoice P (rest tt) ->
      PredChoice P (Choice t rest).

  Fixpoint Choice_bind {T U} (m : lazy_choice T) (k : T -> lazy_choice U) {struct m} : lazy_choice U :=
    match m with
    | Done _ => Done _
    | Choice a b =>
      (fix iter (l : lazy_choice U) : lazy_choice U :=
         match l with
         | Done _ => Choice_bind (b tt) k
         | Choice x xs => Choice x (fun x => iter (xs x))
         end) (k a)
    end.

  Theorem Choice_bind_sound
  : forall {T U} (P : T -> Prop) (Q : _ -> Prop) m k,
      PredChoice P m ->
      (forall x, PredChoice (fun y => P x -> Q y) (k x)) ->
      PredChoice Q (@Choice_bind T U m k).
  Proof.
    compute. intros.
    induction H.
    { constructor. }
    { specialize (H0 t).
      induction H0; eauto.
      { constructor; eauto. } }
  Qed.

End with_nd.


(*******
Section with_error.
  Definition Error (T : Type) : Type := option T.

  Definition PredError {T} (P : (T -> Prop) -> Prop -> Prop) (m : Error T) : Prop :=
    match m with
    | None => P (fun _ => False) True
    | Some x => P (eq x) False
    end.

  Definition Error_bind {T U} (m : Error T) (k : T -> Error U) : Error U :=
    match m with
    | None => None
    | Some x => k x
    end.


  Require Import Morphisms.


  Definition LR {T} := ((@eq T ==> iff) ==> iff ==> iff)%signature.

  Theorem Error_bind_sound
  : forall {T U} (P : (T -> Prop) -> Prop -> Prop) (Q : _ -> _ -> Prop) m (k : T -> Error U)
      (H:Proper LR P) (H' : Proper LR Q),
      PredError P m ->
      (forall x, PredError (fun kS kF => Q (fun y => (forall Z, P Z False -> Z x)-> kS y) kF) (k x)) ->
      PredError (fun kS kF => Q kS kF \/ P (fun _ => False) kF) (@Error_bind T U m k).
  Proof.
    compute. intros.
    destruct m.
    { specialize (H1 t).
      destruct (k t); auto.
      { admit. }
      { admit. } }
    { clear H0. auto. }
  Admitted.

  Theorem Error_ret_sound {T} (v : T) : PredError (fun kP kF => (forall x, kP x -> x = v) /\ (kF -> False)) (Some v).
  Proof.
    compute. split; auto.
  Qed.

  Theorem Error_fail_sound {T} : PredError (fun kP kF => (forall x, kP x -> False) /\ kF) (@None T).
  Proof.
    compute. tauto.
  Qed.

  Theorem Proper_PredError_iff {T}
  : Proper (((eq ==> iff) ==> iff ==> iff) ==> eq ==> iff)%signature (@PredError T).
  Proof.
    cbv beta iota zeta delta - [ iff ].
    intros. subst.
    destruct y0; try tauto.
    eapply H. intros; subst; tauto. tauto.
    eapply H; try tauto.
  Qed.

(*
  Theorem Proper_PredError_impl {T} : Proper (((eq ==> iff) ==> Basics.impl) ==> eq ==> Basics.impl)%signature (@PredError T).
  Proof.
    cbv beta iota zeta delta - [ iff ].
    intros. subst.
    destruct y0; try tauto.
    revert H1. eapply H.
    intros. subst. tauto.
  Qed.
*)

  Opaque PredError.

  Goal PredError (fun kP kF => (forall x, kP x -> x = 3) /\ (kF -> False)) (Error_bind (Some 3) (@Some _)).
  Proof.
    eapply Proper_PredError_iff.
    2: reflexivity.
    2: eapply Error_bind_sound.
    2: eapply Error_ret_sound.
    Focus 2.
    intros; simpl.
    eapply Proper_PredError_iff.
    2: reflexivity.
    2: eapply Error_ret_sound.
    red. red. intros.
    instantiate (1:= fun kS kF => (forall x, kS x -> x = 3) /\ (kF -> False)). simpl.
    split.
    { intros. destruct H1.
      Require Import Setoid.
      red in H. rewrite <- H0. split; auto.
      intros.
      setoid_rewrite H0 in H1.
      specialize (H1 x).

  Qed.

  Goal PredError (fun kP => kP 3) (Error_bind None (@Some _)).
  Proof.
    eapply Error_bind_sound.
    eapply Error_fail_sound.
    simpl.
    intros.
    eapply Proper_PredError_impl.
    2: reflexivity.
    2: eapply Error_ret_sound.
    cbv beta iota zeta delta - [ iff ].
    intros; subst. eapply H; eauto.
  Qed.


End with_error.
****)