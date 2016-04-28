Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Tactics.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.RewriteRelations.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  (** TODO(gmalecha): This is not necessary *)
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

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


  (** This monad abstracts the idea of working under a context.
   ** It is morally exactly the same as [rtac] except for two differences:
   ** 1) It is generalized over the goal representation so it can avoid
   **    manifesting [Goal]s
   ** 2) It has an extra [tvs'] argument that allows it to avoid pushing
   **    terms into the context when it does not need to.
   **
   ** TODO(gmalecha):
   **   This should be unified with the [rtac] monad but understanding
   **   the full design still requires a bit more work.
   **)
  Definition mrw (T : Type) : Type :=
    tenv typ -> tenv typ -> tenv typ -> nat -> nat ->
    forall c : Ctx typ (expr typ func), ctx_subst c ->
                                        option (T * ctx_subst c).

  Definition rw_ret {T} (val : T) : mrw T :=
    fun _ _ _ _ _ _ s => Some (val, s).

  Definition rw_bind {T U} (c : mrw T) (k : T -> mrw U) : mrw U :=
    fun tvs' tus tvs nus nvs ctx cs =>
      match c tvs' tus tvs nus nvs ctx cs with
      | None => None
      | Some (v,cs') => k v tvs' tus tvs nus nvs ctx cs'
      end.

  Definition rw_orelse {T} (c1 c2 : mrw T) : mrw T :=
    fun tvs' tus tvs nus nvs ctx cs =>
      match c1 tvs' tus tvs nus nvs ctx cs with
      | None => c2 tvs' tus tvs nus nvs ctx cs
      | z => z
      end.

  Definition rw_fail {T} : mrw T :=
    fun tvs' tus tvs nus nvs ctx cs =>
      None.

  Definition rw_bind_catch {T U : Type} (c : mrw T) (k : T -> mrw U)
             (otherwise : mrw U)
  : mrw U :=
    fun tus' tus tvs nus nvs ctx cs =>
      match c tus' tus tvs nus nvs ctx cs with
      | None => otherwise tus' tus tvs nus nvs ctx cs
      | Some (val,cs') => k val tus' tus tvs nus nvs ctx cs'
      end.

  Lemma rw_orelse_case
  : forall (T : Type) (A B : mrw T) a b c d e f g h,
      @rw_orelse _ A B a b c d e f g = h ->
      A a b c d e f g = h \/
      B a b c d e f g = h.
  Proof using.
    unfold rw_orelse. intros.
    forward.
  Qed.

  Lemma rw_bind_catch_case
  : forall (T U : Type) (A : mrw T) (B : T -> mrw U) (C : mrw U)
           a b c d e f g h,
      @rw_bind_catch _ _ A B C a b c d e f g = h ->
      (exists x g', A a b c d e f g = Some (x,g') /\
                    B x a b c d e f g' = h) \/
      (C a b c d e f g = h /\ A a b c d e f g = None).
  Proof using.
    unfold rw_bind_catch. intros; forward.
    left. do 2 eexists; split; eauto.
  Qed.

  Lemma rw_bind_case
  : forall (T U : Type) (A : mrw T) (B : T -> mrw U)
           a b c d e f g h,
      @rw_bind _ _ A B a b c d e f g = Some h ->
      exists x g',
        A a b c d e f g = Some (x, g') /\
        B x a b c d e f g' = Some h.
  Proof using.
    unfold rw_bind. intros; forward.
    do 2 eexists; eauto.
  Qed.

  Section rw_map2.
    Context {T U V : Type}.
    Variable f : T -> U -> mrw V.

    Fixpoint rw_map2 (ts : list T) (us : list U) : mrw (list V) :=
      match ts , us with
        | nil , nil => rw_ret nil
        | t :: ts , u :: us =>
          rw_bind (f t u) (fun v =>
                             rw_bind (rw_map2 ts us)
                                     (fun vs => rw_ret (v :: vs)))
        | _ , _ => rw_fail
      end.
  End rw_map2.

  Definition mrw_equiv {T} (rT : T -> T -> Prop) (l : mrw T) (r : mrw T)
  : Prop :=
    forall a b c d e f g,
      Roption (Eqpair rT eq) (l a b c d e f g) (r a b c d e f g).

  Instance Reflexive_mrw_equiv {T} (rT : T -> T -> Prop)
           {Refl_rT : Reflexive rT}
  : Reflexive (mrw_equiv rT).
  Proof using.
    red. red. intros. eapply Reflexive_Roption. eapply Reflexive_Eqpair; eauto.
  Qed.

  Instance Symmetric_mrw_equiv {T} (rT : T -> T -> Prop)
           {Sym_rT : Symmetric rT}
  : Symmetric (mrw_equiv rT).
  Proof using.
    red. red. intros. eapply Symmetric_Roption. eapply Symmetric_Eqpair; eauto.
    eapply H.
  Qed.

  Instance Transitive_mrw_equiv {T} (rT : T -> T -> Prop)
           {Trans_rT : Transitive rT}
  : Transitive (mrw_equiv rT).
  Proof using.
    red. red. intros. eapply Transitive_Roption.
    eapply Transitive_Eqpair; eauto with typeclass_instances.
    eapply H. eapply H0.
  Qed.

  Lemma rw_bind_assoc
  : forall {T U V} (c : mrw T) (k : T -> mrw U) (k' : U -> mrw V),
      mrw_equiv eq
                (rw_bind (rw_bind c k) k')
                (rw_bind c (fun x => rw_bind (k x) k')).
  Proof using.
    unfold rw_bind. simpl.
    red. intros.
    destruct (c a b c0 d e f g); try constructor.
    destruct p.
    eapply Reflexive_Roption. apply Reflexive_Eqpair; eauto.
  Qed.

  Lemma rw_bind_rw_ret
  : forall {T U} (x : T) (k : T -> mrw U),
      rw_bind (rw_ret x) k = k x.
  Proof using. reflexivity. Qed.

  Lemma rw_bind_rw_fail
  : forall {T U} (k : T -> mrw U),
      rw_bind rw_fail k = rw_fail.
  Proof using. reflexivity. Qed.

  Lemma Proper_rw_bind (T U : Type)
  : Proper (mrw_equiv (@eq T) ==> (pointwise_relation (mrw_equiv (@eq U))) ==>
            mrw_equiv (@eq U)) (@rw_bind T U).
  Proof using.
    red. red. red. red. unfold rw_bind. intros.
    red in H.
    specialize (H a b c d e f g).
    destruct H. constructor.
    destruct H. subst.
    eapply H0.
  Qed.

  Instance Injective_mrw_equiv_rw_ret {T} (rT : T -> T -> Prop) (a b : T)
  : Injective (mrw_equiv rT (rw_ret a) (rw_ret b)) :=
  { result := rT a b }.
  Proof using.
    unfold rw_ret. intros. red in H.
    specialize (H nil nil nil 0 0 _ (@TopSubst _ _ nil nil)).
    inv_all. assumption.
  Defined.
  (** End of monad definitions **)

  (* [Progressing T] = [option T] but adds the information that the result
   * makes progress or does not, i.e. a [Progressing T] is relative to an
   * input [in]. If the output is [NoProgress] then the meaning is the same as
   * the input, if the result is [Progress x] then [x] is assumed to be
   * different than [in].
   *)
  Inductive Progressing (T : Type) : Type :=
  | Progress (new_val : T)
  | NoProgress.

  Arguments NoProgress {_}.

  Definition ProgressD {T} (a : T) (x : Progressing T) : T :=
    match x with
    | Progress x => x
    | NoProgress => a
    end.

  Definition fmap_Progressing {T U : Type} (f : T -> U) (x : Progressing T)
    : Progressing U :=
    match x with
    | NoProgress => NoProgress
    | Progress x => Progress (f x)
    end.

  Local Existing Instance Subst_ctx_subst.
  Local Existing Instance SubstOk_ctx_subst.
  Local Existing Instance SubstUpdate_ctx_subst.
  Local Existing Instance SubstUpdateOk_ctx_subst.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (** These are the core specifications. **)
  (****************************************)

  (* [setoid_rewrite_rel e r rw] states that if [rw] is run on any context that
   * [e] is well-typed in, then the final context will extend the initial
   * context and the result will be related at [r]
   *)
  Definition setoid_rewrite_rel
             (e : expr typ func) (r : R)
             (rw : mrw (Progressing (expr typ func)))
  : Prop :=
    forall (ctx : Ctx typ (expr typ func)) cs (tvs' : tenv typ) cs'
           (e' : Progressing (expr typ func)),
      let tus := getUVars ctx in
      let tvs := getVars ctx in
      rw tvs' tus tvs (length tus) (length tvs) ctx cs = Some (e', cs') ->
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst cs' /\
      forall t rD,
      RD RbaseD r t = Some rD ->
      match pctxD cs
          , lambda_exprD tus (tvs' ++ tvs) t e
          , pctxD cs'
          , lambda_exprD tus (tvs' ++ tvs) t (ProgressD e e')
      with
      | Some _ , Some eD , Some csD' , Some eD' =>
        SubstMorphism cs cs' /\
        (forall (us : HList.hlist typD (getAmbientUVars ctx))
                (vs : HList.hlist typD (getAmbientVars ctx)),
            csD' (fun (us : HList.hlist typD (getUVars ctx))
                      (vs : HList.hlist typD (getVars ctx)) =>
                    forall vs',
                      rD (eD us (hlist_app vs' vs))
                         (eD' us (hlist_app vs' vs))) us vs)
      | None , _ , _ , _
      | Some _ , None , _ , _ => True
      | Some _ , Some _ , None , _
      | Some _ , Some _ , Some _ , None => False
      end.

  (* [setoid_rewrite_spec rw] simply states that [rw] is sound for every
   * [e] and [r].
   *)
  Definition setoid_rewrite_spec
             (rw : expr typ func -> R -> mrw (Progressing (expr typ func)))
  : Prop :=
    forall e r, @setoid_rewrite_rel e r (rw e r).

  (* This definition is used for recursive rewriting, it computes a list of
   * sufficient relations to rewrite in the arguments. It is specialized to
   * justify termination.
   *   [respectful_spec resp] states that [resp e r = rs] implies
   *   [Proper (rs ==> r) e]
   * TODO(gmalecha):
   *   This can be generalized a bit to support changing the result argument
   *)
  Definition respectful_spec (respectful : expr typ func -> R -> mrw (list R))
  : Prop :=
    forall tvs' (ctx : Ctx typ (expr typ func)) cs cs' e r rs,
      let tus := getUVars ctx in
      let tvs := getVars ctx in
      respectful e r tvs' tus tvs (length tus) (length tvs) ctx cs = Some (rs,cs') ->
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst cs' /\
      forall ts t rD,
      RD RbaseD r t = Some rD ->
      match pctxD cs
          , lambda_exprD tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) e
          , pctxD cs'
          , RD RbaseD (fold_right Rrespects r rs) (fold_right (typ2 (F:=RFun)) t ts)
      with
      | Some _ , Some eD , Some csD' , Some rD' =>
        SubstMorphism cs cs' /\
        (forall (us : HList.hlist typD (getAmbientUVars ctx))
                (vs : HList.hlist typD (getAmbientVars ctx)),
            csD' (fun (us : HList.hlist typD (getUVars ctx))
                      (vs : HList.hlist typD (getVars ctx)) =>
                    forall vs',
                      Proper rD' (eD us (hlist_app vs' vs))) us vs)
      | None , _ , _ , _
      | Some _ , None , _ , _ => True
      | Some _ , Some _ , None , _
      | Some _ , Some _ , Some _ , None => False
      end.

  Definition lem_rewriter : Type :=
    expr typ func -> R -> mrw (Progressing (expr typ func)).
  Definition respectful_dec : Type :=
    expr typ func -> R -> mrw (list R).

End setoid.

(* This fast-path eliminates the need to build environments when
 * unification is definitely going to fail
    Fixpoint checkUnify (e1 e2 : expr typ func) : bool :=
      match e1 , e2 with
      | ExprCore.UVar _ , _ => true
      | ExprCore.Var v1 , ExprCore.Var v2 => v1 ?[ eq ] v2
      | Inj a , Inj b => a ?[ eq ] b
      | App f1 x1 , App f2 x2 => checkUnify f1 f2
      | Abs _ _ , Abs _ _ => true
      | _ , ExprCore.UVar _ => true
      | _ , _ => false
      end.
 *)

Arguments mrw _ _ _ : clear implicits.
Arguments NoProgress {_}.
Arguments Progress {_} _.
Arguments lem_rewriter typ func Rbase : clear implicits.
Arguments respectful_dec typ func Rbase : clear implicits.

Export MirrorCore.Lambda.RewriteRelations.