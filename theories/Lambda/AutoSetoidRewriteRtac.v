Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Recur.Facts.
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

  (** This is the core of the rewriter which applies respectful and performs
   ** recursive rewriting.
   **)
  Section setoid_rewrite.
    Definition arg_rewriter : Type :=
      expr typ func * (R -> mrw (Progressing (expr typ func))).

    (* This structure is similar in spirit to hereditary substitutions where
     * arguments are paired with the functions used to rewrite them. This allows
     * for recursive rewriting without manifesting well-foundedness proofs.
     *)
    Variable respectfulness
    : expr typ func ->
      forall (es : list arg_rewriter)
             (rg : R),
        mrw (Progressing (expr typ func)).

    (* This is the core rewriter.
     *   [setoid_rewrite' e es r] performs rewriting on [e @ es] with respect
     *   to relation [r].
     *)
    Fixpoint setoid_rewrite'
             (e : expr typ func) (es : list arg_rewriter) (rg : R)
    : mrw (Progressing (expr typ func)) :=
      match e with
      | App f x =>
        setoid_rewrite' f ((x, setoid_rewrite' x nil) :: es) rg
      | Abs t e' =>
        match es with
        | nil =>
          match rg with
          | Rpointwise _t (*=t*) rg' =>
            fun tvs tus tvs' nus nvs c cs =>
              match @setoid_rewrite' e' nil rg'
                                     (t::tvs) tus tvs' nus nvs c cs
              with
              | Some (e'',cs'') =>
                Some (fmap_Progressing (Abs t) e'', cs'')
              | None => None
              end
          | _ => respectfulness (Abs t e') es rg
          end
        | _ => respectfulness (Abs t e') es rg
        end
      | Var v => respectfulness (Var v) es rg
      | UVar u => respectfulness (UVar u) es rg
      | Inj i => respectfulness (Inj i) es rg
      end.

    Definition setoid_rewrite (e : expr typ func) (rg : R)
    : mrw (Progressing (expr typ func)) :=
      setoid_rewrite' e nil rg.

    Definition setoid_rewrite_rec (ls : list arg_rewriter)
    : Prop :=
      Forall (fun e =>
                forall r,
                  @setoid_rewrite_rel (fst e) r (snd e r)) ls.

    Hypothesis respectfulness_sound
    : forall e es rg,
        @setoid_rewrite_rec es ->
        @setoid_rewrite_rel (apps e (map fst es))
                            rg (respectfulness e es rg).

    Lemma setoid_rewrite'_sound
    : forall e es rg,
        @setoid_rewrite_rec es ->
        @setoid_rewrite_rel (apps e (map fst es))
                            rg (setoid_rewrite' e es rg).
    Proof using RSymOk_func RTypeOk_typD Typ2Ok_Fun respectfulness_sound.
      induction e; eauto using respectfulness_sound.
      { simpl in *. intros.
        eapply IHe1; eauto.
        constructor; eauto.
        simpl. intros. eapply IHe2. constructor. }
      { simpl in *. intros.
        destruct es; eauto using respectfulness_sound.
        destruct rg; eauto using respectfulness_sound.
        red; red in IHe; simpl in *.
        intros.
        forwardy. inv_all; subst.
        specialize (IHe nil rg (Forall_nil _) _ _ (t :: tvs') _ _ H0 H1);
          clear H0 H1.
        forward_reason.
        split; auto. intros.
        arrow_case_any.
        { red in x1; subst.
          simpl in H2.
          autorewrite_with_eq_rw_in H2.
          forwardy. inv_all; subst.
          specialize (H1 _ _ H5).
          forward_reason.
          destruct (pctxD cs) eqn:HpctxDcs; trivial.
          rewrite lambda_exprD_Abs; eauto with typeclass_instances.
          rewrite typ2_match_iota; eauto with typeclass_instances.
          unfold Monad.bind, Monad.ret; simpl.
          autorewrite with eq_rw.
          destruct (type_cast x t) eqn:Htcxt; trivial.
          simpl in *.
          destruct (lambda_exprD (getUVars ctx) (t :: tvs' ++ getVars ctx) x0 e)
                   eqn:HexprDe; trivial.
          forwardy. forward_reason.
          rewrite H1.
          destruct p.
          { simpl ProgressD in *.
            rewrite lambda_exprD_Abs; eauto with typeclass_instances.
            rewrite typ2_match_iota; eauto with typeclass_instances.
            unfold Monad.bind, Monad.ret; simpl.
            autorewrite_with_eq_rw.
            rewrite Htcxt.
            rewrite H4.
            split; eauto.
            intros.
            generalize (H7 us vs); clear H7.
            eapply Ap_pctxD; eauto.
            eapply Pure_pctxD; eauto.
            clear. destruct r.
            intros.
            autorewrite_with_eq_rw.
            try do 2 rewrite (Eq.match_eq_sym_eq (typ2_cast x x0)).
            red. intros.
            eapply (H (Hcons a vs')). }
          { simpl ProgressD in *.
            rewrite lambda_exprD_Abs; eauto with typeclass_instances.
            rewrite typ2_match_iota; eauto with typeclass_instances.
            unfold Monad.bind, Monad.ret; simpl.
            autorewrite_with_eq_rw.
            rewrite Htcxt.
            rewrite H4.
            split; eauto.
            intros.
            generalize (H7 us vs); clear H7.
            eapply Ap_pctxD; eauto.
            eapply Pure_pctxD; eauto.
            clear. destruct r.
            intros.
            autorewrite_with_eq_rw.
            try do 2 rewrite (Eq.match_eq_sym_eq (typ2_cast x x0)).
            red. intros.
            eapply (H (Hcons a vs')). } }
        { exfalso; clear - H2. congruence. } }
    Qed.

    Theorem setoid_rewrite_sound
    : forall e rg,
        @setoid_rewrite_rel e rg (setoid_rewrite e rg).
    Proof using RSymOk_func RTypeOk_typD Typ2Ok_Fun respectfulness_sound.
      intros. eapply setoid_rewrite'_sound.
      constructor.
    Qed.

  End setoid_rewrite.

  Section top_bottom.
    Context (reflexive : refl_dec R)
            (transitive : trans_dec R)
            (rw : expr typ func -> R -> mrw (Progressing (expr typ func)))
            (respectful : expr typ func -> R -> mrw (list R)).

    Hypothesis reflexiveOk : refl_dec_ok (RD RbaseD) reflexive.
    Hypothesis transitiveOk : trans_dec_ok (RD RbaseD) transitive.

    Hypothesis rwOk : setoid_rewrite_spec rw.
    Hypothesis respectfulOk : respectful_spec respectful.

    (** TODO(gmalecha): Move **)
    Lemma lambda_exprD_App
    : forall tus tvs td tr f x fD xD,
        lambda_exprD tus tvs (typ2 (F:=RFun) td tr) f = Some fD ->
        lambda_exprD tus tvs td x = Some xD ->
        lambda_exprD tus tvs tr (App f x) = Some (AbsAppI.exprT_App fD xD).
    Proof using Typ2Ok_Fun RSymOk_func RTypeOk_typD.
      intros.
      autorewrite with exprD_rw; simpl.
      erewrite lambda_exprD_typeof_Some by eauto.
      rewrite H. rewrite H0. reflexivity.
    Qed.

    Lemma lambda_exprD_Abs_prem
      : forall tus tvs t t' x xD,
        ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Abs t' x) = Some xD ->
        exists t'' (pf : typ2 t' t'' = t) bD,
          ExprDsimul.ExprDenote.lambda_exprD tus (t' :: tvs) t'' x = Some bD /\
          xD = match pf with
               | eq_refl => AbsAppI.exprT_Abs bD
               end.
    Proof using Typ2Ok_Fun RSymOk_func RTypeOk_typD.
      intros.
      autorewrite with exprD_rw in H.
      destruct (typ2_match_case t); forward_reason.
      { rewrite H0 in H; clear H0.
        red in x2; subst. simpl in *.
        autorewrite_with_eq_rw_in H.
        destruct (type_cast x0 t'); subst; try congruence.
        red in r; subst.
        forward. inv_all; subst.
        eexists; exists eq_refl.
        eexists; split; eauto. inversion H.
        unfold AbsAppI.exprT_Abs.
        autorewrite_with_eq_rw.
        reflexivity. }
      { rewrite H0 in H. congruence. }
    Qed.

    Fixpoint recursive_rewrite' (prog : bool) (f : expr typ func)
             (es : list arg_rewriter)
             (rs : list R)
    : mrw (Progressing (expr typ func)) :=
      match es , rs with
      | nil , nil => rw_ret (if prog then Progress f else NoProgress)
      | (e,rec) :: es , r :: rs =>
        rw_bind (rec r)
                (fun e' =>
                   match e' with
                   | Progress e' =>
                     recursive_rewrite' true (App f e') es rs
                   | NoProgress =>
                     recursive_rewrite' prog (App f e) es rs
                   end)
      | _ , _ => rw_fail
      end.

    Definition recursive_rewrite := recursive_rewrite' false.

    Lemma RD_tyAcc : forall d a b c e f,
        RD RbaseD a b = Some c ->
        RD RbaseD (fold_right Rrespects a d) e = Some f ->
        b = e \/ TransitiveClosure.leftTrans (@tyAcc _ _) b e.
    Proof using Typ2Ok_Fun RbaseD_single_type.
      induction d.
      { simpl; left.
        eapply RD_single_type; eauto. }
      { simpl. intros. arrow_case_any; try congruence. red in x1. subst.
        simpl in *. forwardy.
        clear H3 H1.
        specialize (IHd _ _ _ _ _ H H2).
        destruct IHd.
        { subst. right.
          constructor. eapply tyAcc_typ2R; eauto. }
        { right.
          eapply TransitiveClosure.leftTrans_rightTrans.
          eapply TransitiveClosure.RTStep.
          eapply TransitiveClosure.leftTrans_rightTrans.
          eassumption.
          eapply tyAcc_typ2R; eauto. } }
    Qed.

    Lemma recursive_rewrite'_sound
    : forall tvs',
        forall es ctx (cs : ctx_subst ctx) cs' f f' rs e' prog,
          let tvs := getVars ctx in
          let tus := getUVars ctx in
          recursive_rewrite' prog f' es rs tvs' tus tvs (length tus) (length tvs) cs = Some (e', cs') ->
          forall (Hrws : setoid_rewrite_rec es),
            WellFormed_ctx_subst cs ->
            WellFormed_ctx_subst cs' /\
            forall r t rD',
              RD RbaseD r t = Some rD' ->
            forall ts fD rD eD,
              lambda_exprD tus (tvs' ++ tvs) t (apps f (map fst es)) = Some eD ->
              lambda_exprD tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f = Some fD ->
              RD RbaseD (fold_right Rrespects r rs) (fold_right (typ2 (F:=RFun)) t ts) = Some rD ->
              match pctxD cs
                  , lambda_exprD tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f'
                  , pctxD cs'
              with
              | Some csD , Some fD' , Some csD' =>
                exists eD',
                lambda_exprD tus (tvs' ++ tvs) t (ProgressD (apps f' (map fst es)) e') = Some eD' /\
                SubstMorphism cs cs' /\
                forall us vs,
                  csD' (fun us vs =>
                          forall vs',
                            rD (fD us (hlist_app vs' vs)) (fD' us (hlist_app vs' vs)) ->
                            rD' (eD us (hlist_app vs' vs)) (eD' us (hlist_app vs' vs))) us vs
              | Some _ , Some _ , None => False
              | Some _ , None , _  => True
              | None , _ , _ => True
              end.
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Typ2Ok_Fun.
      induction es; destruct rs; simpl in *.
      { inversion 1; subst. clear H.
        intros.
        split; try assumption. intros.
        consider (pctxD cs'); intros; trivial.
        assert (ts = nil).
        { generalize (RD_single_type _ RbaseD_single_type _ _ _ H0 H3).
          destruct ts; auto.
          simpl. intros.
          exfalso.
          assert (TransitiveClosure.rightTrans (@tyAcc _ _) t (typ2 t0 (fold_right (typ2 (F:=RFun)) t ts))).
          { clear - Typ2Ok_Fun. revert t. revert t0.
            induction ts.
            { simpl. constructor. eapply tyAcc_typ2R; eauto. }
            simpl. intros.
            eapply TransitiveClosure.RTStep. eapply IHts.
            eapply tyAcc_typ2R; eauto. }
          rewrite H5 in H6 at 1.
          eapply wf_anti_sym; [ | eapply H6 ].
          eauto using wf_rightTrans, wf_tyAcc. }
        subst. simpl in *.
        destruct prog.
        { simpl.
          consider (ExprDsimul.ExprDenote.lambda_exprD
                      (getUVars ctx) (tvs' ++ getVars ctx)
                      t f'); intros; trivial.
          eexists; split; eauto.
          split; [ reflexivity | ].
          intros.
          eapply Pure_pctxD; eauto.
          intros.
          rewrite H1 in *. rewrite H3 in *.
          inv_all. subst. assumption. }
        { simpl. rewrite H1 in H2. inv_all.
          subst.
          destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t f'); trivial.
          eexists; split; eauto.
          split; [ reflexivity | ].
          intros. rewrite H3 in H0. inv_all. subst.
          eapply Pure_pctxD; eauto. } }
      { inversion 2. }
      { simpl. unfold rw_fail. destruct a. inversion 2. }
      { intros. destruct a as [ a_fst a_snd ].
        eapply rw_bind_case in H.
        forward_reason.
        inversion Hrws; clear Hrws; subst.
        specialize (H4 _ _ _ _ _ _ H H0); clear H0 H.
        forward_reason.
        assert (exists prog',
           recursive_rewrite' prog' (App f' (ProgressD a_fst x)) es rs tvs'
                              (getUVars ctx) (getVars ctx) (length (getUVars ctx))
                              (length (getVars ctx)) x0 = Some (e', cs') /\
           (e' = NoProgress -> x = NoProgress)).
        { clear - H1. destruct x; eexists; split; eauto.
          { destruct e'; try congruence.
            intro. clear H.
            generalize dependent (App f' new_val).
            revert rs. revert x0. clear. induction es.
            { simpl. destruct rs; compute; congruence. }
            { simpl. destruct a.
              destruct rs; simpl; try solve [ compute ; congruence ].
              intros.
              eapply rw_bind_case in H1.
              forward_reason.
              destruct x; eauto. } } }
        clear H1. rename H2 into H1. destruct H1 as [ ? [ ? ? ] ].
        rename H2 into Hnoprogress.
        specialize (IHes _ _ _ (App f a_fst) _ _ _ _ H1 H5 H); clear H1 H5 H.
        forward_reason.
        split; eauto.
        intros.
        arrow_case_any.
        { unfold Relim in H5; autorewrite_with_eq_rw_in H5.
          forwardy; inv_all; subst.
          destruct ts.
          { exfalso.
            simpl in *.
            red in x4. subst.
            clear - RTypeOk_typD Typ2Ok_Fun RbaseD_single_type H10 H2.
            eapply RD_tyAcc in H10; eauto.
            clear - RTypeOk_typD Typ2Ok_Fun RbaseD_single_type H10 H2.
            destruct H10.
            { eapply tyArr_circ_R; eauto. }
            { assert ((TransitiveClosure.leftTrans (@tyAcc _ _)) x3 (typ2 x2 x3)).
              { constructor. eapply tyAcc_typ2R; eauto. }
              generalize (TransitiveClosure.leftTrans_trans H H0).
              eapply wf_anti_sym.
              eapply wf_leftTrans. eapply wf_tyAcc; eauto. } }
          { simpl in *.
            specialize (H0 _ _ H5).
            destruct (pctxD cs) eqn:HpctxDcs; trivial.
            destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx)
                             (typ2 t0 (fold_right (typ2 (F:=RFun)) t ts)) f')
                     eqn:Hlambda_exprDf'; trivial.
            specialize (H1 _ _ _ H2 ts).
            red in x4.
            rewrite lambda_exprD_apps in H3 by eauto with typeclass_instances.
            unfold apps_sem' in H3.
            generalize (lambda_exprD_typeof_expr _ (or_introl H4)).
            intro Htypeof_f.
            simpl in H3. rewrite Htypeof_f in H3.
            forwardy.
            unfold type_of_apply in H9.
            rewrite typ2_match_iota in H9 by eauto with typeclass_instances.
            autorewrite_with_eq_rw_in H9. forwardy.
            red in y4. inv_all. subst. clear H9.
            assert (x5 = y1).
            { eapply lambda_exprD_typeof_eq; eauto. }
            destruct (typ2_inj _ _ _ _ x4).
            red in H11; red in H13; subst.
            rewrite H12 in *.
            forwardy.
            revert H1.
            Cases.rewrite_all_goal.
            rewrite H7 in H4; inv_all; subst.

            rewrite (lambda_exprD_apps _ _ _
                          (getUVars ctx) (tvs' ++ getVars ctx)
                          (map fst es) (App f a_fst) t).
            unfold apps_sem'. simpl.
            rewrite Htypeof_f.
            erewrite lambda_exprD_typeof_Some by eauto.
            unfold type_of_apply.
            rewrite H6.
            rewrite type_cast_refl; eauto with typeclass_instances.
            unfold Relim.
            autorewrite_with_eq_rw.
            erewrite lambda_exprD_App by eauto.
            rewrite H8.
            intro Hx; specialize (Hx _ _ _ eq_refl eq_refl eq_refl).
            erewrite lambda_exprD_App in Hx by eauto.
            forward.
            forward_reason; inv_all; subst.
            destruct e'.
            { simpl in *.
              eexists; split; eauto.
              split; [ etransitivity; eassumption | ].
              intros. gather_facts.
              eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
              gather_facts.
              eapply Pure_pctxD; eauto.
              rewrite (UIP_refl x4).
              simpl.
              unfold AbsAppI.exprT_App.
              generalize (typ2_cast x2 (fold_right (typ2 (F:=RFun)) t ts)).
              clear.
              generalize dependent (typD (typ2 x2 (fold_right (typ2 (F:=RFun)) t ts))).
              intros; subst.
              simpl in *.
              eauto. }
            { specialize (Hnoprogress eq_refl).
              subst.
              simpl ProgressD in *.
              eexists; split; eauto.
              split; [ etransitivity; eassumption | ].
              intros. gather_facts.
              eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
              gather_facts.
              eapply Pure_pctxD; eauto.
              rewrite (UIP_refl x4).
              simpl.
              unfold AbsAppI.exprT_App.
              generalize (typ2_cast x2 (fold_right (typ2 (F:=RFun)) t ts)).
              clear.
              generalize dependent (typD (typ2 x2 (fold_right (typ2 (F:=RFun)) t ts))).
              intros; subst.
              simpl in *.
              eauto. } } }
        { exfalso. clear - H5. inversion H5. } }
    Time Qed.

    Theorem recursive_rewrite_sound
    : forall tvs',
        forall es ctx (cs : ctx_subst ctx) cs' f f' rs e',
          let tvs := getVars ctx in
          let tus := getUVars ctx in
          recursive_rewrite f' es rs tvs' tus tvs (length tus) (length tvs) cs = Some (e', cs') ->
          forall (Hrws : setoid_rewrite_rec es),
            WellFormed_ctx_subst cs ->
            WellFormed_ctx_subst cs' /\
            forall r t rD',
              RD RbaseD r t = Some rD' ->
            forall ts fD rD eD,
              lambda_exprD tus (tvs' ++ tvs) t (apps f (map fst es)) = Some eD ->
              lambda_exprD tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f = Some fD ->
              RD RbaseD (fold_right Rrespects r rs) (fold_right (typ2 (F:=RFun)) t ts) = Some rD ->
              match pctxD cs
                  , lambda_exprD tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f'
                  , pctxD cs'
              with
              | Some csD , Some fD' , Some csD' =>
                exists eD',
                lambda_exprD tus (tvs' ++ tvs) t (ProgressD (apps f' (map fst es)) e') = Some eD' /\
                SubstMorphism cs cs' /\
                forall us vs,
                  csD' (fun us vs =>
                          forall vs',
                            rD (fD us (hlist_app vs' vs)) (fD' us (hlist_app vs' vs)) ->
                            rD' (eD us (hlist_app vs' vs)) (eD' us (hlist_app vs' vs))) us vs
              | Some _ , Some _ , None => False
              | Some _ , None , _  => True
              | None , _ , _ => True
              end.
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Typ2Ok_Fun.
      intros.
      eapply recursive_rewrite'_sound in H; eauto.
    Qed.

    (** THIS ALGORITHM DOES NOT SEEM TO BE THE BEST
     ** Is there a way to handle the possibility of [rw] failing without
     ** the possibility of redundant back-tracking?
     **)
    Definition bottom_up (e : expr typ func) (r : R)
    : mrw (Progressing (expr typ func)) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
	     (rw_bind_catch
                (respectful e r)
                (fun rs =>
                   rw_bind (recursive_rewrite e efs rs)
			   (fun e' =>
                              if transitive r
                              then match e' with
                                   | NoProgress =>
                                     let e := apps e es in
                                     rw_orelse (rw e r)
                                               (rw_ret NoProgress)
                                   | Progress e' =>
                                     rw_orelse
                                       (rw_bind
                                          (rw e' r)
                                          (fun x =>
                                             match x with
                                             | NoProgress =>
                                               rw_ret (Progress e')
                                             | _ => rw_ret x
                                             end))
                                       (rw_ret (Progress e'))
                                   end
                              else match e' with
                                   | NoProgress =>
                                     rw (apps e es) r
                                   | e' => rw_ret e'
                                   end))
                (fun x => rw (apps e es) r x))
	     (if reflexive r
              then rw_ret NoProgress
              else rw_fail))
        e r.

(* This is an alternative implementation that seems like it might be nicer
    Definition bottom_up (e : expr typ func) (r : R)
    : mrw (Progressing (expr typ func)) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
	     (rw_bind_catch
                (respectful e r)
                (fun rs =>
                   rw_bind (recursive_rewrite e efs rs)
			   (fun e' =>
                              match e' with
                              | NoProgress =>
                                let e := apps e es in
                                rw_orelse (rw e r)
                                          (rw_ret NoProgress)
                              | Progress e' as X =>
                                if transitive r
                                then rw_orelse
                                       (rw_bind
                                          (rw e' r)
                                          (fun x =>
                                             match x with
                                             | NoProgress =>
                                               rw_ret (Progress e')
                                             | _ => rw_ret x
                                             end))
                                       (rw_ret (Progress e'))
                                else rw_ret X
                              end))
                (fun x => rw (apps e es) r x))
	     (if reflexive r
              then rw_ret NoProgress
              else rw_fail))
        e r.
*)

    Lemma bottom_up_sound_lem
    : forall e rg,
        @setoid_rewrite_rel e rg (bottom_up e rg).
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Typ2Ok_Fun
          reflexiveOk respectfulOk rwOk transitiveOk.
      unfold bottom_up. intros.
      eapply setoid_rewrite_sound; eauto; try solve [ constructor ].
      clear rg e.
      intros.
      red. intros.
      eapply rw_orelse_case in H0; destruct H0.
      { eapply rw_bind_catch_case in H0; destruct H0.
        { forward_reason.
          eapply rw_bind_case in H2.
          forward_reason.
          eapply respectfulOk in H0; destruct H0; eauto.
          eapply recursive_rewrite_sound with (f := e) in H2; eauto.
          forward_reason.
          consider (transitive rg); intros.
          { destruct x1.
            { eapply rw_orelse_case in H6; destruct H6.
              { eapply rw_bind_case in H6.
                forward_reason.
                rename H7 into Hrest.
                eapply rwOk in H6. destruct H6; auto.
                assert (cs' = x3 /\ e' = match x1 with
                                         | Progress _ => x1
                                         | NoProgress => Progress new_val
                                         end).
                { clear - Hrest.
                  destruct x1; inversion Hrest; auto. }
                destruct H8; clear Hrest; subst.
                split; auto.
                intros.
                specialize (H7 _ _ H8).
                specialize (fun ts => H4 ts _ _ H8).
                destruct (pctxD cs) eqn:HpctxDcs; trivial.
                destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es)))
                         eqn:Hlambda_exprDapps_e_es; trivial.
                specialize (fun ts fD rD => H5 _ _ _ H8 ts fD rD _ Hlambda_exprDapps_e_es).
                eapply apps_lambda_exprD_fold_type in Hlambda_exprDapps_e_es; eauto.
                forward_reason.
                specialize (H4 x4).
                rewrite H9 in H4.
                destruct (pctxD x0) eqn:HpctxDx0; try contradiction.
                destruct (RD RbaseD (fold_right Rrespects rg x)
                             (fold_right (typ2 (F:=RFun)) t x4)) eqn:Hrd;
                  try contradiction.
                specialize (H5 _ _ _ H9 Hrd).
                rewrite H9 in *.
                destruct (pctxD x2) eqn:HpctxDx2; try contradiction.
                forward_reason.
                simpl in H5. rewrite H5 in *.
                forwardy.
                forward_reason.
                rewrite H7.
                cutrewrite (ProgressD (apps e (map fst es))
                                      match x1 with
                                      | Progress _ => x1
                                      | NoProgress => Progress new_val
                                      end = ProgressD new_val x1);
                  [ | clear; destruct x1; reflexivity ].
                rewrite H15.
                split.
                { etransitivity; [ eassumption | etransitivity; eassumption ]. }
                { intros.
                  gather_facts.
                  eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
                  gather_facts.
                  eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
                  gather_facts.
                  eapply Pure_pctxD; eauto.
                  intros.
                  eapply transitiveOk in H8; eauto.
                  etransitivity; [ clear H17 | eapply H17 ].
                  eapply H14; clear H14.
                  eapply H12. } }
              { compute in H6. inv_all. subst.
                simpl ProgressD in *.
                split; auto.
                intros.
                specialize (H5 _ _ _ H6).
                specialize (fun tvs' => H4 tvs' _ _ H6).
                destruct (pctxD cs) eqn:HpctxD_cs; trivial.
                destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t
                                 (apps e (map fst es))) eqn:Hlambda_exprD_e; trivial.
                specialize (fun ts fD rD => H5 ts fD rD _ eq_refl).
                eapply apps_lambda_exprD_fold_type in Hlambda_exprD_e; try assumption.
                forward_reason.
                specialize (H4 x1).
                rewrite H7 in H4.
                destruct (pctxD x0) eqn:HpctxDx0; try contradiction.
                destruct (RD RbaseD (fold_right Rrespects rg x)
                             (fold_right (typ2 (F:=RFun)) t x1)) eqn:Hrd;
                  try contradiction.
                specialize (H5 _ _ _ H7 Hrd).
                rewrite H7 in *.
                destruct (pctxD cs') eqn:HpctxDx2; try contradiction.
                forward_reason.
                simpl in H5. rewrite H5 in *.
                split.
                { etransitivity; [ eassumption | eassumption ]. }
                { intros.
                  gather_facts.
                  eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
                  gather_facts.
                  eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
                  gather_facts.
                  eapply Pure_pctxD; eauto.
                  intros. eapply H12. eapply H11. } } }

            { eapply rw_orelse_case in H6. destruct H6.
              { eapply rwOk in H6.
                forward_reason.
                split; auto. intros.
                specialize (fun ts => H4 ts _ _ H8); specialize (H7 _ _ H8).
                destruct (pctxD cs) eqn:pctxD_cs; trivial.
                destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t
                                 (apps e (map fst es))) eqn:Hlambda_exprDapps_e_es; trivial.
                specialize (H5 _ _ _ H8).
                rewrite Hlambda_exprDapps_e_es in H5.
                eapply apps_lambda_exprD_fold_type in Hlambda_exprDapps_e_es; try assumption.
                forward_reason.
                specialize (H4 x1).
                generalize (H5 x1); clear H5.
                rewrite H9 in *.
                forwardy.
                Cases.rewrite_all_goal.
                intro Hx; specialize (Hx _ _ _ eq_refl eq_refl eq_refl).
                forwardy.
                forward_reason.
                revert H7.
                Cases.rewrite_all_goal.
                intro H7.
                forwardy.
                Cases.rewrite_all_goal.
                forward_reason.
                split.
                { repeat try (etransitivity; [ eassumption | ]). reflexivity. }
                { eauto. } }
              { compute in H6.
                inv_all; subst. simpl in *.
                split; auto. intros.
                specialize (fun ts => H4 ts _ _ H6); specialize (H5 _ _ _ H6).
                destruct (pctxD cs) eqn:pctxD_cs; trivial.
                destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))) eqn:Hlambda_exprDapps_e_es; trivial.
                eapply apps_lambda_exprD_fold_type in Hlambda_exprDapps_e_es; try assumption.
                forward_reason.
                specialize (H4 x1).
                generalize (H5 x1); clear H5.
                rewrite H7 in *.
                forwardy.
                Cases.rewrite_all_goal.
                intro Hx; specialize (Hx _ _ _ eq_refl eq_refl eq_refl).
                forwardy. forward_reason.
                inv_all. subst.
                Cases.rewrite_all_goal.
                split; [ reflexivity | ].
                intros.
                gather_facts.
                eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
                gather_facts.
                eapply Pure_pctxD; eauto.
                clear.
                intros. eapply H0.
                eapply H. } } }

          { clear H3.
            destruct x1.
            { inversion H6; clear H6; subst.
              split; eauto. intros.
              specialize (H5 _ _ _ H3).
              specialize (fun ts => H4 ts _ _ H3).
              destruct (pctxD cs) eqn:HpctxDcs; trivial.
              destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))) eqn:Hlambda_exprDapps_e_es; trivial.
              destruct (apps_lambda_exprD_fold_type _ _ _ _ _ _ Hlambda_exprDapps_e_es).
              forward_reason.
              specialize (H4 x1).
              specialize (fun rD => H5 x1 _ rD _ eq_refl H6).
              rewrite H6 in *.
              destruct (pctxD x0) eqn:HpctxDx0; try contradiction.
              destruct (RD RbaseD (fold_right Rrespects rg x)
                           (fold_right (typ2 (F:=RFun)) t x1)); try contradiction.
              specialize (H5 _ eq_refl).
              destruct (pctxD cs') eqn:HpctxDcs'; try assumption.
              forward_reason.
              rewrite H5.
              split.
              { etransitivity; eauto. }
              { intros.
                repeat (gather_facts; try (eapply pctxD_SubstMorphism; eauto; [ ])).
                eapply Pure_pctxD; eauto.
                revert H8. clear.
                intros. eapply H0. eapply H. } }
            { eapply rwOk in H6; eauto.
              specialize (H6 H2).
              destruct H6. split; auto.
              intros.
              specialize (H6 _ _ H7).
              specialize (fun ts => H4 ts _ _ H7).
              specialize (H5 _ _ _ H7).
              destruct (pctxD cs) eqn:HpctxD_cs; trivial.
              destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t
                               (apps e (map fst es)))
                       eqn:Hlambda_exprD_apps_e_es; trivial.
              destruct (apps_lambda_exprD_fold_type _ _ _ _ _ _ Hlambda_exprD_apps_e_es).
              forward_reason.
              specialize (H4 x1).
              rewrite H8 in *.
              forwardy.
              specialize (H5 _ _ _ _ eq_refl H8 H11).
              rewrite H4 in *.
              rewrite H8 in *.
              forwardy.
              forward_reason.
              revert H6.
              simpl ProgressD in *.
              Cases.rewrite_all_goal.
              intros; forwardy.
              forward_reason.
              Cases.rewrite_all_goal.
              split; [ reflexivity | ].
              intros; gather_facts.
              eapply Pure_pctxD; eauto. } } }
        { destruct H0. clear H2.
          eapply rwOk; eauto. } }
      { consider (reflexive rg); intros.
        { inversion H2; clear H2; subst.
          split; eauto. intros.
          specialize (reflexiveOk _ H0 H2).
          simpl ProgressD in *.
          destruct (pctxD cs') eqn:HpctxDcs'; trivial.
          destruct (lambda_exprD (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))); trivial.
          split.
          { reflexivity. }
          { intros. eapply Pure_pctxD; eauto. } }
        { inversion H2. } }
    Time Qed.

    Theorem bottom_up_sound
    : setoid_rewrite_spec bottom_up.
    Proof using RSymOk_func RTypeOk_typD RbaseD_single_type Typ2Ok_Fun
          reflexiveOk respectfulOk rwOk transitiveOk.
      intros. red. eapply bottom_up_sound_lem.
    Qed.

(*
    Fixpoint top_down (f : nat) (e : expr typ func) (r : R) {struct f}
    : option (expr typ func) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
             (rw_bind (rw (apps e es) r)
                      (fun e' =>
                         if transitive r then
                           match f with
                             | 0 => rw_ret e'
                             | S f => top_down f e' r
                           end
                         else
                           rw_ret e'))
             match respectful e r with
	       | None => if reflexive r then rw_ret (apps e es) else rw_fail
	       | Some rs =>
	         rw_orelse
                   (recursive_rewrite e efs rs)
		            (fun e' => rw_ret (apps e es')))
                   (if reflexive r then rw_ret (apps e es) else rw_fail)
	     end)
        e nil r.
*)
  End top_bottom.


  (** This should probably go somewhere else **)
  Section the_tactic.

    Definition lem_rewriter : Type :=
      expr typ func -> R -> mrw (Progressing (expr typ func)).
    Definition respectful_dec : Type :=
      expr typ func -> R -> mrw (list R).

  Definition auto_setoid_rewrite_bu
             (r : R)
             (reflexive : refl_dec R)
             (transitive : trans_dec R)
             (rewriter : lem_rewriter)
             (respectful : respectful_dec)
  : rtac typ (expr typ func) :=
    let rw := bottom_up reflexive transitive rewriter respectful in
    fun tus tvs nus nvs ctx cs g =>
      match @rw g r nil tus tvs nus nvs ctx cs with
      | None => Fail
      | Some (Progress g', cs') => More_ cs' (GGoal g')
      | Some (NoProgress, cs') => Fail
      end.

  Variable R_impl : R.

  Hypothesis R_impl_is_impl
    : RD RbaseD R_impl (typ0 (F:=Prop)) =
      Some match eq_sym (typ0_cast (F:=Prop)) in _ = t return t -> t -> Prop with
           | eq_refl => Basics.impl
           end.

  Theorem auto_setoid_rewrite_bu_sound
  : forall is_refl is_trans rw proper
           (His_reflOk : refl_dec_ok (RD RbaseD) is_refl)
           (His_transOk : trans_dec_ok (RD RbaseD) is_trans),
      setoid_rewrite_spec rw ->
      respectful_spec proper ->
      rtac_sound (auto_setoid_rewrite_bu (Rflip R_impl)
                                         is_refl is_trans rw proper).
  Proof using RSymOk_func RTypeOk_typD R_impl_is_impl
        RbaseD_single_type Typ2Ok_Fun.
    intros. unfold auto_setoid_rewrite_bu. red.
    intros.
    generalize (@bottom_up_sound is_refl is_trans rw proper
                                 His_reflOk His_transOk H H0 g (Rflip R_impl) ctx s nil).
    simpl.
    destruct (bottom_up is_refl is_trans rw proper g (Rflip R_impl) nil
      (getUVars ctx) (getVars ctx) (length (getUVars ctx))
      (length (getVars ctx)) s).
    { destruct p. destruct p; subst; eauto using rtac_spec_Fail.
      red. intros Hbus ? ?.
      specialize (Hbus _ _ eq_refl H2).
      forward_reason.
      split; try assumption.
      split; [ constructor | ].
      specialize (H4 (typ0 (F:=Prop))).
      rewrite R_impl_is_impl in H4.
      specialize (H4 _ eq_refl).
      revert H4.
      destruct (pctxD s) eqn:HpctxDs; try (clear; tauto).
      simpl. unfold propD. unfold exprD_typ0.
      simpl.
      destruct (lambda_exprD (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) g);
        try solve [ tauto ].
      destruct (pctxD c) eqn:HpctxDc; try solve [ tauto ].
      destruct (lambda_exprD (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) new_val);
        try solve [ tauto ].
      destruct 1; split; try assumption.
      intros.
      gather_facts.
      eapply Pure_pctxD; eauto.
      intros.
      specialize (H5 Hnil). simpl in *.
      revert H6 H5. autorewrite_with_eq_rw.
      clear. generalize (typ0_cast (F:=Prop)).
      generalize dependent (typD (typ0 (F:=Prop))).
      do 4 intro. subst. simpl.
      unfold flip, Basics.impl. tauto. }
    { subst. intro. clear.
      eapply rtac_spec_Fail. }
  Qed.

  End the_tactic.

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

Arguments NoProgress {_}.
Arguments Progress {_} _.
Arguments lem_rewriter typ func Rbase : clear implicits.
Arguments respectful_dec typ func Rbase : clear implicits.

Export MirrorCore.Lambda.RewriteRelations.