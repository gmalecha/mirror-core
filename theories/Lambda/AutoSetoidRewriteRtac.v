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
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

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
          , exprD' tus (tvs' ++ tvs) t e
          , pctxD cs'
          , exprD' tus (tvs' ++ tvs) t (ProgressD e e')
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
          , exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) e
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
    Proof.
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
          rewrite exprD'_Abs; eauto with typeclass_instances.
          rewrite typ2_match_iota; eauto with typeclass_instances.
          unfold Monad.bind, Monad.ret; simpl.
          autorewrite with eq_rw.
          destruct (type_cast x t) eqn:Htcxt; trivial.
          simpl in *.
          destruct (exprD' (getUVars ctx) (t :: tvs' ++ getVars ctx) x0 e)
                   eqn:HexprDe; trivial.
          forwardy. forward_reason.
          rewrite H1.
          destruct p.
          { simpl ProgressD in *.
            rewrite exprD'_Abs; eauto with typeclass_instances.
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
            rewrite exprD'_Abs; eauto with typeclass_instances.
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
    Proof.
      intros. eapply setoid_rewrite'_sound.
      constructor.
    Qed.

  End setoid_rewrite.

(*
  Definition refl_dec : Type := R -> bool.
  Definition trans_dec : Type := R -> bool.
  Definition refl_dec_ok (rd : refl_dec) : Prop :=
    forall r t rD, rd r = true -> RD RbaseD r t = Some rD -> Reflexive rD.
  Definition trans_dec_ok (rd : trans_dec) : Prop :=
    forall r t rD, rd r = true -> RD RbaseD r t = Some rD -> Transitive rD.
*)

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
    Lemma exprD'_App
    : forall tus tvs td tr f x fD xD,
        exprD' tus tvs (typ2 (F:=RFun) td tr) f = Some fD ->
        exprD' tus tvs td x = Some xD ->
        exprD' tus tvs tr (App f x) = Some (AbsAppI.exprT_App fD xD).
    Proof using Typ2Ok_Fun RSymOk_func RTypeOk_typD.
      intros.
      autorewrite with exprD_rw; simpl.
      erewrite exprD_typeof_Some by eauto.
      rewrite H. rewrite H0. reflexivity.
    Qed.

    Lemma exprD'_Abs_prem
      : forall tus tvs t t' x xD,
        ExprDsimul.ExprDenote.exprD' tus tvs t (Abs t' x) = Some xD ->
        exists t'' (pf : typ2 t' t'' = t) bD,
          ExprDsimul.ExprDenote.exprD' tus (t' :: tvs) t'' x = Some bD /\
          xD = match pf with
               | eq_refl => AbsAppI.exprT_Abs bD
               end.
    Proof using tyArr Typ2Ok_Fun RSymOk_func RTypeOk_typD.
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
    Proof using RTypeOk_typD Typ2Ok_Fun RbaseD_single_type.
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
              exprD' tus (tvs' ++ tvs) t (apps f (map fst es)) = Some eD ->
              exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f = Some fD ->
              RD RbaseD (fold_right Rrespects r rs) (fold_right (typ2 (F:=RFun)) t ts) = Some rD ->
              match pctxD cs
                  , exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f'
                  , pctxD cs'
              with
              | Some csD , Some fD' , Some csD' =>
                exists eD',
                exprD' tus (tvs' ++ tvs) t (ProgressD (apps f' (map fst es)) e') = Some eD' /\
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
    Proof using tyArr RTypeOk_typD Typ2Ok_Fun RSymOk_func Typ0_Prop
          RelDec_Correct_eq_typ (* Rbase_eq_ok *) RbaseD_single_type.
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
          consider (ExprDsimul.ExprDenote.exprD'
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
          destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t f'); trivial.
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
            destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx)
                             (typ2 t0 (fold_right (typ2 (F:=RFun)) t ts)) f')
                     eqn:HexprD'f'; trivial.
            specialize (H1 _ _ _ H2 ts).
            red in x4.
            rewrite exprD'_apps in H3 by eauto with typeclass_instances.
            unfold apps_sem' in H3.
            generalize (exprD'_typeof_expr _ (or_introl H4)).
            intro Htypeof_f.
            simpl in H3. rewrite Htypeof_f in H3.
            forwardy.
            unfold type_of_apply in H9.
            rewrite typ2_match_iota in H9 by eauto with typeclass_instances.
            autorewrite_with_eq_rw_in H9. forwardy.
            red in y4. inv_all. subst. clear H9.
            assert (x5 = y1).
            { eapply exprD_typeof_eq; eauto. }
            destruct (typ2_inj _ _ _ _ x4).
            red in H11; red in H13; subst.
            rewrite H12 in *.
            forwardy.
            revert H1.
            Cases.rewrite_all_goal.
            rewrite H7 in H4; inv_all; subst.

            rewrite (exprD'_apps _ _ _
                          (getUVars ctx) (tvs' ++ getVars ctx)
                          (map fst es) (App f a_fst) t).
            unfold apps_sem'. simpl.
            rewrite Htypeof_f.
            erewrite exprD_typeof_Some by eauto.
            unfold type_of_apply.
            rewrite H6.
            rewrite type_cast_refl; eauto with typeclass_instances.
            unfold Relim.
            autorewrite_with_eq_rw.
            erewrite exprD'_App by eauto.
            rewrite H8.
            intro Hx; specialize (Hx _ _ _ eq_refl eq_refl eq_refl).
            erewrite exprD'_App in Hx by eauto.
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
              exprD' tus (tvs' ++ tvs) t (apps f (map fst es)) = Some eD ->
              exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f = Some fD ->
              RD RbaseD (fold_right Rrespects r rs) (fold_right (typ2 (F:=RFun)) t ts) = Some rD ->
              match pctxD cs
                  , exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=RFun)) t ts) f'
                  , pctxD cs'
              with
              | Some csD , Some fD' , Some csD' =>
                exists eD',
                exprD' tus (tvs' ++ tvs) t (ProgressD (apps f' (map fst es)) e') = Some eD' /\
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
    Proof using tyArr RTypeOk_typD Typ2Ok_Fun RSymOk_func Typ0_Prop
          RelDec_Correct_eq_typ RbaseD_single_type.
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
    Proof. clear Rbase_eq_ok Rbase_eq.
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
                destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es)))
                         eqn:HexprD'apps_e_es; trivial.
                specialize (fun ts fD rD => H5 _ _ _ H8 ts fD rD _ HexprD'apps_e_es).
                eapply apps_exprD'_fold_type in HexprD'apps_e_es; eauto.
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
                destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t
                                 (apps e (map fst es))) eqn:HexprD'_e; trivial.
                specialize (fun ts fD rD => H5 ts fD rD _ eq_refl).
                eapply apps_exprD'_fold_type in HexprD'_e; try assumption.
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
                destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t
                                 (apps e (map fst es))) eqn:HexprD'apps_e_es; trivial.
                specialize (H5 _ _ _ H8).
                rewrite HexprD'apps_e_es in H5.
                eapply apps_exprD'_fold_type in HexprD'apps_e_es; try assumption.
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
                destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))) eqn:HexprD'apps_e_es; trivial.
                eapply apps_exprD'_fold_type in HexprD'apps_e_es; try assumption.
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
              destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))) eqn:HexprD'apps_e_es; trivial.
              destruct (apps_exprD'_fold_type _ _ _ _ _ _ HexprD'apps_e_es).
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
              destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t
                               (apps e (map fst es)))
                       eqn:HexprD'_apps_e_es; trivial.
              destruct (apps_exprD'_fold_type _ _ _ _ _ _ HexprD'_apps_e_es).
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
          destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t (apps e (map fst es))); trivial.
          split.
          { reflexivity. }
          { intros. eapply Pure_pctxD; eauto. } }
        { inversion H2. } }
    Time Qed.

    Theorem bottom_up_sound
    : setoid_rewrite_spec bottom_up.
    Proof.
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
  Proof.
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
      simpl. unfold propD. unfold exprD'_typ0.
      simpl.
      destruct (exprD' (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) g);
        try solve [ tauto ].
      destruct (pctxD c) eqn:HpctxDc; try solve [ tauto ].
      destruct (exprD' (getUVars ctx) (getVars ctx) (typ0 (F:=Prop)) new_val);
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

  (** This starts plugins for the rewriter **)
  (******************************************)

  Definition func_sdec (a b : func) : bool :=
    match sym_eqb a b with
    | Some x => x
    | _ => false
    end.

  Definition expr_sdec : expr typ func -> expr typ func -> bool :=
    @expr_eq_sdec typ func _ func_sdec.

  Lemma expr_sdec_sound
  : forall a b : expr typ func, expr_sdec a b = true -> a = b.
  Proof.
    eapply expr_eq_sdec_ok; eauto.
    unfold func_sdec.
    intros. generalize (sym_eqbOk a b); eauto with typeclass_instances.
    destruct (sym_eqb a b); intros; subst; auto.
    inversion H.
  Qed.

  (** Apply the same rewrite multiple times while it is still making progress **)
  Section repeat_rewrite.
    Variable rw : lem_rewriter.
    Variable is_refl : refl_dec R.
    Variable is_trans : trans_dec R.

    Fixpoint repeat_rewrite' (n : nat)
             (prog : expr typ func -> Progressing (expr typ func))
             (e : expr typ func) (r : R)
    : mrw (Progressing (expr typ func)) :=
      match n with
      | 0 => if is_refl r
             then rw_ret (prog e)
             else rw_fail
      | S n => rw_bind_catch
                 (rw e r)
                 (fun e' =>
                    match e' with
                    | NoProgress =>
                      if is_refl r then rw_ret (prog e) else rw_fail
                    | Progress e' as X =>
                      if is_trans r then repeat_rewrite' n (@Progress _) e' r
                      else rw_ret X
                    end)
                 (if is_refl r
                  then rw_ret (prog e)
                  else rw_fail)
      end.

    Hypothesis rw_sound : setoid_rewrite_spec rw.
    Hypothesis is_reflOk : refl_dec_ok (RD RbaseD) is_refl.
    Hypothesis is_transOk : trans_dec_ok (RD RbaseD) is_trans.

    Lemma repeat_rewrite'_mono : forall n e r c A B C D E F X Y,
        repeat_rewrite' (c:=c) n (@Progress _) e r A B C D E F = Some (X,Y) ->
        X <> NoProgress.
    Proof using.
      induction n; simpl.
      { intros. destruct (is_refl r). inversion H. congruence. inversion H. }
      { intros.
        eapply rw_bind_catch_case in H. destruct H; forward_reason.
        { destruct x.
          { destruct (is_trans r); eauto.
            inversion H0. congruence. }
          { destruct (is_refl r).
            { inversion H0; congruence. }
            { inversion H0. } } }
        { destruct (is_refl r).
          { inversion H; congruence. }
          { inversion H. } } }
    Qed.

    Theorem repeat_rewrite'_sound
    : forall n (prog : bool),
        setoid_rewrite_spec (repeat_rewrite' n (if prog then @Progress _ else (fun _ => NoProgress))).
    Proof.
      induction n.
      { intros. simpl. destruct prog.
        { do 2 red. intros.
          specialize (@is_reflOk r).
          destruct (is_refl r).
          { inversion H; clear H; subst.
            split; auto.
            intros.
            eapply is_reflOk in H; trivial.
            simpl.
            forward.
            split; [ reflexivity | ].
            intros. eapply Pure_pctxD; eauto. }
          { inversion H. } }
        { do 2 red; intros.
          specialize (@is_reflOk r).
          destruct (is_refl r).
          { inversion H; clear H; subst.
            split; auto.
            intros.
            eapply is_reflOk in H; eauto.
            simpl. forward.
            split; [ reflexivity | ].
            intros; eapply Pure_pctxD; eauto. }
          { inversion H. } } }
      { simpl. do 2 red; intros.
        eapply rw_bind_catch_case in H; destruct H; forward_reason.
        { eapply rw_sound in H.
          forward_reason. destruct x.
          { specialize (@is_transOk r).
            destruct (is_trans r).
            { generalize (repeat_rewrite'_mono _ _ _ _ _ _ _ _ _ H1).
              eapply (IHn true) in H1.
              forward_reason. split; auto.
              intros.
              specialize (H3 _ _ H5).
              specialize (H2 _ _ H5).
              simpl in *.
              forward.
              forward_reason.
              destruct e'; simpl in *.
              { Cases.rewrite_all_goal.
                split; [ reflexivity | ].
                intros. gather_facts.
                eapply pctxD_SubstMorphism; [ | | eassumption | ]; eauto.
                gather_facts.
                eapply is_transOk in H5; eauto.
                eapply Pure_pctxD; eauto. }
              { congruence. } }
            { inversion H1; clear H1; subst.
              simpl in *. split; auto. } }
          { specialize (@is_reflOk r).
            destruct (is_refl r); [ | inversion H1 ].
            inversion H1; clear H1; subst.
            split; auto.
            intros. specialize (H2 _ _ H1).
            forward. destruct prog; simpl in *.
            { rewrite H5. forward_reason.
              split; auto. }
            { rewrite H5; forward_reason; auto. } } }
        { specialize (@is_reflOk r).
          destruct (is_refl r); [ | inversion H ].
          inversion H; clear H; subst.
          split; auto.
          intros.
          forward.
          cutrewrite (ProgressD e
                                ((if prog then (@Progress _)
                                  else fun _ : expr typ func => NoProgress) e) = e);
            [ | destruct prog; reflexivity ].
          rewrite H3; forward_reason.
          split; [ reflexivity | ].
          eapply is_reflOk in H; eauto.
          eapply Pure_pctxD; eauto. } }
    Qed.

    Definition repeat_rewrite (progress : bool) : nat -> lem_rewriter :=
      let prog := if progress then @Progress _ else (fun _ => NoProgress) in
      fun n =>
        repeat_rewrite' n prog.

    Theorem repeat_rewrite_sound
    : forall b n, setoid_rewrite_spec (repeat_rewrite b n).
    Proof.
      unfold repeat_rewrite. simpl. intros.
      eapply repeat_rewrite'_sound.
    Qed.

  End repeat_rewrite.

  Section core_rewrite.
    (* This is the implementation of rewriting a single lemma *)
    (** Note, this is quite inefficient due to building and destructing
     ** the pair
     **)
    Fixpoint extend_ctx (tvs' : tenv typ)
             (ctx : Ctx typ (expr typ func)) (cs : ctx_subst ctx) {struct tvs'}
    : { ctx : Ctx typ (expr typ func) & ctx_subst ctx } :=
      match tvs' with
      | nil => @existT _ _ ctx cs
      | t :: tvs' =>
        match @extend_ctx tvs' ctx cs with
        | existT _ ctx' cs' => @existT _ _ (CAll ctx' t) (AllSubst cs')
        end
      end.

    Require Import MirrorCore.RTac.SolveK.

    (** TODO(gmalecha): This is not a nice interface because it is not
     ** a standard rewriter for two reasons:
     ** 1) It assumes that tvs' = nil, and
     ** 2) It assumes that the relation is the same as the relation for
     **    the lemma.
     **)
    Definition core_rewrite (lem : rw_lemma typ func Rbase)
               (tac : rtacK typ (expr typ func))
    : expr typ func -> tenv typ -> tenv typ -> nat -> nat ->
      forall c : Ctx typ (expr typ func),
        ctx_subst c -> option (expr typ func * ctx_subst c) :=
        match typeof_expr nil lem.(vars) lem.(concl).(lhs) with
        | None => fun _ _ _ _ _ _ _ => None
        | Some t =>
          fun e tus tvs nus nvs ctx cs =>
           let ctx' := CExs ctx lem.(vars) in
           let cs' : ctx_subst ctx' := ExsSubst cs (amap_empty _) in
           let tus' := tus ++ lem.(vars) in
           match
             exprUnify 10 tus' tvs 0 (vars_to_uvars 0 nus lem.(concl).(lhs))
                       e t cs'
           with
           | None => None
           | Some cs'' =>
             let prems :=
                 List.map (fun e => GGoal (vars_to_uvars 0 nus e)) lem.(premises)
             in
             match
               (SOLVEK tac) tus' tvs (length lem.(vars) + nus) nvs ctx' cs'' (GConj_list prems)
             with
             | Solved cs''' =>
               match cs''' in ctx_subst ctx
                     return match ctx with
                            | CExs z _ => option (expr typ func * ctx_subst z)
                            | _ => unit
                            end
               with
               | ExsSubst cs'''' sub =>
		 if amap_is_full (length lem.(vars)) sub then
                   let res :=
                       instantiate (fun u => amap_lookup u sub) 0
                                   (vars_to_uvars 0 nus lem.(concl).(rhs))
                   in
                   Some (res, cs'''')
                 else
                   None
               | _ => tt
               end
             | _ => None
             end
           end
        end.

    (** TODO: Move **)
    Lemma exprD'_weakenV
    : forall (tus tvs : tenv typ) (e : expr typ func) (t : typ)
             (val : exprT tus tvs (typD t)) (tvs' : list typ),
        exprD' tus tvs t e = Some val ->
        exists val' : exprT tus (tvs ++ tvs') (typD t),
          exprD' tus (tvs ++ tvs') t e = Some val' /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs)
                  (vs' : hlist typD tvs'),
              val us vs = val' us (hlist_app vs vs')).
    Proof.
      intros.
      generalize (@exprD'_weakenV typ _ (expr typ func) _ _ tus tvs tvs' e t val H).
      eauto.
    Qed.

    (** TODO: Move **)
    Lemma exprD'_weakenU
    : forall (tus tvs : tenv typ) (e : expr typ func) (t : typ)
             (val : exprT tus tvs (typD t)) (tus' : list typ),
        exprD' tus tvs t e = Some val ->
        exists val' : exprT (tus ++ tus') tvs (typD t),
          exprD' (tus ++ tus') tvs t e = Some val' /\
          (forall (us : hlist typD tus) (vs : hlist typD tvs)
                  (us' : hlist typD tus'),
              val us vs = val' (hlist_app us us') vs).
    Proof.
      intros.
      generalize (@exprD'_weakenU typ _ (expr typ func) _ _ tus tus' tvs e t val H).
      eauto.
    Qed.

    Local Instance Subst_amap T : Subst (amap T) T :=
      FMapSubst.SUBST.Subst_subst T.
    Local Instance SubstOk_amap : SubstOk (amap (expr typ func)) typ (expr typ func) :=
      @FMapSubst.SUBST.SubstOk_subst typ _ (expr typ func) _.

    Opaque instantiate.

    Lemma core_rewrite_lemma
    : forall (ctx : Ctx typ (expr typ func)) (t0 : typ)
               (x12 : amap (expr typ func)) (x13 : ctx_subst ctx)
               (l : list typ) (y0 : exprT (getUVars ctx) l (typD t0)),
        WellFormed_entry x13 (length l) x12 ->
        forall (e : expr typ func) (t : tenv typ)
               (y3 : exprT (getUVars ctx ++ l) t Prop)
               (x5 : hlist (fun t1 : typ => exprT (getUVars ctx) t (typD t1)) l),
          amap_substD (getUVars ctx ++ l) t x12 = Some y3 ->
          amap_is_full (length l) x12 = true ->
          (forall (us : hlist typD (getUVars ctx)) (vs : hlist typD t),
              let us' :=
                  hlist_map
                    (fun (t1 : typ) (x : exprT (getUVars ctx) t (typD t1)) => x us vs) x5
              in
              y3 (hlist_app us us') vs) ->
          exprD' (getUVars ctx) l t0 e = Some y0 ->
          exists e'D : exprT (getUVars ctx) t (typD t0),
            exprD' (getUVars ctx) t t0
                   (instantiate (fun u : ExprI.uvar => amap_lookup u x12) 0
                                (vars_to_uvars 0 (length (getUVars ctx)) e)) =
            Some e'D /\
            (forall (us : hlist typD (getUVars ctx)) (vs : hlist typD t),
                e'D us vs =
                y0 us
                   (hlist_map
                      (fun (t1 : typ) (x6 : exprT (getUVars ctx) t (typD t1)) =>
                         x6 us vs) x5)).
    Proof using RType_typD RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      intros ctx t0 x12 x13 l y0 H40 e t y3 x5 Hamap_substD H4 H H13.
      generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ e nil t0 l _ H13).
      destruct 1 as [ ? [ ? ? ] ].
      eapply ExprI.exprD'_weakenV with (tvs':=t) in H0; eauto with typeclass_instances.
      destruct H0 as [ ? [ ? ? ] ].
      destruct (@instantiate_sound typ (expr typ func) _ _ _ (getUVars ctx++l) t
                                   (fun u : ExprI.uvar => amap_lookup u x12)
                                   (vars_to_uvars 0 (length (getUVars ctx)) e) nil t0 x0 y3).
      { generalize (@sem_preserves_if_substD (amap (expr typ func)) typ (expr typ func) RType_typD Expr_expr _ _).
        simpl. intro. eapply H3.
        2: eapply Hamap_substD.
        eapply WellFormed_entry_WellFormed_pre_entry in H40.
        destruct H40. assumption. }
      { eassumption. }
      { destruct H3.
        eapply exprD'_strengthenU_multi in H3.
        2: eauto with typeclass_instances.
        { destruct H3 as [ ? [ ? ? ] ].
          eexists; split; try eassumption.
          intros.
          specialize (H us vs).
          specialize (H5 _ _ Hnil H).
          simpl in *.
          symmetry.
          etransitivity; [ eapply (H1 _ _ Hnil) | ].
          etransitivity; [ eapply H2 | ].
          etransitivity; [ eapply H5 | ].
          eapply H6. }
        { intros.
          clear H2 H1 H3 H5 H.
          match goal with
          | |- ?X = _ => consider X; try reflexivity; intro
          end.
          exfalso.
          eapply mentionsU_instantiate in H.
          assert (amap_lookup (length (getUVars ctx) + u) x12 <> None).
          { clear - H4 H40 H6.
            destruct H40.
            clear H0.
            red in H.
            destruct H as [ ? [ ? ? ] ].
            clear H H1.
            generalize dependent (length (getUVars ctx)).
            generalize dependent (length l).
            intros.
            eapply pigeon_principle; eauto. }
          destruct H.
          { destruct H. eauto. }
          { destruct H. destruct H. destruct H as [ ? [ ? ? ] ].
            destruct H40.
            consider (amap_lookup (length (getUVars ctx) + u) x12); intros; try congruence.
            eapply FMapSubst.SUBST.normalized_fmapsubst in H1.
            3: eapply H.
            cut (true = false); [ clear; intros; congruence | ].
            rewrite <- H3. rewrite <- H1. reflexivity.
            destruct H5. assumption. } } }
    Qed.

    (* TODO(gmalecha): This is not a nice interface! *)
    Theorem core_rewrite_sound
    : forall ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall l0 r0 e e' cs',
          WellFormed_rtacK r0 ->
          core_rewrite l0 r0 e tus tvs (length tus) (length tvs) cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (Hlem : lemmaD (rw_conclD RbaseD) nil nil l0)
                  (Hrtac :           rtacK_sound r0),
           forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD (rel (concl l0)) t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match exprD' tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match exprD' tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                               rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof using RelDec_Correct_eq_typ RbaseD_single_type
          RTypeOk_typD RSymOk_func Typ2Ok_Fun tyArr.
      Opaque vars_to_uvars.
      unfold core_rewrite. generalize dependent 10.
      simpl.
      intros.
      consider (typeof_expr nil l0.(vars) l0.(concl).(lhs)); intros.
      { match goal with
        | H : match ?X with _ => _ end = _ |- _ =>
          consider X; intros
        end; try match goal with
                 | H : None = Some _ |- _ => exfalso ; clear - H ; inversion H
                 end.
        assert (WellFormed_rtacK (SOLVEK r0)).
        { apply WF_SOLVEK. assumption. }
        clear H; rename H4 into H.
        match goal with
        | Hrt : WellFormed_rtacK ?X , _ : match ?X _ _ _ _ ?C ?CS ?G with _ => _ end = _ |- _ =>
          specialize (@Hrt C CS G _ eq_refl)
        end.
        match goal with
        | Hrt : rtacK_spec_wf _ _ ?X , H : match ?Y with _ => _ end = _ |- _ =>
          replace Y with X in H ; [ destruct X eqn:?; intros | f_equal ]
        end; try congruence.
        2: clear; simpl; repeat rewrite app_length; simpl; omega.
        rewrite (ctx_subst_eta c0) in H3.
        repeat match goal with
               | H : match ?X with _ => _ end = _ |- _ =>
                 let H' := fresh in
                 destruct X eqn:H'; [ | solve [ exfalso; clear - H3; inversion H3 ] ]
               end.
        inv_all. subst.
        destruct (@exprUnify_sound (ctx_subst (CExs ctx (vars l0))) typ func _ _ _ _ _ _ _ _ _ _ n
                                   _ _ _ _ _ _ _ nil H2).
        { constructor; eauto using WellFormed_entry_amap_empty. }
        split.
        { red in H.
          assert (WellFormed_Goal (getUVars (CExs ctx (vars l0)))
                                  (getVars (CExs ctx (vars l0)))
                                  (GConj_list
                                     (map
                                        (fun e : expr typ func =>
                                           GGoal (vars_to_uvars 0 (length (getUVars ctx)) e))
                                        (premises l0)))).
          { eapply WellFormed_Goal_GConj_list. clear.
            induction (premises l0); simpl.
            - constructor.
            - constructor; eauto. constructor. }
          specialize (H H6 H3); clear H6.
          rewrite (ctx_subst_eta c0) in H.
          inv_all. auto. }
        clear H. intro. intro H.
        assert (rtacK_sound (SOLVEK r0)).
        { apply SOLVEK_sound. assumption. }
        clear H; rename H6 into H.
        intros.
        destruct (pctxD cs) eqn:HpctxDcs; trivial.
        destruct (exprD' (getUVars ctx) (getVars ctx) t0 e) eqn:HexprD'e; trivial.
        simpl in *.
        eapply lemmaD_lemmaD' in Hlem. forward_reason.
        eapply lemmaD'_weakenU with (tus':=getUVars ctx) in H7;
          eauto using ExprOk_expr, rw_concl_weaken.
        simpl in H7. forward_reason.
        unfold lemmaD' in H7.
        forwardy. inv_all. subst.
        unfold rw_conclD in H10.
        forwardy. inv_all; subst.
        assert (t0 = t).
        { revert H0.
          assert (y1 = t0).
          { eapply RD_single_type; eauto. }
          subst t0.
          intro.
          eapply ExprFacts.typeof_expr_weaken with (tus':=getUVars ctx) (tvs':=nil) in H0; eauto.
          simpl in H0. rewrite H10 in H0. inv_all; auto. }
        subst.
        assert (y1 = t).
        { revert H13. revert H6.
          intros. eapply RD_single_type; eauto. }
        subst t. rename y1 into t.
        generalize (fun tus tvs e t => @ExprI.exprD'_conv typ _ (expr typ func)
                                          _ tus tus (tvs ++ nil) tvs e t eq_refl
                                          (eq_sym (app_nil_r_trans _))). simpl.
        intro HexprD'_conv.
        rewrite HexprD'_conv in H12. autorewrite_with_eq_rw_in H12.
        rewrite HexprD'_conv in H11. autorewrite_with_eq_rw_in H11.
        forwardy. inv_all. subst.

        generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ _ nil _ _ _ H11).
        simpl. destruct 1 as [ ? [ HexprD'e_subst ? ] ].
        eapply exprD'_weakenV with (tvs':=getVars ctx) in HexprD'e_subst; eauto.
        simpl in HexprD'e_subst. forward_reason.
        intros; subst.
        replace (length (getUVars ctx ++ t :: nil))
           with (S (length (getUVars ctx))) in H15
             by (rewrite app_length; simpl; omega).
        eapply exprD'_weakenU
          with (tus':=l0.(vars)) in HexprD'e; eauto.
        destruct (drop_exact_append_exact (vars l0) (getUVars ctx)) as [ ? [ Hx ? ] ].
        rewrite Hx in *; clear Hx.
        destruct (pctxD_substD H1 HpctxDcs) as [ ? [ Hx ? ] ].
        rewrite Hx in *; clear Hx.
        destruct HexprD'e as [ ? [ Hx ? ] ].
        specialize (H5 _ _ _ H15 Hx eq_refl).
        clear Hx.
        forward_reason.
        generalize (pctxD_SubstMorphism_progress H5).
        simpl. rewrite HpctxDcs.
        intro Hx; specialize (Hx _ eq_refl). destruct Hx.
        red in H.
        replace (getUVars ctx ++ vars l0)
           with (getUVars (CExs ctx (vars l0)))
             in Heqr
             by reflexivity.
        eapply (H (CExs ctx (vars l0))) in Heqr. red in Heqr.
        destruct Heqr; eauto.
        { clear. induction (premises l0); simpl. constructor.
          destruct l; simpl. constructor.
          constructor. constructor. eauto. }
        rewrite H22 in *.
        assert (exists Ps,
                   goalD (getUVars ctx ++ vars l0) (getVars ctx)
                         (GConj_list
                            (map
                               (fun e2 : expr typ func =>
                                  GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                               (premises l0))) = Some Ps /\
                   forall (us : hlist typD (getUVars ctx)) us' vs,
                     Ps (hlist_app us us') vs <->
                     Forall (fun y => y us (hlist_app us' Hnil)) y).
        { revert H7.
          destruct l0. simpl in *.
          clear - RTypeOk_typD RSymOk_func Typ2Ok_Fun.
          intros.
          cut (exists Ps : exprT (getUVars ctx ++ vars) (getVars ctx) Prop,
                  goalD (getUVars ctx ++ vars) (getVars ctx)
                        (GConj_list_simple
                           (map
                              (fun e2 : expr typ func =>
                                 GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                              premises)) = Some Ps /\
                  (forall (us : hlist typD (getUVars ctx)) (us' : hlist typD vars)
                          (vs : hlist typD (getVars ctx)),
                      Ps (hlist_app us us') vs <->
                      Forall
                        (fun
                            y0 : hlist typD (getUVars ctx) ->
                                 hlist typD (vars ++ nil) -> Prop =>
                            y0 us (hlist_app us' Hnil)) y)).
          { destruct (goalD_GConj_list_GConj_list_simple
                        (getUVars ctx ++ vars) (getVars ctx)
                        (map (fun e2 : expr typ func =>
                                GGoal (vars_to_uvars 0 (length (getUVars ctx)) e2))
                           premises)).
            { intros; forward_reason; congruence. }
            { intros; forward_reason.
              inv_all. subst. eexists; split; eauto.
              intros.
              rewrite <- H1. eapply H.
              reflexivity. reflexivity. } }
          revert H7. revert y.
          induction premises; simpl; intros.
          { eexists; split; eauto.
            simpl. inv_all. subst.
            split; eauto. }
          { simpl in *.
            forwardy. inv_all. subst.
            unfold exprD'_typ0 in H.
            simpl in H. forwardy.
            generalize (@vars_to_uvars_sound typ (expr typ func) _ _ _ _ _ _ _ _ nil _ _ _ H).
            intro. forward_reason.
            unfold propD, exprD'_typ0.
            simpl in H2.
            eapply exprD'_weakenV
              with (tvs':=getVars ctx)
                in H2; eauto.
            forward_reason. simpl in H2.
            generalize (@exprD'_conv typ _ (expr typ func) _); eauto. simpl.
            intro Hx.
            rewrite Hx
               with (pfu:=f_equal _ (eq_sym (app_nil_r_trans _))) (pfv:=eq_refl)
                 in H2.
            autorewrite_with_eq_rw_in H2.
            forwardy.
            rewrite H2.
            specialize (IHpremises _ H0).
            forward_reason. rewrite H6.
            eexists; split; eauto. simpl.
            intros.
            inv_all. subst.
            intros. rewrite Forall_cons_iff.
            rewrite <- (H7 _ _ vs).
            autorewrite with eq_rw.
            specialize (H3 us (hlist_app us' Hnil) Hnil).
            simpl in *.
            rewrite H3; clear H3.
            erewrite (H4 (hlist_app us (hlist_app us' Hnil)) Hnil vs); clear H4.
            simpl. rewrite hlist_app_nil_r.
            unfold f_equal.
            autorewrite with eq_rw.
            clear.
            generalize (app_nil_r_trans vars).
            generalize dependent (vars ++ nil).
            intros; subst. reflexivity. } }
        destruct H25 as [ ? [ Hx ? ] ].
        change_rewrite Hx in H24; clear Hx.
        forwardy.
        rewrite (ctx_subst_eta c0) in H24.
        simpl in H24.
        forwardy. rewrite H27.
        inv_all; subst.
        destruct (amap_substD_amap_empty (getUVars ctx ++ vars l0)
                                         (getVars ctx)) as [ ? [ Hx ? ] ].
          change_rewrite Hx in H5; clear Hx.
        rewrite HpctxDcs in H5.
        simpl in *.
        destruct (drop_exact_append_exact l0.(vars) (getUVars ctx)) as [ ? [ Hx ? ] ];
          rewrite Hx in *; clear Hx.
        destruct H26.
        inv_all. subst.
        forwardy.
        repeat match goal with
               | H : ?X = _ , H' : ?X = _ |- _ => rewrite H in H'
               end.
        forward_reason; inv_all; subst.
        simpl in *.
        rewrite H5 in *.
        rewrite H3 in *.
        rewrite H27 in *.
        rewrite H24 in *.
        inv_all.
        forwardy.
        generalize H24. intro Hamap_substD.
        eapply subst_getInstantiation in H24;
          eauto using WellFormed_entry_WellFormed_pre_entry
                 with typeclass_instances.
        destruct H24.
        assert (exists e'D,
                   exprD' (getUVars ctx) (getVars ctx) t
                          (instantiate (fun u : ExprI.uvar => amap_lookup u x12)
                                       0 (vars_to_uvars 0 (length (getUVars ctx)) l0.(concl).(rhs))) = Some e'D /\
                   forall us vs,
                     e'D us vs =
                     y0 us (hlist_map
                              (fun (t : typ) (x6 : exprT (getUVars ctx) (getVars ctx) (typD t)) =>
                                 x6 us vs) x5)).
        { eapply core_rewrite_lemma; eauto. }
        destruct H20 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
        split.
        { etransitivity; eassumption. }
        intros.
        eapply pctxD_substD' with (us:=us) (vs:=vs) in H38; eauto with typeclass_instances.
        gather_facts.
        eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
        gather_facts.
        eapply pctxD_SubstMorphism; [ | | eauto | ]; eauto.
        gather_facts.
        eapply Pure_pctxD; eauto. intros.
        specialize (H20 us0 vs0).
        specialize (H6 us0 vs0).
        generalize dependent (hlist_map
           (fun (t : typ) (x6 : exprT (getUVars ctx) (getVars ctx) (typD t)) =>
            x6 us0 vs0) x5); simpl; intros.
        rewrite H20; clear H20.
        generalize H6.
        eapply H24 in H6; clear H24.
        specialize (H29 us0 h).
        clear - H19 H16 H14 H17 H25 H28 H21 H9 H18 H22 H23 H26 H6 H8 H29.
        eapply H9 in H8; clear H9.
        rewrite foralls_sem in H8.
        specialize (H8 h).
        setoid_rewrite impls_sem in H8.
        rewrite Quant._forall_sem in H26.
        repeat match goal with
               | H : (forall x : hlist _ _ , _) , H' : hlist _ _ |- _ =>
                 specialize (H H')
               end.
        specialize (H16 (hlist_app us0 h) Hnil vs0).
        specialize (H21 (hlist_app us0 h) vs0).
        rewrite H19; clear H19.
        rewrite H29 in *; clear H29.
        destruct H21; auto.
        specialize (H0 Hnil). simpl in H0.
        rewrite <- H0; clear H0.
        simpl in *.
        rewrite <- H16; clear H16.
        rewrite <- H14; clear H14.
        simpl.
        revert H8.
        instantiate (1:= us0).
        autorewrite_with_eq_rw.
        rewrite hlist_app_nil_r.
        autorewrite_with_eq_rw.
        intros. apply H8; clear H8.
        eapply List.Forall_map.
        eapply H26 in H0; clear H26.
        eapply H25 in H0; clear H25.
        revert H0.
        eapply Forall_impl. clear.
        intros.
        rewrite <- hlist_app_nil_r.
        assumption. }
      { exfalso; clear - H2; inversion H2. }
    Time Qed.

    Theorem core_rewrite_soundX
    : forall ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall l0 r0 e e' cs'
          (Hlem  : lemmaD (rw_conclD RbaseD) nil nil l0)
          (Hrtac : rtacK_sound r0),
          core_rewrite l0 r0 e tus tvs (length tus) (length tvs) cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD (rel (concl l0)) t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match exprD' tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match exprD' tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                               rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof using RelDec_Correct_eq_typ RbaseD_single_type
          RTypeOk_typD RSymOk_func Typ2Ok_Fun tyArr.
      Opaque vars_to_uvars.
      intros.
      eapply core_rewrite_sound in H; eauto using rtacK_sound_WellFormed_rtacK.
      forward_reason.
      split; eauto.
    Qed.

  End core_rewrite.

  (* This section implements the re-indexing operation
   * to run [rtac]'s from [mrw]. Note that the main thing to do
   * is extend the context with any extra variables and re-index
   * variables in the term.
   *)
  Section reindexing.
    (* This has to do with converting expressions for tactics *)
    Let _lookupU (u : ExprI.uvar) : option (expr typ func) := None.
    Let _lookupV (under : nat) (above : nat) (v : ExprI.var)
    : option (expr typ func) :=
      Some (Var (if v ?[ ge ] under
                 then v - under
                 else v + above)).

    Definition expr_convert (u : nat) (above : nat)
    : expr typ func -> expr typ func :=
      expr_subst _lookupU (_lookupV u above) 0.

    (** TODO(gmalecha): Move to EnvI or ExtLib.Data.HList **)
    Lemma nth_error_get_hlist_nth_appR'
    : forall T (F : T -> Type) ls u v,
        nth_error_get_hlist_nth F ls u = Some v ->
        forall ls',
        exists v',
          nth_error_get_hlist_nth F (ls' ++ ls) (u + length ls') = Some (existT _ (projT1 v) v') /\
          forall a b,
            projT2 v a = v' (hlist_app b a).
    Proof using.
      induction ls'.
      { simpl.
        replace (u + 0) with u by omega.
        destruct v. eexists; split; eauto.
        simpl. intros.
        rewrite (hlist_eta b). reflexivity. }
      { simpl.
        replace (u + S (length ls')) with (S (u + length ls')) by omega.
        destruct IHls' as [ ? [ ? ? ] ].
        rewrite H0. eexists; split; eauto.
        simpl. intros.
        rewrite (hlist_eta b). simpl. eauto. }
    Qed.

    Lemma expr_convert_sound
    : forall tus tvs tvs' e t eD,
        exprD' tus (tvs ++ tvs') t e = Some eD ->
        exists eD',
          exprD' tus (tvs' ++ tvs) t (expr_convert (length tvs) (length tvs') e) = Some eD' /\
          forall a b c,
            eD a (hlist_app b c) = eD' a (hlist_app c b).
    Proof.
      clear - Typ2Ok_Fun RTypeOk_typD RSymOk_func.
      unfold expr_convert.
      intros.
      destruct (fun Hu Hv => @ExprI.expr_subst_sound
                    typ _ (expr typ func) Expr_expr _
                    _lookupU
                    (_lookupV (length tvs) (length tvs'))
                    0 e _ eq_refl nil
                    tus (tvs ++ tvs') tus (tvs' ++ tvs)
                    (fun us vs us' vs' =>
                       us = us' /\
                       let (_vs,_vs') := hlist_split _ _ vs in
                       let (__vs,__vs') := hlist_split _ _ vs' in
                       _vs = __vs' /\ _vs' = __vs) Hu Hv t _ eq_refl H).
      { simpl. clear.
        intros. eexists; split; eauto.
        intros. destruct H1; subst; auto. }
      { simpl. intros.
        autorewrite with exprD_rw. simpl.
        consider (u ?[ ge ] length tvs); intros.
        { eapply nth_error_get_hlist_nth_appR in H1; eauto.
          simpl in H1. forward_reason.
          eapply nth_error_get_hlist_nth_weaken with (ls':=tvs) in H1.
          simpl in H1.
          forward_reason. rewrite H1.
          rewrite type_cast_refl; eauto.
          eexists; split; eauto.
          unfold Rcast_val, Rcast, Relim. simpl.
          intros.
          revert H5.
          rewrite <- (hlist_app_hlist_split _ _ vs).
          rewrite <- (hlist_app_hlist_split _ _ vs').
          rewrite hlist_split_hlist_app.
          rewrite hlist_split_hlist_app.
          destruct 1.
          rewrite H3. rewrite <- H4.
          f_equal. tauto. }
        { assert (u < length tvs) by omega.
          eapply nth_error_get_hlist_nth_appL in H3.
          destruct H3. destruct H3.
          rewrite H3 in H1.
          assert (u + length tvs' >= length tvs') by omega.
          destruct H4 as [ ? [ ? ? ] ].
          eapply nth_error_get_hlist_nth_appR' in H4; simpl in H4.
          destruct H4 as [ ? [ ? ? ] ].
          rewrite H4.
          inv_all. subst. simpl.
          rewrite type_cast_refl; eauto.
          eexists; split; eauto.
          intros us vs us' vs'.
          rewrite <- (hlist_app_hlist_split _ _ vs).
          rewrite <- (hlist_app_hlist_split _ _ vs').
          rewrite hlist_split_hlist_app.
          rewrite hlist_split_hlist_app.
          destruct 1.
          simpl in *.
          rewrite H6. rewrite <- H7.
          unfold Rcast_val, Rcast; simpl. f_equal. tauto. } }
      { simpl in H0.
        destruct H0; eexists; split; eauto.
        intros. apply (H1 a (hlist_app b c) a (hlist_app c b) Hnil).
        split; auto.
        do 2 rewrite hlist_split_hlist_app.
        tauto. }
    Qed.

    (* This code starts to build the structure necessary for [rtac]
     *)
    Fixpoint wrap_tvs (tvs : tenv typ) (ctx : Ctx typ (expr typ func))
    : Ctx typ (expr typ func) :=
      match tvs with
      | nil => ctx
      | t :: tvs' => wrap_tvs tvs' (CAll ctx t)
      end.

    Fixpoint wrap_tvs_ctx_subst tvs ctx (cs : ctx_subst ctx)
    : ctx_subst (wrap_tvs tvs ctx) :=
      match tvs as tvs return ctx_subst (wrap_tvs tvs ctx) with
      | nil => cs
      | t :: tvs => wrap_tvs_ctx_subst _ (AllSubst cs)
      end.

    Fixpoint unwrap_tvs_ctx_subst T tvs ctx
    : ctx_subst (wrap_tvs tvs ctx) -> (ctx_subst ctx -> T) -> T :=
      match tvs as tvs
            return ctx_subst (wrap_tvs tvs ctx) -> (ctx_subst ctx -> T) -> T
      with
      | nil => fun cs k => k cs
      | t :: tvs => fun cs k =>
        @unwrap_tvs_ctx_subst T tvs (CAll ctx t) cs (fun z => k (fromAll z))
      end.

    (* TODO(gmalecha): This does not have a stand-alone soundness theorem,
     * which is problematic because it does some quite complex manipulation.
     *)
    Definition for_tactic
               (m : expr typ func ->
                    tenv typ -> tenv typ -> nat -> nat ->
                    forall ctx : Ctx typ (expr typ func),
                      ctx_subst ctx -> option (expr typ func * ctx_subst ctx))
    : expr typ func -> mrw (expr typ func) :=
      fun e tvs' tus tvs nus nvs ctx cs =>
        let under := length tvs' in
        let e' := expr_convert under nvs e in
        match
          m e' tus (tvs ++ tvs') nus (under + nvs) _
            (@wrap_tvs_ctx_subst tvs' ctx cs)
        with
        | None => None
        | Some (v,cs') =>
          Some (expr_convert nvs under v,
                @unwrap_tvs_ctx_subst _ tvs' ctx cs' (fun x => x))
        end.

    (* TODO(gmalecha): This should go in a new file that implements
     * rewriting databases.
     *)
    Fixpoint using_rewrite_db'
             (ls : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R ->
      tenv typ -> tenv typ -> nat -> nat ->
      forall ctx, ctx_subst ctx -> option (expr typ func * ctx_subst ctx) :=
      match ls with
      | nil => fun _ _ _ _ _ _ _ _ => None
      | (lem,tac) :: ls =>
        let res := using_rewrite_db' ls in
        let crw := core_rewrite lem tac in
        fun e r tus tvs nus nvs ctx cs =>
          if Req_dec Rbase_eq r lem.(concl).(rel) then
            match crw e tus tvs nus nvs ctx cs with
            | None => res e r tus tvs nus nvs ctx cs
            | X => X
            end
          else res e r tus tvs nus nvs ctx cs
      end.

    Lemma using_rewrite_db'_sound
    : forall r ctx (cs : ctx_subst ctx),
        let tus := getUVars ctx in
        let tvs := getVars ctx in
        forall hints : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)),
        Forall (fun lt =>
                  lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
                  rtacK_sound (snd lt)) hints ->
        forall e e' cs',
          @using_rewrite_db' hints e r tus tvs (length tus) (length tvs) ctx cs = Some (e', cs') ->
          WellFormed_ctx_subst cs ->
          WellFormed_ctx_subst cs' /\
          (forall (t : typ) (rD : typD t -> typD t -> Prop),
              RD RbaseD r t = Some rD ->
              match pctxD cs with
              | Some _ =>
                match exprD' tus tvs t e with
                | Some eD =>
                  match pctxD cs' with
                  | Some csD' =>
                    match exprD' tus tvs t e' with
                    | Some eD' =>
                      SubstMorphism cs cs' /\
                      (forall (us : hlist typD (getAmbientUVars ctx))
                              (vs : hlist typD (getAmbientVars ctx)),
                          csD'
                            (fun (us0 : hlist typD (getUVars ctx))
                                 (vs0 : hlist typD (getVars ctx)) =>
                                 rD (eD us0 vs0)
                                    (eD' us0 vs0)) us vs)
                    | None => False
                    end
                  | None => False
                  end
                | None => True
                end
              | None => True
              end).
    Proof.
      induction 1.
      { simpl. inversion 1. }
      { simpl. intros. destruct x.
        assert (using_rewrite_db' l e r tus tvs (length tus) (length tvs) cs = Some (e',cs')
             \/ (r = l0.(concl).(rel) /\
                 core_rewrite l0 r0 e tus tvs (length tus) (length tvs) cs = Some (e',cs'))).
        { generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r l0.(concl).(rel)).
          destruct (Req_dec Rbase_eq r l0.(concl).(rel)); eauto.
          intros. destruct (core_rewrite l0 r0 e tus tvs (length tus) (length tvs) cs); eauto. }
        clear H1. destruct H3; eauto.
        destruct H1. subst. clear IHForall H0.
        simpl in H. destruct H.
        revert H2. revert H3. revert H. revert H0.
        intros.
        eapply core_rewrite_sound in H3; eauto using rtacK_sound_WellFormed_rtacK.
        forward_reason. eauto. }
    Qed.

    Section using_prewrite_db.
      Variable phints : expr typ func -> R -> list (rw_lemma typ func Rbase * rtacK typ (expr typ func)).

      Definition using_prewrite_db' :=
        fun e r => using_rewrite_db' (phints e r) e r.

      Lemma using_prewrite_db_sound'
      : forall r ctx (cs : ctx_subst ctx),
          let tus := getUVars ctx in
          let tvs := getVars ctx in
          forall e e' cs',
            @using_prewrite_db' e r tus tvs (length tus) (length tvs) ctx cs = Some (e', cs') ->
            forall (Hrtac_wf : forall e r,
                       Forall (fun lt => WellFormed_rtacK (snd lt)) (phints e r)),
            WellFormed_ctx_subst cs ->
            WellFormed_ctx_subst cs' /\
            ((forall e r tus tvs t eD,
                 exprD' tus tvs t e = Some eD ->
                 Forall (fun lt =>
                           lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
                           rtacK_sound (snd lt)) (phints e r)) ->
             (forall (t : typ) (rD : typD t -> typD t -> Prop),
                 RD RbaseD r t = Some rD ->
                 match pctxD cs with
                 | Some _ =>
                   match exprD' tus tvs t e with
                   | Some eD =>
                     match pctxD cs' with
                     | Some csD' =>
                       match exprD' tus tvs t e' with
                       | Some eD' =>
                         SubstMorphism cs cs' /\
                         (forall (us : hlist typD (getAmbientUVars ctx))
                                 (vs : hlist typD (getAmbientVars ctx)),
                             csD'
                               (fun (us0 : hlist typD (getUVars ctx))
                                    (vs0 : hlist typD (getVars ctx)) =>
                                  rD (eD us0 vs0)
                                     (eD' us0 vs0)) us vs)
                       | None => False
                       end
                     | None => False
                     end
                   | None => True
                   end
                 | None => True
                 end)).
      Proof.
        simpl.
        unfold using_prewrite_db'.
        intros r ctx cs e. revert cs.
        cut (forall (cs : ctx_subst ctx) (e' : expr typ func) (cs' : ctx_subst ctx),
                using_rewrite_db' (phints e r) e r (getUVars ctx) 
                                  (getVars ctx) (length (getUVars ctx)) (length (getVars ctx)) cs =
                Some (e', cs') ->
                (Forall
                   (fun lt : rw_lemma typ func Rbase * rtacK typ (expr typ func) =>
                      WellFormed_rtacK (snd lt)) (phints e r)) ->
                WellFormed_ctx_subst cs ->
                WellFormed_ctx_subst cs' /\
                ((forall (tus tvs : tenv typ) 
                         (t : typ) (eD : exprT tus tvs (typD t)),
                     exprD' tus tvs t e = Some eD ->
                     Forall
                       (fun
                           lt : lemma typ (expr typ func) (rw_concl typ func Rbase) *
                                rtacK typ (expr typ func) =>
                           lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\ rtacK_sound (snd lt))
                       (phints e r)) ->
                 forall (t : typ) (rD : typD t -> typD t -> Prop),
                   RD RbaseD r t = Some rD ->
                   match pctxD cs with
                   | Some _ =>
                     match exprD' (getUVars ctx) (getVars ctx) t e with
                     | Some eD =>
                       match pctxD cs' with
                       | Some csD' =>
                         match exprD' (getUVars ctx) (getVars ctx) t e' with
                         | Some eD' =>
                           SubstMorphism cs cs' /\
                           (forall (us : hlist typD (getAmbientUVars ctx))
                                   (vs : hlist typD (getAmbientVars ctx)),
                               csD'
                                 (fun (us0 : hlist typD (getUVars ctx))
                                      (vs0 : hlist typD (getVars ctx)) =>
                                    rD (eD us0 vs0) (eD' us0 vs0)) us vs)
                         | None => False
                         end
                       | None => False
                       end
                     | None => True
                     end
                   | None => True
                   end)).
        { clear.
          intros; forward_reason.
          eapply H in H0; eauto.
          forward_reason. split; eauto.
          intros.
          eapply H2; eauto. }
        induction (phints e r).
        { inversion 1. }
        { simpl. intros.
          destruct a.
          assert (using_rewrite_db' l e r (getUVars ctx) (getVars ctx) (length (getUVars ctx)) (length (getVars ctx)) cs = Some (e',cs')
                  \/ (r = r0.(concl).(rel) /\
                      core_rewrite r0 r1 e (getUVars ctx) (getVars ctx) (length (getUVars ctx)) (length (getVars ctx)) cs = Some (e',cs'))).
          { generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r r0.(concl).(rel)).
            destruct (Req_dec Rbase_eq r r0.(concl).(rel)); eauto.
            intros. destruct (core_rewrite r0 r1 e (getUVars ctx) (getVars ctx) (length (getUVars ctx)) (length (getVars ctx)) cs); eauto. }
          clear H.
          destruct H2.
          { eapply IHl in H; clear IHl; eauto.
            forward_reason. split; eauto.
            intros. eapply H2; eauto.
            intros. eapply H3 in H5; eauto. inversion H5; eauto.
            inversion H0; auto. }
          { forward_reason. subst.
            split.
            { eapply core_rewrite_sound in H2; eauto.
              forward_reason; eauto.
              inversion H0; trivial. }
            { intros. forward.
              specialize (H _ _ _ _ H5).
              inversion H; clear H; subst; forward_reason.
              eapply core_rewrite_sound in H1; eauto.
              forward_reason; eauto.
              eapply H7 in H3.
              revert H3.
              Cases.rewrite_all_goal.
              trivial.
              inversion H0; trivial. } } }
      Qed.
    End using_prewrite_db.

    Definition using_rewrite_db''
               (ls : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R -> mrw (expr typ func) :=
      let rw_db := using_rewrite_db' ls in
      fun e r => for_tactic (fun e => rw_db e r) e.

    Definition using_prewrite_db''
        (lems : expr typ func -> R -> list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : expr typ func -> R -> mrw (expr typ func) :=
      fun e r =>
        for_tactic (fun e => using_rewrite_db' (lems e r) e r) e.

    Lemma getAmbientUVars_wrap_tvs : forall tvs ctx,
        getAmbientUVars (wrap_tvs tvs ctx) = getAmbientUVars ctx.
    Proof using.
      induction tvs; simpl. reflexivity.
      intros. rewrite IHtvs. reflexivity.
    Defined.

    Lemma getAmbientVars_wrap_tvs : forall tvs ctx,
        getAmbientVars (wrap_tvs tvs ctx) = getAmbientVars ctx.
    Proof using.
      induction tvs; simpl. reflexivity.
      intros. rewrite IHtvs. reflexivity.
    Defined.

    Lemma getVars_wrap_tvs : forall tvs' ctx,
        getVars (wrap_tvs tvs' ctx) = getVars ctx ++ tvs'.
    Proof using.
      induction tvs'; simpl; eauto.
      symmetry. eapply app_nil_r_trans.
      simpl. intros. rewrite IHtvs'. simpl.
      rewrite app_ass_trans. reflexivity.
    Defined.

    Lemma WellFormed_ctx_subst_unwrap_tvs
    : forall tvs' ctx ctx' (cs : ctx_subst _)
             (k : ctx_subst (Ctx_append ctx ctx') -> ctx_subst ctx),
        (forall cs, WellFormed_ctx_subst cs -> WellFormed_ctx_subst (k cs)) ->
        WellFormed_ctx_subst cs ->
        WellFormed_ctx_subst
          (@unwrap_tvs_ctx_subst (ctx_subst ctx) tvs' (Ctx_append ctx ctx') cs k).
    Proof using.
      induction tvs'; simpl; auto.
      intros. specialize (IHtvs' ctx (CAll ctx' a) cs).
      simpl in *. eapply IHtvs'; eauto.
      intros. eapply H. rewrite (ctx_subst_eta cs0) in H1.
      inv_all. assumption.
    Qed.

    Fixpoint unwrap_tvs_ctx_subst' (tvs : tenv typ) (ctx : Ctx typ (expr typ func))
    : ctx_subst (wrap_tvs tvs ctx) -> ctx_subst ctx :=
      match tvs as tvs return ctx_subst (wrap_tvs tvs ctx) -> ctx_subst ctx with
      | nil => fun X => X
      | t :: tvs => fun X => fromAll (unwrap_tvs_ctx_subst' tvs _ X)
      end.

    Theorem unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'
    : forall T tvs ctx cs (k : _ -> T),
        k (@unwrap_tvs_ctx_subst' tvs ctx cs) =
        unwrap_tvs_ctx_subst tvs cs k.
    Proof using.
      induction tvs; simpl. auto.
      intros. rewrite <- IHtvs. reflexivity.
    Qed.

    (** TODO: Move **)
    Lemma pctxD_iff : forall ctx (cs : ctx_subst ctx) cD P Q,
        pctxD cs = Some cD ->
        (forall us vs, P us vs <-> Q us vs) ->
        forall us vs,
          cD P us vs <-> cD Q us vs.
    Proof using.
      intros.
      split; eapply Ap_pctxD; eauto; eapply Pure_pctxD; eauto; intros; eapply H0; eauto.
    Qed.

    (** TODO: Move **)
    Lemma forall_hlist_nil : forall T (F : T -> Type) (P : hlist F nil -> Prop),
        (forall x, P x) <-> P Hnil.
    Proof using.
      intros. split. eauto. intros. rewrite hlist_eta. assumption.
    Qed.

    Lemma forall_hlist_cons : forall T (F : T -> Type) t ts (P : hlist F (t :: ts) -> Prop),
        (forall x, P x) <-> (forall x xs, P (Hcons x xs)).
    Proof.
      intros. split. eauto. intros. rewrite hlist_eta. eapply H.
    Qed.

    Lemma getUVars_wrap_tvs
    : forall tvs' ctx, getUVars (wrap_tvs tvs' ctx) = getUVars ctx.
    Proof using.
      induction tvs'; simpl; auto.
      intros.  rewrite IHtvs'. reflexivity.
    Defined.

    Lemma WellFormed_ctx_subst_wrap_tvs : forall tvs' ctx (cs : ctx_subst ctx),
        WellFormed_ctx_subst cs ->
        WellFormed_ctx_subst (wrap_tvs_ctx_subst tvs' cs).
    Proof using.
      induction tvs'; simpl; auto.
      intros. eapply IHtvs'. constructor. assumption.
    Qed.

    Lemma pctxD_unwrap_tvs_ctx_subst
    : forall tvs ctx (cs : ctx_subst _) cD,
        pctxD cs = Some cD ->
        exists cD',
          pctxD (@unwrap_tvs_ctx_subst _ tvs ctx cs (fun x => x)) = Some cD' /\
          forall (us : hlist typD _) (vs : hlist typD _) (P : exprT _ _ Prop),
            cD' (fun us vs => forall vs', P us (hlist_app vs vs')) us vs <->
            cD match eq_sym (getVars_wrap_tvs tvs ctx) in _ = V
                   , eq_sym (getUVars_wrap_tvs tvs ctx) in _ = U
                     return exprT U V Prop
               with
               | eq_refl , eq_refl => P
               end
               match eq_sym (getAmbientUVars_wrap_tvs tvs ctx) in _ = V
                     return hlist _ V
               with
               | eq_refl => us
               end
               match eq_sym (getAmbientVars_wrap_tvs tvs ctx) in _ = V
                     return hlist _ V
               with
               | eq_refl => vs
               end.
    Proof.
      clear - RTypeOk_typD RSymOk_func Typ2Ok_Fun tyArr.
      intros. rewrite <- unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'.
      generalize dependent cD. revert cs. revert ctx.
      induction tvs.
      { simpl. eauto.
        eexists; split; eauto.
        intros.
        eapply pctxD_iff; eauto.
        intros.
        rewrite forall_hlist_nil.
        rewrite hlist_app_nil_r.
        generalize (app_nil_r_trans (getVars ctx)).
        clear. generalize dependent (getVars ctx ++ nil).
        intros; subst. reflexivity. }
      { simpl; intros.
        specialize (@IHtvs _ _ _ H).
        forward_reason.
        generalize dependent (unwrap_tvs_ctx_subst' tvs (CAll ctx a) cs).
        intro. rewrite (ctx_subst_eta c); simpl.
        intros; forwardy.
        eexists; split; eauto.
        inv_all. subst. intros.
        specialize (H1 us vs
                       match eq_sym (app_ass_trans (getVars ctx) (a::nil) _) in _ = X
                             return exprT _ X Prop
                       with
                       | eq_refl => P
                       end).
        simpl in *.
        etransitivity; [ etransitivity; [ | eapply H1 ] | ]; clear H1.
        { eapply pctxD_iff; eauto.
          intros.
          rewrite forall_hlist_cons.
          eapply Data.Prop.forall_iff; intros.
          eapply Data.Prop.forall_iff; intros.
          rewrite hlist_app_assoc.
          clear. simpl.
          generalize dependent (app_ass_trans (getVars ctx) (a :: nil) tvs).
          simpl in *.
          generalize dependent ((getVars ctx ++ a :: nil) ++ tvs).
          intros; subst. reflexivity. }
        { clear - H tyArr.
          match goal with
          | |- _ _ ?U ?V <-> _ _ ?U' ?V' =>
            replace V with V' ; [ replace U with U' | ]
          end.
          { eapply pctxD_iff; eauto; clear.
            generalize (app_ass_trans (getVars ctx) (a :: nil) tvs).
            generalize (getVars_wrap_tvs tvs (CAll ctx a)).
            generalize (getUVars_wrap_tvs tvs (CAll ctx a)).
            simpl.
            intros;
            repeat match goal with
               | H : @eq (tenv typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               | H : @eq (list typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               end. reflexivity. }
          { clear.
            generalize (getAmbientUVars_wrap_tvs tvs (CAll ctx a)).
            simpl in *. destruct e. reflexivity. }
          { clear.
            generalize (getAmbientVars_wrap_tvs tvs (CAll ctx a)).
            simpl. destruct e. reflexivity. } } }
    Qed.

    Lemma pctxD_wrap_tvs_ctx_subst
    : forall tvs ctx (cs : ctx_subst ctx) cD,
        pctxD cs = Some cD ->
        exists cD',
          pctxD (wrap_tvs_ctx_subst tvs cs) = Some cD' /\
          forall us vs (P : exprT _ _ Prop),
            cD (fun us vs => forall vs', P us (hlist_app vs vs')) us vs <->
            cD' match eq_sym (getVars_wrap_tvs tvs ctx) in _ = V
                                                           , eq_sym (getUVars_wrap_tvs tvs ctx) in _ = U
                      return exprT U V Prop
                with
                | eq_refl , eq_refl => P
                end
                match eq_sym (getAmbientUVars_wrap_tvs tvs ctx) in _ = V
                      return hlist _ V
                with
                | eq_refl => us
                end
                match eq_sym (getAmbientVars_wrap_tvs tvs ctx) in _ = V
                      return hlist _ V
                with
                | eq_refl => vs
                end.
    Proof using RTypeOk_typD RSymOk_func Typ2Ok_Fun.
      induction tvs.
      { simpl. eauto.
        eexists; split; eauto.
        intros; eapply pctxD_iff; eauto.
        intros. rewrite forall_hlist_nil.
        rewrite hlist_app_nil_r. clear.
        generalize (app_nil_r_trans (getVars ctx)).
        generalize dependent (getVars ctx ++ nil). intros; subst.
        reflexivity. }
      { simpl. intros.
        specialize (IHtvs (CAll ctx a) (AllSubst cs)).
        simpl in IHtvs. rewrite H in IHtvs.
        specialize (IHtvs _ eq_refl).
        destruct IHtvs as [ ? [ ? ? ] ].
        eexists; split; eauto.
        intros.
        specialize (H1 us vs
                       match eq_sym (app_ass_trans (getVars ctx) (a::nil) _) in _ = X
                             return exprT _ X Prop
                       with
                       | eq_refl => P
                       end).
        etransitivity; [ etransitivity; [ | eapply H1 ] | ]; clear H1.
        { eapply pctxD_iff; eauto.
          intros. rewrite forall_hlist_cons.
          eapply Data.Prop.forall_iff; intro.
          eapply Data.Prop.forall_iff; intro.
          rewrite hlist_app_assoc.
          clear.
          generalize dependent (eq_sym (app_ass_trans (getVars ctx) (a :: nil) tvs)).
          simpl in *. destruct e. reflexivity. }
        { match goal with
          | |- _ _ ?U ?V <-> _ _ ?U' ?V' =>
            replace V with V' ; [ replace U with U' | ]
          end.
          { eapply pctxD_iff; eauto.
            intros.
            generalize (app_ass_trans (getVars ctx) (a :: nil) tvs).
            generalize (getVars_wrap_tvs tvs (CAll ctx a)).
            generalize (getUVars_wrap_tvs tvs (CAll ctx a)).
            simpl. clear.
            intros;
            repeat match goal with
               | H : @eq (tenv typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               | H : @eq (list typ) ?X ?Y |- _ =>
                 first [ generalize dependent X | generalize dependent Y ] ; intros; subst
               end. reflexivity. }
          { clear.
            generalize (getAmbientUVars_wrap_tvs tvs (CAll ctx a)).
            simpl in *. destruct e. reflexivity. }
          { clear.
            generalize (getAmbientVars_wrap_tvs tvs (CAll ctx a)).
            simpl. destruct e. reflexivity. } } }
    Qed.

    Lemma SubstMorphism_wrap_tvs_ctx_subst
    : forall tvs' ctx cs c,
        SubstMorphism (wrap_tvs_ctx_subst tvs' cs) c ->
        SubstMorphism cs
                      (unwrap_tvs_ctx_subst tvs' c (fun x : ctx_subst ctx => x)).
    Proof.
      clear -tyArr _lookupU _lookupV. intros.
      rewrite <- unwrap_tvs_ctx_subst_unwrap_tvs_ctx_subst'.
      revert H. revert ctx c cs.
      induction tvs'.
      { simpl. tauto. }
      { simpl. intros.
        eapply IHtvs' in H.
        inv_all. rewrite H. assumption. }
    Qed.

    Definition using_rewrite_db
               (hints : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : lem_rewriter :=
      fun e r => rw_bind (using_rewrite_db'' hints e r)
                         (fun e => rw_ret (Progress e)).

    Theorem using_rewrite_db_sound
    : forall hints : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)),
        Forall (fun lt =>
                  lemmaD (rw_conclD RbaseD) nil nil (fst lt) /\
                  rtacK_sound (snd lt)) hints ->
        setoid_rewrite_spec (using_rewrite_db hints).
    Proof.
      unfold using_rewrite_db, using_rewrite_db''.
      unfold for_tactic.
      red. red. intros.
      unfold rw_bind in H0.
      forwardy. inv_all. subst.
      rewrite Plus.plus_comm in H0. rewrite <- app_length in H0.
      destruct (fun Hx =>
                    @using_rewrite_db'_sound r _ (wrap_tvs_ctx_subst tvs' cs) hints H
                                             (expr_convert (length tvs') (length (getVars ctx)) e) e1 c0 Hx
                                             (WellFormed_ctx_subst_wrap_tvs _ H1)).
      { rewrite <- H0. f_equal.
        eauto using getUVars_wrap_tvs.
        eauto using getVars_wrap_tvs.
        rewrite getUVars_wrap_tvs. reflexivity.
        rewrite getVars_wrap_tvs. reflexivity. }
      clear H0. subst.
      split.
      { eapply WellFormed_ctx_subst_unwrap_tvs
          with (ctx':=CTop nil nil); eauto. }
      intros.
      specialize (H3 _ _ H0); clear H0.
      destruct (pctxD cs) eqn:HpctxD_cs; trivial.
      destruct (@pctxD_wrap_tvs_ctx_subst tvs' _ _ _ HpctxD_cs) as [ ? [ ? ? ] ].
      rewrite H0 in H3.
      destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:HexprD'_e; trivial.
      generalize (@exprD'_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (tus':=getUVars ctx) (tvs':=getVars ctx++tvs')
              (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym (getVars_wrap_tvs tvs' ctx))
           in H3.
      clear Hconv.
      eapply expr_convert_sound in HexprD'_e.
      destruct HexprD'_e as [ ? [ Hx ? ] ].
      rewrite Hx in *; clear Hx.
      autorewrite_with_eq_rw_in H3.
      forwardy.
      destruct (pctxD_unwrap_tvs_ctx_subst _ _ _ H3) as [ ? [ HpctxD_x1 ? ] ].
      rewrite HpctxD_x1.
      generalize (@exprD'_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym(getVars_wrap_tvs tvs' ctx))
           in H6.
      clear Hconv.
      autorewrite_with_eq_rw_in H6.
      forwardy; inv_all; subst.
      eapply expr_convert_sound in H6.
      destruct H6 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      destruct H7.
      split.
      { clear H9 H8 H4.
        eapply SubstMorphism_wrap_tvs_ctx_subst; eauto. }
      { intros.
        specialize (H9 match
                        eq_sym (getAmbientUVars_wrap_tvs tvs' ctx) in (_ = V)
                        return (hlist typD V)
                      with
                      | eq_refl => us
                      end
                       match
                         eq_sym (getAmbientVars_wrap_tvs tvs' ctx) in (_ = V)
                         return (hlist typD V)
                       with
                       | eq_refl => vs
                       end).
        specialize (H8 us vs
                   (fun us0 vs0 =>
                      rD (x0 us0 vs0) (y2 us0 vs0))).
        simpl in H8.
        generalize dependent (getVars_wrap_tvs tvs' ctx).
        generalize dependent (getUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientVars_wrap_tvs tvs' ctx).
        generalize (Ap_pctxD _ HpctxD_x1).
        generalize (Pure_pctxD _ HpctxD_x1).
        revert H5 H6 H7. clear.
        generalize dependent (getAmbientVars (wrap_tvs tvs' ctx)).
        generalize dependent (getAmbientUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getVars (wrap_tvs tvs' ctx)).
        intros; subst; simpl in *.
        eapply H8 in H9; clear H8.
        revert H9. eapply H0; clear H0.
        eapply H; clear H.
        clear - H5 H6.
        intros. rewrite H5. rewrite <- H6. eauto. }
    Time Qed.

    Definition using_prewrite_db
               (hints : expr typ func -> R ->
                        list (rw_lemma typ func Rbase * rtacK typ (expr typ func)))
    : lem_rewriter :=
      fun e r => rw_bind (using_prewrite_db'' hints e r)
                         (fun e => rw_ret (Progress e)).


    (** TODO(gmalecha): This is almost identical to the above theorem *)
    Theorem using_prewrite_db_sound
    : forall hints : expr typ func -> R ->
                     list (rw_lemma typ func Rbase * rtacK typ (expr typ func)),
        (forall r e,
            Forall (fun lt =>
                      (forall tus tvs t eD,
                          exprD' tus tvs t e = Some eD ->
                          lemmaD (rw_conclD RbaseD) nil nil (fst lt)) /\
                      rtacK_sound (snd lt)) (hints e r)) ->
        setoid_rewrite_spec (using_prewrite_db hints).
    Proof.
      intros.
      unfold using_prewrite_db, using_prewrite_db''.
      unfold for_tactic.
      red. red. intros.
      unfold rw_bind in H0.
      forwardy. inv_all. subst.
      rewrite Plus.plus_comm in H0. rewrite <- app_length in H0.
      destruct (@using_prewrite_db_sound' hints r _ (wrap_tvs_ctx_subst tvs' cs)
                                          (expr_convert (length tvs') (length (getVars ctx)) e) e1 c0).
      { rewrite <- H0.
        unfold using_prewrite_db'. f_equal.
        eauto using getUVars_wrap_tvs.
        eauto using getVars_wrap_tvs.
        rewrite getUVars_wrap_tvs. reflexivity.
        rewrite getVars_wrap_tvs. reflexivity. }
      { clear - H.
        intros. specialize (H r e).
        revert H.
        eapply Forall_impl. intros. destruct H.
        eauto using rtacK_sound_WellFormed_rtacK. }
      { eauto using WellFormed_ctx_subst_wrap_tvs. }
      clear H0. subst. split.
      { eapply WellFormed_ctx_subst_unwrap_tvs
          with (ctx':=CTop nil nil); eauto. }
      intros.
      specialize (fun Hx => H3 Hx _ _ H0); clear H0.
      destruct (pctxD cs) eqn:HpctxD_cs; trivial.
      destruct (@pctxD_wrap_tvs_ctx_subst tvs' _ _ _ HpctxD_cs) as [ ? [ ? ? ] ].
      rewrite H0 in H3.
      destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:HexprD'_e; trivial.
      generalize (@exprD'_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (tus':=getUVars ctx) (tvs':=getVars ctx++tvs')
              (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym (getVars_wrap_tvs tvs' ctx))
           in H3.
      clear Hconv.
      eapply expr_convert_sound in HexprD'_e.
      destruct HexprD'_e as [ ? [ Hx ? ] ].
      rewrite Hx in *; clear Hx.
      autorewrite_with_eq_rw_in H3.
      match goal with
      | H : ?X -> _ |- _ =>
        match type of X with
        | Prop =>
          let H' := fresh in
          assert (H' : X) ; [ clear H | specialize (H H'); clear H' ]
        end
      end.
      { clear - H.
        intros. generalize (H r e).
        eapply Forall_impl. intros; forward_reason.
        split; eauto. }
      forwardy.
      destruct (pctxD_unwrap_tvs_ctx_subst _ _ _ H3) as [ ? [ HpctxD_x1 ? ] ].
      rewrite HpctxD_x1.
      generalize (@exprD'_conv typ _ (expr typ func) _). simpl.
      intro Hconv.
      rewrite Hconv
         with (pfu:=eq_sym (getUVars_wrap_tvs tvs' ctx)) (pfv:=eq_sym(getVars_wrap_tvs tvs' ctx))
           in H6.
      clear Hconv.
      autorewrite_with_eq_rw_in H6.
      forwardy; inv_all; subst.
      eapply expr_convert_sound in H6.
      destruct H6 as [ ? [ Hx ? ] ]; rewrite Hx; clear Hx.
      destruct H7.
      split.
      { clear H9 H8 H4.
        eapply SubstMorphism_wrap_tvs_ctx_subst; eauto. }
      { intros.
        specialize (H9 match
                        eq_sym (getAmbientUVars_wrap_tvs tvs' ctx) in (_ = V)
                        return (hlist typD V)
                      with
                      | eq_refl => us
                      end
                       match
                         eq_sym (getAmbientVars_wrap_tvs tvs' ctx) in (_ = V)
                         return (hlist typD V)
                       with
                       | eq_refl => vs
                       end).
        specialize (H8 us vs
                   (fun us0 vs0 =>
                      rD (x0 us0 vs0) (y2 us0 vs0))).
        simpl in H8.
        generalize dependent (getVars_wrap_tvs tvs' ctx).
        generalize dependent (getUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientUVars_wrap_tvs tvs' ctx).
        generalize dependent (getAmbientVars_wrap_tvs tvs' ctx).
        generalize (Ap_pctxD _ HpctxD_x1).
        generalize (Pure_pctxD _ HpctxD_x1).
        revert H5 H6 H7. clear.
        generalize dependent (getAmbientVars (wrap_tvs tvs' ctx)).
        generalize dependent (getAmbientUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getUVars (wrap_tvs tvs' ctx)).
        generalize dependent (getVars (wrap_tvs tvs' ctx)).
        intros; subst; simpl in *.
        eapply H8 in H9; clear H8.
        revert H9. eapply H0; clear H0.
        eapply H; clear H.
        clear - H5 H6.
        intros. rewrite H5. rewrite <- H6. eauto. }
    Qed.

  End reindexing.

  Section reduction.
    Variable reducer : expr typ func -> expr typ func.
    Variable lr : lem_rewriter.

    Definition rw_simplify : lem_rewriter :=
      fun e => lr (reducer e).

    Hypothesis reducer_sound
    : forall tus tvs t e eD,
        exprD' tus tvs t e = Some eD ->
        exists eD',
          exprD' tus tvs t (reducer e) = Some eD' /\
          forall us vs, eD us vs = eD' us vs.
    Hypothesis lr_sound : setoid_rewrite_spec lr.

    Theorem rw_simplify_sound
    : setoid_rewrite_spec rw_simplify.
    Proof.
      unfold rw_simplify. do 2 red. intros.
      eapply lr_sound in H; eauto.
      forward_reason; split; eauto.
      intros. eapply H1 in H2; clear H1.
      forward.
      specialize (@reducer_sound _ _ _ _ _ H3).
      destruct reducer_sound as [ ? [ ? ? ] ].
      rewrite H4 in *.
      destruct (pctxD cs') eqn:?; auto.
      destruct e'.
      { simpl in *.
        forward.
        destruct H6; split; auto.
        intros.
        gather_facts.
        eapply Pure_pctxD; eauto.
        intros. rewrite H5. eauto. }
      { simpl in *. rewrite H4 in *.
        rewrite H3.
        destruct H2; split; auto.
        intros.
        gather_facts.
        eapply Pure_pctxD; eauto.
        intros. rewrite H5.
        auto. }
    Qed.

    Definition rw_post_simplify : lem_rewriter :=
      Eval unfold rw_bind, rw_ret in 
      fun e r => rw_bind (lr e r)
                         (fun e' => rw_ret (match e' with
                                            | Progress e' => Progress (reducer e')
                                            | NoProgress => NoProgress
                                            end)).

    Theorem rw_post_simplify_sound
    : setoid_rewrite_spec rw_post_simplify.
    Proof.
      unfold rw_post_simplify. do 2 red. intros.
      forward. inv_all; subst.
      eapply lr_sound in H1; eauto.
      forward_reason; split; eauto.
      intros. eapply H1 in H2; clear H1.
      destruct (pctxD cs) eqn:?; auto.
      destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t e) eqn:?; auto.
      destruct (pctxD cs') eqn:?; auto.
      destruct p0; simpl in *.
      { destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t new_val) eqn:?; try contradiction.
        eapply reducer_sound in Heqo2.
        destruct Heqo2 as [ ? [ ? ? ] ].
        rewrite H1. destruct H2; split; auto.
        intros.
        gather_facts.
        eapply Pure_pctxD; eauto.
        intros. rewrite <- H3. eauto. }
      { destruct (exprD' (getUVars ctx) (tvs' ++ getVars ctx) t e); auto. }
    Qed.

  End reduction.

  Section get_respectful.
    (* This is just a "special" version of the rewriting lemma *)
    Record Proper_concl : Type :=
    { relation : R
    ; term     : expr typ func
    }.

    Definition Proper_conclD (tus tvs : tenv typ) (p : Proper_concl)
    : option (exprT tus tvs Prop) :=
      match typeof_expr tus tvs p.(term) with
      | Some t =>
        match RD RbaseD p.(relation) t
            , exprD' tus tvs t p.(term)
        with
        | Some rD , Some eD =>
          Some (fun us vs => rD (eD us vs) (eD us vs))
        | _ , _ => None
        end
      | None => None
      end.

    Definition Proper_lemma := Lemma.lemma typ (expr typ func) Proper_concl.

    (* This splits a relation into a relation arity and a relation *)
    Fixpoint split_R (r : R) : list R * R :=
      match r with
      | Rrespects l r =>
        let (ls, r) := split_R r in
        (l :: ls, r)
      | _ => (nil, r)
      end.

    Lemma split_R_sound : forall r_end r rs,
        split_R r = (rs, r_end) ->
        fold_right Rrespects r_end rs = r.
    Proof using.
      induction r; simpl; intros; inv_all; subst; simpl; try reflexivity.
      destruct (split_R r2). inv_all. subst.
      specialize (IHr2 _ eq_refl).
      simpl. rewrite IHr2. reflexivity.
    Qed.

    Require Import MirrorCore.RTac.CoreK.

    Definition apply_respectful (lem : Proper_lemma)
               (tacK : rtacK typ (expr typ func))
    : respectful_dec :=
      let (rs,r_final) := split_R lem.(Lemma.concl).(relation) in
      match lem.(Lemma.vars) with
      | nil => match lem.(Lemma.premises) with
               | nil => fun e r =>
                          match expr_sdec e lem.(Lemma.concl).(term)
                                , Req_dec Rbase_eq r r_final
                          with
                          | true , true => rw_ret rs
                          | _ , _ => rw_fail
                          end
               | _ :: _ => fun e r =>
                             (** TODO(gmalecha): Handle this *)
                             rw_fail
               end
      | _ :: _ => fun _ _ => (** TODO(gmalecha): Handle this *)
                    rw_fail
      end.

    Theorem apply_respectful_sound : forall lem tacK,
        Lemma.lemmaD Proper_conclD nil nil lem ->
        forall Htac : rtacK_sound tacK,
          respectful_spec (apply_respectful lem tacK).
    Proof.
      red; intros.
      unfold apply_respectful in H0.
      consider (split_R (relation (Lemma.concl lem))); intros.
      destruct (Lemma.vars lem) eqn:?.
      { destruct (Lemma.premises lem) eqn:?; try solve [ inversion H2 ].
        generalize (expr_sdec_sound e lem.(Lemma.concl).(term)).
        generalize (Req_dec_ok Rbase_eq Rbase_eq_ok r r0).
        destruct (expr_sdec e (term (Lemma.concl lem))); try solve [ inversion H2 ].
        destruct (Req_dec Rbase_eq r r0); try solve [ inversion H2 ].
        unfold rw_ret in H2. inv_all.
        intros. specialize (H2 eq_refl). specialize (H5 eq_refl).
        subst.
        split; auto. intros.
        forward.
        red in H.
        simpl in H.
        unfold Lemma.lemmaD' in H.
        forwardy. inv_all. subst.
        generalize dependent lem.(Lemma.vars); intros; subst.
        generalize dependent lem.(Lemma.premises); intros; subst.
        simpl in *.
        unfold Proper_conclD in H6.
        forwardy.
        inv_all. subst.
        simpl in *.
        erewrite split_R_sound by eassumption.
        destruct (ExprFacts.exprD'_weaken _ _ _ (getUVars ctx) (tvs'++getVars ctx) H8) as [ ? [ ? ? ] ].
        simpl in H.
        generalize (@exprD'_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H4).
        unfold Rty. intros.
        revert H5.
        subst y. intros.
        rewrite H7.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto.
        intros.
        specialize (@H9 HList.Hnil HList.Hnil us0 (HList.hlist_app vs' vs0)); simpl in H9.
        rewrite H9 in H5.
        rewrite H4 in H.
        inv_all. subst. eapply H5. }
      { inversion H2. }
    Qed.

    Definition apply_prespectful {T : Type}
               (get : expr typ func -> R -> option T)
               (lem : T -> Proper_lemma) (tacK : rtacK _ _)
    : respectful_dec :=
      fun e r =>
        match get e r with
        | Some t => apply_respectful (lem t) tacK e r
        | _ => rw_fail
        end.

    Theorem apply_prespectful_sound : forall {T} get (lem : T -> _) (tacK : _),
        (forall e r x,
            get e r = Some x ->
            forall tus tvs t eD,
              exprD' tus tvs e t = Some eD ->
              Lemma.lemmaD Proper_conclD nil nil (lem x)) ->
        rtacK_sound tacK ->
        respectful_spec (apply_prespectful get lem tacK).
    Proof.
      intros. unfold apply_prespectful.
      red. intros.
      destruct (get e r) eqn:?; try solve [ inversion H1 ].
      (** above *)
      unfold apply_respectful in H1.
      destruct (split_R t.(lem).(concl).(relation)) eqn:?.
      eapply split_R_sound in Heqp.
      destruct (t.(lem).(vars)) eqn:Hvars; [ | inversion H1 ].
      destruct (t.(lem).(premises)) eqn:Hprems; [ | inversion H1 ].
      generalize (expr_sdec_sound e t.(lem).(concl).(term)).
      destruct (expr_sdec e t.(lem).(concl).(term)); [ | inversion H1 ].
      generalize (Req_dec_ok _ Rbase_eq_ok r r0).
      destruct (Req_dec Rbase_eq r r0); [ | inversion H1 ].
      intro X; specialize (X eq_refl); subst.
      intro X; specialize (X eq_refl); subst.
      inversion H1; clear H1; subst.
      split; auto.
      intros.
      forward.
      eapply H in Heqo; [ | eapply H4 ].
      rename Heqo into Hlem.
      red in Hlem.
      simpl in Hlem.
      red in Hlem. rewrite Hprems in *. rewrite Hvars in *.
      simpl in Hlem. red in Hlem.
      revert Hlem.
      forward. inv_all. subst.
      destruct (ExprFacts.exprD'_weaken _ _ _ (getUVars ctx) (tvs'++getVars ctx) H8) as [ ? [ ? ? ] ].
      simpl in H.
      generalize (@exprD'_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H6 H4).
      intro. red in H10. revert Hlem. subst.
      simpl in *.
      rewrite Heqp in *.
      rewrite H7 in *.
      rewrite H4 in *.
      inv_all. subst.
      intros.
      intros; split; [ reflexivity | ].
      intros. eapply Pure_pctxD; eauto.
      intros. red.
      rewrite (H9 Hnil Hnil us0 (hlist_app vs' vs0)) in Hlem.
      eapply Hlem.
    Qed.

    Definition or_respectful
               (a b : expr typ func -> R -> mrw (list R))
    : respectful_dec :=
      fun e r => rw_orelse (a e r) (b e r).

    Theorem or_respectful_sound : forall a b,
        respectful_spec a ->
        respectful_spec b ->
        respectful_spec (or_respectful a b).
    Proof.
      unfold or_respectful. intros.
      red. intros.
      eapply rw_orelse_case in H1; destruct H1; [ eapply H | eapply H0 ];
      eassumption.
    Qed.

    Definition fail_respectful : respectful_dec :=
      fun _ _ => rw_fail.

    Theorem fail_respectful_sound : respectful_spec fail_respectful.
    Proof using.
      red. intros. inversion H.
    Qed.

    Require Import MirrorCore.RTac.IdtacK.

    Fixpoint do_respectful (propers : list (expr typ func * R))
    : respectful_dec :=
      match propers with
      | nil => fail_respectful
      | (f,rel) :: propers =>
        or_respectful
          (apply_respectful {| vars := nil
                             ; premises := nil
                             ; concl := {| relation := rel
                                         ; term := f |}
                             |} IDTACK)
          (fun x => do_respectful propers x)
      end.

    Theorem do_respectful_sound
    : forall propers,
        Forall (fun er =>
                  let '(e,r) := er in
                  match typeof_expr nil nil e with
                  | None => False
                  | Some t =>
                    match RD RbaseD r t
                        , exprD' nil nil e t
                    with
                    | Some rD , Some eD =>
                      Proper rD (eD Hnil Hnil)
                    | _ , _ => False
                    end
                  end) propers ->
        respectful_spec (do_respectful propers).
    Proof.
      induction 1.
      { eapply fail_respectful_sound. }
      { simpl. destruct x. eapply or_respectful_sound.
        { apply apply_respectful_sound.
          { clear - H.
            red. simpl. unfold lemmaD'. simpl.
            unfold Proper_conclD. simpl.
            forward. change_rewrite H1. apply H2. }
          { apply IDTACK_sound. } }
        { eauto. } }
    Qed.

  End get_respectful.

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