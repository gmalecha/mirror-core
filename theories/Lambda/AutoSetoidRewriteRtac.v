Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.ExprSubstitute.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
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
  Variable Req : Rbase -> Rbase -> bool.

  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R)
  | Rpointwise (t : typ) (r : R).

  Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

  Hypothesis RbaseD_single_type
  : forall r t1 t2 rD1 rD2,
      RbaseD r t1 = Some rD1 ->
      RbaseD r t2 = Some rD2 ->
      t1 = t2.

  (** This is due to universe problems! **)
  Definition respectful :=
    fun (A B : Type) (R : A -> A -> Prop) (R' : B -> B -> Prop) (f g : A -> B) =>
      forall x y : A, R x y -> R' (f x) (g y).
  Definition pointwise_relation :=
    fun (A B : Type) (R : B -> B -> Prop) (f g : A -> B) =>
      forall a : A, R (f a) (g a).

  Fixpoint RD (r : R) (t : typ) : option (typD t -> typD t -> Prop) :=
    match r with
      | Rinj r => RbaseD r t
      | Rrespects l r =>
        typ2_match (F:=Fun) (fun T => option (T -> T -> Prop)) t
                   (fun lt rt =>
                      match RD l lt , RD r rt with
                        | Some l , Some r => Some (respectful l r)
                        | _ , _ => None
                      end)
                   None
      | Rpointwise _t r =>
        typ2_match (F:=Fun) (fun T => option (T -> T -> Prop)) t
                   (fun lt rt =>
                      match type_cast t _t with
                        | Some _ =>
                          match RD r rt with
                            | Some r => Some (pointwise_relation (A:=typD lt) r)
                            | _ => None
                          end
                        | None => None
                      end)
                   None
    end.

  Theorem RD_single_type
  : forall r t1 t2 rD1 rD2,
      RD r t1 = Some rD1 ->
      RD r t2 = Some rD2 ->
      t1 = t2.
  Proof.
    clear - RbaseD_single_type Typ2Ok_Fun.
    induction r; simpl; intros.
    { eapply RbaseD_single_type; eauto. }
    { arrow_case_any; try congruence.
      red in x1. subst.
      destruct (typ2_match_case t1); forward_reason.
      { rewrite H2 in H. clear H1 H2.
        red in x3. subst.
        simpl in *.
        autorewrite with eq_rw in *. forward.
        inv_all; subst. specialize (IHr1 _ _ _ _ H H0).
        specialize (IHr2 _ _ _ _ H2 H5). subst; reflexivity. }
      { rewrite H2 in *. congruence. } }
    { arrow_case_any; try congruence.
      destruct (typ2_match_case t1); forward_reason.
      { rewrite H2 in *.
        red in x1; red in x4. subst.
        clear H2 H1. simpl in *.
        autorewrite with eq_rw in *.
        forward. }
      { rewrite H2 in *. congruence. } }
  Qed.

  Definition mrw (T : Type) : Type :=
    tenv typ -> tenv typ -> tenv typ -> nat -> nat -> forall c : Ctx typ (expr typ func), ctx_subst c ->
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

  Let rewrite_expr :=
    forall (es : list (expr typ func * (R -> mrw (expr typ func))))
           (rg : R),
      mrw (expr typ func).

  Existing Instance Expr_expr.

  Definition setoid_rewrite_rel (ctx : Ctx typ (expr typ func)) cs (tvs' : tenv typ)
             (e : expr typ func) (r : R) (rw : mrw (expr typ func)) : Prop :=
    forall cs' (e' : expr typ func) t rD,
      let tus := getUVars ctx in
      let tvs := getVars ctx in
      rw tvs' tus tvs (length tus) (length tvs) ctx cs = Some (e', cs') ->
      RD r t = Some rD ->
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst cs' /\
      match pctxD cs , exprD' tus (tvs' ++ tvs) t e
          , pctxD cs' , exprD' tus (tvs' ++ tvs) t e'
      with
      | Some _ , Some eD , Some csD' , Some eD' =>
        SubstMorphism cs cs' /\
        (forall (us : HList.hlist typD (getAmbientUVars ctx))
                (vs : HList.hlist typD (getAmbientVars ctx)),
            csD' (fun (us : HList.hlist typD (getUVars ctx))
                      (vs : HList.hlist typD (getVars ctx)) =>
                    forall vs',
                      rD (eD us (hlist_app vs' vs)) (eD' us (hlist_app vs' vs))) us vs)
      | None , _ , _ , _
      | Some _ , None , _ , _ => True
      | Some _ , Some _ , None , _
      | Some _ , Some _ , Some _ , None => False
      end.

  Definition setoid_rewrite_spec (rw : expr typ func -> R -> mrw (expr typ func)) : Prop :=
    forall tvs' ctx cs e r, @setoid_rewrite_rel ctx cs tvs' e r (rw e r).

  Definition respectful_spec (respectful : expr typ func -> R -> mrw (list R)) : Prop :=
    forall tvs' (ctx : Ctx typ (expr typ func)) cs cs' e r rs t ts rD,
      let tus := getUVars ctx in
      let tvs := getVars ctx in
      respectful e r tvs' tus tvs (length tus) (length tvs) ctx cs = Some (rs,cs') ->
      RD r t = Some rD ->
      WellFormed_ctx_subst cs ->
      WellFormed_ctx_subst cs' /\
      match pctxD cs
          , exprD' tus (tvs' ++ tvs) (fold_right (typ2 (F:=Fun)) t ts) e
          , pctxD cs'
          , RD (fold_right Rrespects r rs) (fold_right (typ2 (F:=Fun)) t ts)
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

  Section setoid_rewrite.
    Variable respectfulness
    : expr typ func -> rewrite_expr.

    Fixpoint setoid_rewrite (e : expr typ func)
             (es : list (expr typ func * (R -> mrw (expr typ func)))) (rg : R)
    : mrw (expr typ func) :=
      match e with
        | App f x =>
          setoid_rewrite f ((x, setoid_rewrite x nil) :: es) rg
        | Abs t e' =>
          match es with
            | nil => match rg with
                       | Rpointwise _t (*=t*) rg' =>
                         fun tvs tus tvs' nus nvs c cs =>
                           match @setoid_rewrite e' nil rg'
                                                 (t::tvs) tus tvs' nus nvs c cs
                           with
                           | Some (e'',cs'') =>
                             Some (Abs t e'', cs'')
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

    Let _lookupU (u : ExprI.uvar) : option (expr typ func) := None.
    Let _lookupV (under : nat) (v : ExprI.var) : option (expr typ func) :=
      if v ?[ ge ] under then
        None
      else
        Some (Var (under - 1 - v)).

(*
    Definition setoid_rewrite_rec tvs' ctx cs
      (ls : list (expr typ func * (R -> mrw (expr typ func))))
    : Prop :=
      Forall (fun e =>
                forall r,
                  @setoid_rewrite_rel ctx cs tvs' (expr_subst _lookupU (_lookupV (length tvs')) 0 (fst e)) r (snd e r)) ls.
*)

    Definition setoid_rewrite_rec tvs' ctx cs
      (ls : list (expr typ func * (R -> mrw (expr typ func))))
    : Prop :=
      Forall (fun e =>
                forall r,
                  @setoid_rewrite_rel ctx cs tvs' (fst e) r (snd e r)) ls.

(*
    Hypothesis respectfulness_sound
    : forall e e' tus tvs t es rg rD eesD,
        respectfulness e es rg = Some e' ->
        RD rg t = Some rD ->
        setoid_rewrite_rec tus tvs es ->

        exprD' tus tvs t (apps e (map fst es)) = Some eesD ->
        exists eesD',
          exprD' tus tvs t e' = Some eesD' /\
          forall us vs,
            rD (eesD us vs) (eesD' us vs).
*)

    Lemma _lookupV_self_ident : forall u v,
        match _lookupV u match _lookupV u v with
                         | Some (Var v') => v'
                         | _ => v
                         end
        with
        | Some (Var v') => v'
        | _ => v
        end = v.
    Proof.
      clear. subst _lookupV. simpl. intros.
      consider (v ?[ ge ] u); intros.
      { rewrite rel_dec_eq_true; eauto with typeclass_instances. }
      consider ((u - 1 - v) ?[ ge ] u); auto.
      { intros. red in v. simpl in *.
        unfold var. admit. (* omega *) }
    Qed.

    Hypothesis respectfulness_sound
    : forall e es rg ctx cs tvs',
        let under := length tvs' in
        @setoid_rewrite_rec tvs' ctx cs es ->
        @setoid_rewrite_rel ctx cs tvs'
                            (apps e (map fst es))
                            rg (respectfulness e es rg).

    Theorem setoid_rewrite_sound
    : forall ctx cs e es rg tvs',
        let under := length tvs' in
        @setoid_rewrite_rec tvs' ctx cs es ->
        @setoid_rewrite_rel ctx cs tvs'
                            (apps e (map fst es))
                            rg (setoid_rewrite e es rg).
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
        forwardy.
        arrow_case_any.
        { red in x1; subst.
          simpl in H1.
          autorewrite with eq_rw in H1.
          forwardy. inv_all; subst.
          specialize (IHe nil rg (t :: tvs') (Forall_nil _) _ _ _ _ H0 H6 H2).
          forward_reason; split; auto.
          destruct (pctxD cs) eqn:HpctxDcs; trivial.
          rewrite exprD'_Abs; eauto with typeclass_instances.
          rewrite typ2_match_iota; eauto with typeclass_instances.
          unfold Monad.bind, Monad.ret; simpl.
          autorewrite with eq_rw.
          destruct (type_cast x t) eqn:Htcxt; trivial.
          simpl in H5.
          destruct (exprD' (getUVars ctx) (t :: tvs' ++ getVars ctx) x0 e)
                   eqn:HexprDe; trivial.
          forwardy.
          rewrite H5.
          rewrite exprD'_Abs; eauto with typeclass_instances.
          rewrite typ2_match_iota; eauto with typeclass_instances.
          unfold Monad.bind, Monad.ret; simpl.
          autorewrite with eq_rw.
          rewrite Htcxt.
          rewrite H7.
          forward_reason.
          split; eauto.
          intros.
          generalize (H9 us vs); clear H9.
          eapply Ap_pctxD; eauto.
          eapply Pure_pctxD; eauto.
          clear. destruct r.
          intros.
          autorewrite with eq_rw.
          red. intros.
          eapply (H (Hcons a vs')). }
        { exfalso; clear - H1. congruence. } }
    Qed.
  End setoid_rewrite.

  Section top_bottom.
    Context (reflexive transitive : R -> bool)
            (rw : expr typ func -> R -> mrw (expr typ func))
            (respectful : expr typ func -> R -> mrw (list R)).

    Hypothesis reflexiveOk
    : forall r t rD, reflexive r = true -> RD r t = Some rD -> Reflexive rD.
    Hypothesis transitiveOk
    : forall r t rD, transitive r = true -> RD r t = Some rD -> Transitive rD.

    Hypothesis rwOk : setoid_rewrite_spec rw.
    Hypothesis respectfulOk : respectful_spec respectful.

    Lemma exprD'_App
    : forall tus tvs td tr f x fD xD,
        exprD' tus tvs (typ2 (F:=Fun) td tr) f = Some fD ->
        exprD' tus tvs td x = Some xD ->
        exprD' tus tvs tr (App f x) = Some (exprT_App fD xD).
    Proof.
      clear - Typ2Ok_Fun RSymOk_func RTypeOk_typD.
      intros.
      autorewrite with exprD_rw; simpl.
      erewrite exprD_typeof_Some by eauto.
      rewrite H. rewrite H0. reflexivity.
    Qed.

    Fixpoint apply_fold tus tvs t ts
             (es : HList.hlist (fun t => ExprI.exprT tus tvs (typD t)) ts)
    : ExprI.exprT tus tvs (typD (fold_right (typ2 (F:=Fun)) t ts))
      -> ExprI.exprT tus tvs (typD t) :=
      match es in HList.hlist _ ts
            return ExprI.exprT tus tvs (typD (fold_right (typ2 (F:=Fun)) t ts))
                   -> ExprI.exprT tus tvs (typD t)
      with
        | HList.Hnil => fun f => f
        | HList.Hcons t' ts x xs => fun f =>
                                      @apply_fold tus tvs t ts xs (exprT_App f x)
      end.

    Lemma apps_exprD'_fold_type
    : forall tus tvs es e t eD,
        exprD' tus tvs t (apps e es) = Some eD ->
        exists ts fD esD,
          exprD' tus tvs (fold_right (typ2 (F:=Fun)) t ts) e = Some fD /\
          hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                      (fun t e => exprD' tus tvs t e) ts es = Some esD /\
          forall us vs,
            eD us vs = @apply_fold _ _ _ _ esD fD us vs.
    Proof.
      clear - Typ2Ok_Fun RTypeOk_typD RSymOk_func.
      intros.
      rewrite exprD'_apps in H; eauto.
      unfold apps_sem' in H. forward. clear H.
      revert H0; revert H1; revert eD; revert t; revert e0; revert e.
      revert t0.
      induction es; simpl; intros.
      { exists nil. exists eD. exists HList.Hnil.
        simpl. split; eauto.
        forward. destruct r. inv_all; subst. assumption. }
      { arrow_case_any.
        { clear H.
          red in x1. subst.
          simpl in H1. autorewrite with eq_rw in H1.
          forward; inv_all; subst.
          eapply IHes with (e := App e a) in H1; eauto.
          { forward_reason.
            assert (x0 = fold_right (typ2 (F:=Fun)) t x1).
            { autorewrite with exprD_rw in H1; simpl in H1.
              forward; inv_all; subst.
              eapply exprD_typeof_Some in H0; eauto.
              eapply exprD_typeof_Some in H4; eauto.
              rewrite H0 in H4.
              inv_all. assumption. }
            { subst.
              eexists (x :: x1). exists e0.
              eexists. split; eauto.
              split. simpl.
              rewrite H2. rewrite H. reflexivity.
              simpl. intros.
              erewrite exprD'_App in H1; eauto.
              inv_all; subst. eauto. } }
          { erewrite exprD'_App; eauto.
            unfold exprT_App. autorewrite with eq_rw.
            reflexivity. } }
        { inversion H1. } }
    Qed.

    Inductive Forall3 {T U V : Type} (P : T -> U -> V -> Prop)
    : list T -> list U -> list V -> Prop :=
    | Forall3_nil : Forall3 P nil nil nil
    | Forall3_cons : forall t u v ts us vs,
                       P t u v -> Forall3 P ts us vs ->
                       Forall3 P (t :: ts) (u :: us) (v :: vs).

(*
    Theorem rw_map2_sound
    : forall T U V (f : T -> U -> mrw V) (P : T -> U -> V -> Prop) ts us vs,
        rw_map2 f ts us = Some vs ->
        (forall a b c, f a b = rw_ret c -> P a b c) ->
        Forall3 P ts us vs.
    Proof. clear. intros. revert H. revert vs; revert us.
           induction ts; destruct us; simpl in *;
           try solve [ inversion 1 ]; intros.
           { inversion H. constructor. }
           { specialize (H0 a u).
             destruct (f a u); [ simpl in H | inversion H ].
             specialize (IHts us).
             destruct (rw_map2 f ts us); inversion H.
             constructor; eauto. }
    Qed.
*)

    Fixpoint recursive_rewrite (f : expr typ func)
             (es : list (expr typ func * (R -> mrw (expr typ func))))
             (rs : list R)
    : mrw (expr typ func) :=
      match es , rs with
        | nil , nil => rw_ret f
        | e :: es , r :: rs =>
          rw_bind ((snd e) r)
                  (fun e' => recursive_rewrite (App f e') es rs)
        | _ , _ => rw_fail
      end.

    Definition mrw_equiv {T} (rT : T -> T -> Prop) (l : mrw T) (r : mrw T) : Prop :=
      forall a b c d e f g,
        Roption (Eqpair rT eq) (l a b c d e f g) (r a b c d e f g).

    Instance Reflexive_mrw_equiv {T} (rT : T -> T -> Prop) {Refl_rT : Reflexive rT}
    : Reflexive (mrw_equiv rT).
    red. red. intros. eapply Reflexive_Roption. eapply Reflexive_Eqpair; eauto.
    Qed.

    Instance Symmetric_mrw_equiv {T} (rT : T -> T -> Prop) {Sym_rT : Symmetric rT}
    : Symmetric (mrw_equiv rT).
    red. red. intros. eapply Symmetric_Roption. eapply Symmetric_Eqpair; eauto. eapply H.
    Qed.

    Instance Transitive_mrw_equiv {T} (rT : T -> T -> Prop) {Trans_rT : Transitive rT}
    : Transitive (mrw_equiv rT).
    red. red. intros. eapply Transitive_Roption. eapply Transitive_Eqpair; eauto with typeclass_instances.
    eapply H. eapply H0.
    Qed.

    Lemma rw_bind_assoc
    : forall {T U V} (c : mrw T) (k : T -> mrw U) (k' : U -> mrw V),
        mrw_equiv eq
                  (rw_bind (rw_bind c k) k')
                  (rw_bind c (fun x => rw_bind (k x) k')).
    Proof.
      clear. unfold rw_bind. simpl.
      red. intros.
      destruct (c a b c0 d e f g); try constructor.
      destruct p.
      eapply Reflexive_Roption. apply Reflexive_Eqpair; eauto.
    Qed.

    Lemma Proper_rw_bind (T U : Type)
    : Proper (mrw_equiv (@eq T) ==> (pointwise_relation (mrw_equiv (@eq U))) ==> mrw_equiv (@eq U)) (@rw_bind T U).
    Proof.
      clear. red. red. red. red. unfold rw_bind. intros.
      red in H.
      specialize (H a b c d e f g).
      destruct H. constructor.
      destruct H. subst.
      eapply H0.
    Qed.

    Lemma rw_bind_rw_ret
    : forall {T U} (x : T) (k : T -> mrw U),
        rw_bind (rw_ret x) k = k x.
    Proof. clear. reflexivity. Qed.

    Lemma rw_bind_rw_fail
    : forall {T U} (k : T -> mrw U),
        rw_bind rw_fail k = rw_fail.
    Proof. clear. reflexivity. Qed.

    Theorem recursive_rewrite_is_map2
    : forall f es rs,
        mrw_equiv (@eq _)
                  (recursive_rewrite f es rs)
                  (rw_bind (rw_map2 (fun e r => snd e r) es rs)
                           (fun es' => rw_ret (apps f es'))).
    Proof.
      clear.
      intros f es; revert f.
      induction es; destruct rs; simpl; intros; auto.
      { rewrite rw_bind_rw_ret. simpl. reflexivity. }
      { rewrite rw_bind_rw_fail. reflexivity. }
      { rewrite rw_bind_rw_fail. reflexivity. }
      { etransitivity.
        2: symmetry; eapply rw_bind_assoc.
        eapply Proper_rw_bind; auto. reflexivity.
        red; intros.
        rewrite IHes.
        etransitivity.
        2: symmetry; eapply rw_bind_assoc.
        eapply Proper_rw_bind; auto. reflexivity.
        red; intros.
        rewrite rw_bind_rw_ret. reflexivity. }
    Qed.

    Inductive Forall2_hlist2 {T U : Type} (F : U -> Type)
              (P : T -> forall u : U,F u -> F u -> Prop)
    : list T -> forall us : list U, HList.hlist F us -> HList.hlist F us -> Prop :=
    | Forall2_hlist2_nil : Forall2_hlist2 P nil HList.Hnil HList.Hnil
    | Forall2_hlist2_cons : forall t u x y ts us xs ys,
                              P t u x y ->
                              Forall2_hlist2 P ts xs ys ->
                              @Forall2_hlist2 T U F P (t :: ts) (u :: us)
                                              (HList.Hcons x xs)
                                              (HList.Hcons y ys).

    Record rw_concl : Type :=
    { lhs : expr typ func
    ; rel : R
    ; rhs : expr typ func }.

    Definition rw_lemma : Type := Lemma.lemma typ (expr typ func) rw_concl.

    Instance RelDec_eq_R : RelDec (@eq R).
    Admitted.

    (** Note, this is quite inefficient due to building and destructing the pair **)
    Fixpoint extend_ctx (tvs' : tenv typ)
             (ctx : Ctx typ (expr typ func)) (cs : ctx_subst ctx) {struct tvs'}
    : { ctx : Ctx typ (expr typ func) & ctx_subst ctx } :=
      match tvs' with
      | nil => @existT _ _ ctx cs
      | t :: tvs' =>
        match @extend_ctx tvs' ctx cs with
        | existT ctx' cs' => @existT _ _ (CAll ctx' t) (AllSubst cs')
        end
      end.

(*
    Definition R_typ : R -> option typ. Admitted.
*)

(*
let '(existT ctx' cs') := @extend_ctx _tvs ctx cs in
           let tvs' := match rev _tvs with
                       | nil => tvs
                       | rtvs => tvs ++ rtvs
                       end in
*)

    Definition core_rewrite (lem : rw_lemma) (tac : rtacK typ (expr typ func))
               (e : expr typ func)
    : tenv typ -> tenv typ -> nat -> nat ->
      forall c : Ctx typ (expr typ func), ctx_subst c -> option (expr typ func * ctx_subst c).
    refine (
        match typeof_expr nil lem.(vars) lem.(concl).(lhs) with
        | None => fun _ _ _ _ _ _ => None
        | Some t =>
          fun tus tvs nus nvs ctx cs =>
           let ctx' := CExs ctx (t :: lem.(vars)) in
           let cs' : ctx_subst ctx' := ExsSubst cs (amap_empty _) in
           match exprUnify 10 tus tvs 0 (vars_to_uvars 0 (S nus) lem.(concl).(lhs)) e t cs' with
           | None => None
           | Some cs'' =>
             let prems := List.map (fun e => GGoal (vars_to_uvars 0 (S nus) e)) lem.(premises) in
             match tac tus tvs nus nvs ctx' cs'' (GConj_list prems) with
             | Solved cs''' =>
               match cs''' in ctx_subst ctx
                     return match ctx with
                            | CExs z _ => option (expr typ func * ctx_subst z)
                            | _ => unit
                            end
               with
               | ExsSubst _ _ cs'''' sub =>
                 match amap_lookup nus sub with
                 | None => None
                 | Some e =>
                   if amap_is_full (S (length lem.(vars))) sub then
                     Some (e, cs'''')
                   else
                     None
                 end
               | _ => tt
               end
             | _ => None
             end
           end
        end).
    Defined.

    Definition apply_rewrite (l : rw_lemma * rtacK typ (expr typ func)) (e : expr typ func) (t : typ) (r : R)
    : tenv typ -> tenv typ -> nat -> nat ->
      forall c : Ctx typ (expr typ func), ctx_subst c -> option (expr typ func * ctx_subst c).
    refine (
      let '(lem,tac) := l in
      if lem.(concl).(rel) ?[ eq ] r then
        (fun tus tvs nus nvs ctx cs =>
           let ctx' := CExs ctx (t :: lem.(vars)) in
           let cs' : ctx_subst ctx' := ExsSubst cs (amap_empty _) in
           match exprUnify 10 tus tvs 0 (vars_to_uvars 0 (S nus) lem.(concl).(lhs)) e t cs' with
           | None => None
           | Some cs'' =>
             let prems := List.map (fun e => GGoal (vars_to_uvars 0 (S nus) e)) lem.(premises) in
             match tac tus tvs nus nvs ctx' cs'' (GConj_list prems) with
             | Solved cs''' =>
               match cs''' in ctx_subst ctx
                     return match ctx with
                            | CExs z _ => option (expr typ func * ctx_subst z)
                            | _ => unit
                            end
               with
               | ExsSubst _ _ cs'''' sub =>
                 match amap_lookup nus sub with
                 | None => None
                 | Some e =>
                   if amap_is_full (S (length lem.(vars))) sub then
                     Some (e, cs'''')
                   else
                     None
                 end
               | _ => tt
               end
             | _ => None
             end
           end)
      else
        (fun _ _ _ _ _ _ => None)).
    Defined.

    Definition dtree : Type := R -> list (rw_lemma * rtacK typ (expr typ func)).

(* This fast-path eliminates the need to build environments when unification is definitely going to fail
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

    Fixpoint rewrite_dtree (ls : list (rw_lemma * rtacK typ (expr typ func)))
    : dtree :=
        match ls with
        | nil => fun _ => nil
        | (lem,tac) :: ls =>
          let build := rewrite_dtree ls in
          fun r =>
            if r ?[ eq ] lem.(concl).(rel) then
              (lem,tac) :: build r
            else
              build r
        end.

    Instance Injective_mrw_equiv_rw_ret {T} (rT : T -> T -> Prop) (a b : T)
    : Injective (mrw_equiv rT (rw_ret a) (rw_ret b)) :=
    { result := rT a b }.
    Proof.
      unfold rw_ret. clear. intros. red in H.
      specialize (H nil nil nil 0 0 _ (@TopSubst _ _ nil nil)).
      inv_all. assumption.
    Defined.

    (** NOT TRUE **)
(*
    Lemma rw_map2_for_rewrite_recursive
    : forall es rs es',
        mrw_equiv eq (rw_map2 (fun ef r => snd ef r) es rs) (rw_ret es') ->
        forall (tvs' : tenv typ) ctx (cs : ctx_subst ctx) ts,
          let tus := getUVars ctx in
          let tvs := tvs' ++ getVars ctx in
          forall esD,
          setoid_rewrite_rec tvs' cs es ->
          Forall2 (fun t r => exists rD, RD r t = Some rD) ts rs ->
          hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                      (fun t e => exprD' tus tvs (fst e) t) ts es = Some esD ->
          exists esD',
            hlist_build (fun t => ExprI.exprT tus tvs (typD t))
                        (fun t e => exprD' tus tvs e t) ts es' = Some esD' /\
            Forall2_hlist2 (fun r t (e e' : ExprI.exprT tus tvs (typD t)) =>
                              forall us vs rD,
                                RD r t = Some rD ->
                                rD (e us vs) (e' us vs)) rs esD esD'.
    Proof.
      induction es; destruct ts; destruct rs; simpl in *; intros;
      try solve [ inversion H1 | inversion H2 ].
      { inversion H2; subst.
        inv_all. subst.
        eexists; split; eauto. constructor. }
      { unfold rw_bind in H.
        admit. (*
        forwardy. inv_all; subst.
        inversion H1; clear H1; subst.
        inversion H0; clear H0; subst.
        eapply IHes in H6; eauto.
        forward_reason.
        eapply H6 in H3; eauto.
        forward_reason.
        Cases.rewrite_all_goal.
        eexists; split; eauto.
        constructor; eauto.
        { intros. rewrite H1 in *. inv_all. subst. eauto. } *) }
    Qed.
*)

    Definition rw_bind_catch {T U : Type} (c : mrw T) (k : T -> mrw U) (otherwise : mrw U) : mrw U :=
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
    Proof.
      clear. unfold rw_orelse. intros.
      forward.
    Qed.
    Lemma rw_bind_catch_case
      : forall (T U : Type) (A : mrw T) (B : T -> mrw U) (C : mrw U)
               a b c d e f g h,
        @rw_bind_catch _ _ A B C a b c d e f g = h ->
        (exists x g', A a b c d e f g = Some (x,g') /\
                      B x a b c d e f g' = h) \/
        (C a b c d e f g = h /\ A a b c d e f g = None).
    Proof. clear.
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
    Proof. clear.
           unfold rw_bind. intros; forward.
           do 2 eexists; eauto.
    Qed.

(*
    Theorem recursive_rewrite_sound
    : forall tvs' t r rD',
        RD r t = Some rD' ->
        forall es ctx (cs : ctx_subst ctx) cs' f f' rs e',
          let tvs := getVars ctx in
          let tus := getUVars ctx in
        recursive_rewrite f' es rs tvs' tus tvs (length tus) (length tvs) cs = Some (e', cs') ->
        forall ts fD rD eD
               (Hrws : setoid_rewrite_rec tvs' cs es),
          exprD' tus (tvs' ++ tvs) (apps f (map fst es)) t = Some eD ->
          exprD' tus (tvs' ++ tvs) f (fold_right (typ2 (F:=Fun)) t ts) = Some fD ->
          RD (fold_right Rrespects r rs) (fold_right (typ2 (F:=Fun)) t ts) = Some rD ->
          match pctxD cs , exprD' tus (tvs' ++ tvs) f' (fold_right (typ2 (F:=Fun)) t ts)
              , pctxD cs'
          with
          | Some csD , Some fD' , Some csD' =>
            exists eD',
            exprD' tus (tvs' ++ tvs) e' t = Some eD' /\
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
    Proof.
      clear reflexiveOk transitiveOk rwOk respectfulOk.
      clear rw respectful reflexive transitive.
      induction es; destruct rs; simpl in *.
      { inversion 1; subst. clear H0.
        intros.
        consider (pctxD cs'); intros; trivial.
        assert (ts = nil) by admit.
        subst. simpl in *.
        consider (ExprDsimul.ExprDenote.exprD' (getUVars ctx) (tvs' ++ getVars ctx)
                                               t e'); intros; trivial.
        eexists; split; eauto.
        split; [ reflexivity | ].
        intros.
        eapply Pure_pctxD; eauto.
        intros.
        rewrite H1 in *. rewrite H2 in *.
        inv_all. subst. assumption. }
      { inversion 1. }
      { inversion 1. }
      { intros.
        eapply rw_bind_case in H0.
        forward_reason.
        arrow_case_any.
        { unfold Relim in H3; autorewrite with eq_rw in H3.
          forwardy; inv_all; subst.
          destruct ts.
          { exfalso. (*
            simpl in *.
            red in x3. subst.
            clear IHes. clear H5.
            assert ((TransitiveClosure.leftTrans (@tyAcc _ _)) x2 (typ2 x1 x2)).
            { constructor.
              eapply tyAcc_typ2R; eauto. }
            generalize dependent (typ2 x1 x2).
            revert r x2 y2.
                      *) admit. }
          { simpl in *.
            rewrite exprD'_apps in H1.
            inversion Hrws; clear Hrws; subst.
            specialize (@IHes _ _ _ (App f e') _ _ _ H4). (* e'? *)



        consider (snd a r0); simpl; intros.
        { arrow_case_any.
          unfold Relim in H4; autorewrite with eq_rw in H4.
          forwardy; inv_all; subst.
          destruct ts.
          { (** False **)
            simpl in *. red in x1. subst.
            clear IHes. exfalso. clear H6.
            revert H9 H. clear - Typ2Ok_Fun RTypeOk_typD.
            (* [R] has at most 1 type *)
            assert ((TransitiveClosure.leftTrans (@tyAcc _ _)) x0 (typ2 x x0)).
            { constructor.
              eapply tyAcc_typ2R; eauto. }
            generalize dependent (typ2 x x0).
            clear - Typ2Ok_Fun RTypeOk_typD.
            revert r x0 y2.
            induction rs.
            { intros; simpl in *.
              specialize (RD_single_type _ _ _ H9 H0).
              intros; subst.
              eapply (@Facts.wf_anti_sym _ _ (wf_leftTrans (@wf_tyAcc typ _ _))) in H.
              assumption. }
            { intros; simpl in *.
              arrow_case_any.
              { red in x2. subst. simpl in *. clear H1.
                autorewrite with eq_rw in *.
                forward. inv_all; subst.
                eapply IHrs.
                2: eapply H2. 2: eassumption.
                eapply TransitiveClosure.LTStep.
                2: eassumption.
                eapply tyAcc_typ2R; eauto. }
              { congruence. } } }
          { simpl in x1. red in x1.
            generalize dependent x1.
            intro. generalize x1.
            inv_all; subst; intros.
            generalize H1.
            rewrite exprD'_apps in H1; eauto.
            unfold apps_sem' in H1.
            forwardy.
            generalize (exprD'_typeof_expr _ (or_introl H2)).
            simpl in H1. intro.
            rewrite H10 in H1. unfold type_of_apply in H1.
            forwardy. simpl in H11.
            rewrite typ2_match_iota in H11; eauto.
            autorewrite with eq_rw in H11. forwardy.
            inv_all; subst.
            autorewrite with exprD_rw in H7. simpl in H7.
            revert H7. Cases.rewrite_all_goal.
            destruct y4.
            change_rewrite H2. intro.
            forwardy. inv_all; subst.
            intro. inversion Hrws; clear Hrws; subst.
            specialize (H15 _ _ H7 _ _ _ H0 H4).
            forward_reason.
            eapply IHes in H5; [ | eauto | eauto | eauto using exprD'_App
                                 | eauto using exprD'_App
                                 | eauto ].
            forward_reason.
            eexists; split; eauto.
            clear - H14 H15 RelDec_Correct_eq_typ.
            intros us vs.
            unfold relation.
            autorewrite with eq_rw.
            unfold exprT_App in *.
            generalize dependent (typ2_cast x (fold_right (typ2 (F:=Fun)) t ts)).
            revert x1. revert y2.
            simpl in *.
            intros.
            rewrite (UIP_refl x1) in H; clear x1.
            generalize dependent (typD (typ2 x (fold_right (typ2 (F:=Fun)) t ts))).
            intros; subst.
            eapply H15; clear H15.
            eapply H. eauto. }
          { inversion H4. } }
        { inversion H5. } }
    Qed.
     *)


    (*
    Lemma rw_orelse_sound : forall {T} (a b c : mrw T),
        rw_orelse a b = c ->
        (exists x, a = Some x /\ c = Some x) \/
        (a = rw_fail /\ b = c).
    Proof. clear. intros. destruct a; eauto. Qed.
     *)

    Definition bottom_up (e : expr typ func) (r : R)
    : mrw (expr typ func) :=
      setoid_rewrite
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
	     (rw_bind_catch (respectful e r)
                            (fun rs =>
                               rw_bind (recursive_rewrite e efs rs)
			               (fun e' =>
                                          if transitive r
                                          then rw_orelse (rw e' r) (rw_ret e')
                                          else rw_ret e'))
                            (fun x => rw (apps e es) r x))
	     (if reflexive r then rw_ret (apps e es) else rw_fail))
        e nil r.

(*
    Lemma bottom_up_sound_lem
    : forall ctx cs e rg tvs',
        let under := length tvs' in
        @setoid_rewrite_rel ctx cs tvs' e rg (bottom_up e rg).
    Proof.
      unfold bottom_up. intros.
      eapply setoid_rewrite_sound; eauto; try solve [ constructor ].
      clear rg tvs' e ctx cs.
      intros.
      red. intros.

      eapply rw_orelse_case in H0; destruct H0.
      { 
        eapply rw_bind_catch_case in H0; destruct H0.
        { forward_reason.
          
          eapply rw_bind_case in H3.
          forward_reason. simpl in H4.
          eapply respectfulOk in H0; destruct H0; eauto.
          consider (transitive rg); intros.
          { eapply rw_orelse_case in H6; destruct H6.
            { eapply rwOk in H6.


      eapply rw_orelse_sound in H2; destruct H2; forward_reason.
      { inv_all; subst.
        consider (respectful e0 rg0); intros.
        { unfold rw_bind in H6.
          forwardy.
          generalize H4.
          eapply apps_exprD'_fold_type in H4.
          forward_reason.
          intro.
          eapply respectfulOk in H2; eauto.
          forward_reason.
          eapply recursive_rewrite_sound with (r := rg0) (rs := l) in H6;
            eauto.
          forward_reason.
          cut (   (Transitive rD0 /\ rw y rg0 = Some x)
                  \/ (x = y)).
          { clear H7. destruct 1.
            { destruct H7.
              red in rwOk.
              eapply rwOk in H13. 3: eauto.
              2: eauto.
              destruct H13 as [ ? [ ? ? ] ].
              eexists; split; eauto.
              intros. etransitivity. eapply H12.
              eapply H11. eauto. }
            { subst.
              eexists; split; eauto.
              intros. eapply H12; eauto. eapply H11. } }
          { consider (transitive rg0); intros.
            * destruct (rw y rg0).
              + left.
                eapply transitiveOk in H7; eauto.
              + right. inversion H13. reflexivity.
            * right. inversion H13. reflexivity. } }
        { eapply rwOk in H6; eauto. } }
      { clear H2.
        consider (reflexive rg0); intros.
        { eapply reflexiveOk in H2; eauto.
          inversion H6.
          eexists; split; eauto. }
        { inversion H6. } }
    Qed.
*)

    Theorem bottom_up_sound
    : setoid_rewrite_spec bottom_up.
    Proof.
    Admitted.

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

End setoid.

(*
Definition my_respectfulness (f : expr typ func)
           (es : list (expr typ func * (RG -> mrw (expr typ func))))
           (rg : RG)
: mrw (expr typ func) :=
  rw_ret (apps f (List.map (fun x => fst x) es)).


Definition my_respectfulness' (f : expr nat nat)
               (es : list (expr nat nat * (RG (typ:=nat) nat -> mrw (typ:=nat) nat (expr nat nat))))
               (rg : RG (typ:=nat) nat)
    : mrw (typ:=nat) nat (expr nat nat) :=
      rw_ret (apps f (List.map (fun x => snd x rg) es)).

  Fixpoint build_big (n : nat) : expr nat nat :=
    match n with
      | 0 => Inj 0
      | S n => App (build_big n) (build_big n)
    end.

  Time Eval vm_compute in
      match setoid_rewrite (Rbase:=nat) (@my_respectfulness nat nat nat) (build_big 24) nil (RGinj 0) (rsubst_empty _) with
        | Some e => true
        | None => false
      end.
*)
