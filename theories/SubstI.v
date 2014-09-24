Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.OpenT.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Lemma hlist_build_app_if
: forall A T (F : T -> Type) G a b c d e f,
    @length T a = @length A c ->
    hlist_build F G (a ++ b) (c ++ d) = Some (hlist_app e f) ->
    hlist_build F G a c = Some e /\
    hlist_build F G b d = Some f.
Proof.
  clear.
  induction a; simpl; intros.
  { intuition; destruct c; simpl in *; try congruence.
    rewrite (hlist_eta e). reflexivity.
    rewrite (hlist_eta e) in H0. simpl in H0. assumption. }
  { destruct c; simpl in *; try congruence.
    inversion H; clear H; subst.
    forward. inv_all.
    rewrite (hlist_eta e) in *.
    simpl in *.
    assert (h = hlist_app (hlist_tl e) f).
    { inversion H1. inv_all. assumption. }
    subst.
    destruct (@IHa _ _ _ _ _ H2 H); clear IHa.
    rewrite H3. intuition. inversion H1; inv_all. subst; reflexivity. }
Qed.

Lemma hlist_build_app_only_if
: forall A T (F : T -> Type) G a b (c : list A) d e f,
    hlist_build F G a c = Some e ->
    hlist_build F G b d = Some f ->
    hlist_build F G (a ++ b) (c ++ d) = Some (hlist_app e f).
Proof.
  induction a; simpl; intros; forward.
  { rewrite (hlist_eta e). simpl. auto. }
  { inv_all; subst.
    simpl. eapply IHa in H0; eauto. rewrite H0. rewrite H2. reflexivity. }
Qed.

Section subst.
  Variable T : Type.
  Variable typ : Type.
  (** the [expr] type requires a notion of unification variable **)
  Variable RType_type : RType typ.
  Variable expr : Type.
  Variable Expr_expr : Expr _ expr.
  Variable ExprOk_expr : ExprOk _.
  Variable ExprUVar_expr : ExprUVar expr.
  Variable ExprUVarOk_expr : ExprUVarOk ExprUVar_expr.

  Let uvar : Type := nat.

  Class Subst :=
  { lookup : uvar -> T -> option expr
  ; domain : T -> list uvar
  }.

  Class SubstUpdate :=
  { set : uvar -> expr -> T -> option T
  ; drop : uvar -> T -> option T
  ; empty : T
  }.

  Inductive Roption {T} (r : Relation_Definitions.relation T) : Relation_Definitions.relation (option T) :=
  | Roption_None : Roption r None None
  | Roption_Some : forall x y, r x y -> Roption r (Some x) (Some y).

  Definition r tus : Relation_Definitions.relation (option (OpenT ctxD tus Prop)).
    eapply Roption.
    eapply OpenTrel.
    - intros. eapply OpenTrel.
      + exact (fun t => @eq _).
      + exact (@eq _).
    - exact (fun x y => x <-> y).
  Defined.

  Class SubstOk (S : Subst) : Type :=
  { WellFormed_subst : T -> Prop
  ; substD : forall (tus : _), T -> option (OpenT ctxD tus Prop)
  ; substD_respects
    : forall tus t, r (@substD tus t) (@substD tus t)
  ; substD_weaken
    : forall tus tus' s sD,
        substD tus s = Some sD ->
        exists sD',
          substD (tus ++ tus') s = Some sD' /\
          forall us us',
            sD us <-> sD' (hlist_app us us')
  ; substD_lookup
    : forall s uv e,
        WellFormed_subst s ->
        lookup uv s = Some e ->
        forall tus sD,
          substD tus s = Some sD ->
          exists t val get,
            nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ t get) /\
            exprD' tus t.(cctx) e t.(vtyp) = Some val /\
            forall us z,
              sD us ->
              get us z = val us z
  ; WellFormed_domain : forall s ls,
      WellFormed_subst s ->
      domain s = ls ->
      (forall n, In n ls <-> lookup n s <> None)
  }.

  Class SubstUpdateOk (S : Subst) (SU : SubstUpdate) (SOk : SubstOk S) :=
  { WellFormed_empty : WellFormed_subst empty
  ; substD_empty
    : forall tus,
      exists P,
        substD tus empty = Some P /\
        forall us, P us
  ; set_sound
      (** TODO(gmalecha): This seems to need to be rephrased as well **)
    : forall uv e s s',
        set uv e s = Some s' ->
        lookup uv s = None ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        forall tus t val get sD,
          substD tus s = Some sD ->
          nth_error_get_hlist_nth ctxD tus uv = Some (@existT _ _ t get) ->
          exprD' tus t.(cctx) e t.(vtyp) = Some val ->
          exists sD',
            substD tus s' = Some sD' /\
            forall us vs,
              sD' us ->
              sD us /\
              get us vs = val us vs
    (** NOTE: This is likely to only be used through [pull],
     ** so if it weakens/changes a little bit it is not a problem.
     **)
  ; drop_sound
    : forall s s' u,
        drop u s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        exists e,
          lookup u s = Some e /\
          lookup u s' = None /\
          (forall u', u' <> u -> lookup u' s = lookup u' s') /\
          forall tus tu sD,
            u = length tus ->
            substD (tus ++ tu :: nil) s = Some sD ->
            exists sD',
              substD tus s' = Some sD' /\
              exists eD,
                exprD' tus tu.(cctx) e tu.(vtyp) = Some eD /\
                forall us,
                  sD' us <->
                  sD (hlist_app us (Hcons (F:=ctxD) (eD us) Hnil))
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.

  Lemma substD_conv
  : forall tus tus' (pfu : tus' = tus) s,
      substD tus s =
      match pfu in _ = u' return option (OpenT _ u' Prop) with
        | eq_refl => substD tus' s
      end.
  Proof.
    clear. destruct pfu. reflexivity.
  Qed.

  (** This is the "obvious" extension of [drop] **)
  Fixpoint pull (from : uvar) (len : nat) (s : T) : option T :=
    match len with
      | 0 => Some s
      | S len' => match pull (S from) len' s with
                   | None => None
                   | Some s' => drop from s'
                  end
    end.

  Definition Subst_Extends (a b : T) : Prop :=
    forall tus P Q,
      substD tus b = Some P ->
      substD tus a = Some Q ->
      forall us, P us -> Q us.

  (** TODO: Maybe this should be essential **)
  Class NormalizedSubstOk : Type :=
  { lookup_normalized : forall s e u,
      WellFormed_subst s ->
      lookup u s = Some e ->
      forall u' e',
        lookup u' s = Some e' ->
        mentionsU u' e = false
  }.

  Fixpoint seq (start : nat) (len : nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

  Theorem pull_sound
  : forall (Hnormalized : NormalizedSubstOk) n s s' u,
      pull u n s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall tus tus' sD,
        u = length tus ->
        n = length tus' ->
        substD (tus ++ tus') s = Some sD ->
        exists eus',
          mapT (fun u => lookup u s) (seq u n) = Some eus' /\
          (forall u', u' < u \/ u' > u + n -> lookup u' s = lookup u' s') /\
          (forall u', u' < n -> lookup (u + u') s' = None) /\
        exists sD',
          substD tus s' = Some sD' /\
          exists us' : hlist (fun t => OpenT _ tus (ctxD t)) tus',
            @hlist_build _ _ _ (fun t e => exprD' tus t.(cctx) e t.(vtyp)) tus' eus' = Some us' /\
            forall us,
              let us' := hlist_map (fun t (x : OpenT _ tus (ctxD t)) => x us) us' in
              sD' us <->
              sD (hlist_app us us').
  Proof.
    Opaque mapT.
    induction n.
    { intros. simpl in *.
      inv_all. subst.
      split; auto.
      intros. subst.
      destruct tus'; try solve [ simpl in * ; congruence ].
      clear H1.
      exists nil. split; [ reflexivity | ].
      split; try reflexivity.
      split; [ inversion 1 | ].
      rewrite substD_conv with (pfu := eq_sym (app_nil_r_trans tus)) in H2.
      unfold OpenT in H2.
      autorewrite with eq_rw in H2.
      forwardy.
      eexists; split; eauto.
      simpl. eexists; split; eauto.
      inv_all. subst.
      simpl. intros. rewrite hlist_app_nil_r.
      autorewrite with eq_rw. reflexivity. }
    { simpl. intros. forwardy.
      eapply IHn in H; clear IHn; auto.
      forward_reason.
      eapply drop_sound in H1; auto.
      forward_reason; split; auto.
      intros; subst.
      rewrite list_mapT_cons.
      destruct tus'; try solve [ simpl in *; congruence ].
      specialize (H2 (tus ++ c :: nil) tus').
      rewrite substD_conv with (pfu := app_ass_trans tus (c :: nil) tus') in H9.
      unfold OpenT in H9.
      autorewrite with eq_rw in H9.
      forwardy.
      assert (S (length tus) = length (tus ++ c :: nil)).
      { rewrite app_length. simpl. omega. }
      assert (n = length tus').
      { simpl in *; congruence. }
      specialize (H2 _ H10 H11 H7); clear H10 H11.
      forward_reason.
      rewrite H10 by omega. rewrite H3.
      change_rewrite H2.
      eexists; split; eauto.
      split; [ | split ].
      { destruct 1.
        { rewrite H10; eauto. rewrite H5 by omega. reflexivity. }
        { rewrite H10 by omega. rewrite H5 by omega. reflexivity. } }
      { intros. destruct u'.
        { replace (length tus + 0) with (length tus) by omega.
          assumption. }
        { replace (length tus + S u') with (S (length tus) + u') by omega.
          rewrite <- H5 by omega.
          eapply H11. omega. } }
      { specialize (H6 tus _ _ eq_refl H12).
        forward_reason.
        eexists; split; eauto.
        simpl. rewrite H15.
        assert (exists us',
                  hlist_build (fun t : ctyp typ => exprT tus (cctx t) (typD (vtyp t)))
                              (fun (t : ctyp typ) (e : expr) => exprD' tus (cctx t) e (vtyp t))
                              tus' x0 = Some us' /\
                  forall us val,
                    hlist_hrel (fun (t : ctyp typ)
                                       (x : OpenT ctxD tus (ctxD t))
                                       (y : OpenT ctxD (tus ++ c :: nil) (ctxD t)) =>
                                     forall vs, x us vs = y (hlist_app us (Hcons val Hnil)) vs) us' x2).
        { clear H14. generalize dependent x2.
          assert (forall e, In e x0 ->
                            mentionsU (length tus) e = false).
          { intros.
            eapply mapT_In in H13; try eassumption.
            simpl in H13.
            forward_reason.
            eapply Hnormalized.
            2: eassumption. eassumption.
            rewrite <- H10 in H3. eapply H3.
            left. omega. }
          generalize tus'. clear H7 H2.
          induction x0.
          { intros. destruct tus'0; simpl in *; try congruence.
            inv_all; subst. eexists; split; eauto.
            intros. constructor. }
          { intros. destruct tus'0; simpl in *; try congruence.
            forwardy. inv_all; subst.
            eapply IHx0 in H2; eauto.
            forward_reason.
            change_rewrite H2.
            assert (exists val, exprD' tus c0.(cctx) a c0.(vtyp) = Some val /\
                                forall us vs v,
                                  val us vs = y2 (hlist_app us (Hcons v Hnil)) vs).
            { eapply exprD'_strengthenU_single in H7; eauto with typeclass_instances.
              forward_reason. eauto. }
            forward_reason. rewrite H9.
            eexists; split; eauto. intros.
            constructor; eauto. } }
        { forward_reason.
          change_rewrite H17.
          eexists; split; eauto.
          intros.
          inv_all; subst. clear H10 H11.
          rewrite H16; clear H16.
          rewrite H14; clear H14.
          simpl.
          rewrite hlist_app_assoc. simpl.
          repeat first [ rewrite eq_Const_eq | rewrite eq_Arr_eq ].
          specialize (substD_respects ((tus ++ c :: nil) ++ tus') s).
          rewrite H7. inversion 1. subst.
          eapply H11.
          match goal with
            | |- equiv_hlist _ match ?X with _ => _ end match ?Y with _ => _ end =>
              change Y with X ; destruct X
          end.
          rewrite <- equiv_hlist_app.
          split.
          - eapply Reflexive_equiv_hlist.
            intros. red. red. intros.
            eapply equiv_eq_eq in H9. destruct H9; reflexivity.
          - constructor.
            + red. intros. apply equiv_eq_eq in H9. destruct H9; reflexivity.
            + eapply hlist_hrel_equiv.
              specialize (H18 us (x4 us)).
              eapply hlist_hrel_map.
              2: eapply hlist_hrel_flip; eapply H18.
              simpl. clear H18.
              intros. red. intros.
              eapply equiv_eq_eq in H10. subst. symmetry. eapply H9. } } }
  Qed.

  Variable instantiate : (uvar -> list expr -> option expr) -> nat -> expr -> expr.

  Hypothesis exprD'_instantiate : InstantiateI.exprD'_instantiate _ _ instantiate.
(*
  Hypothesis instantiate_mentionsU : instantiate_mentionsU _ _ instantiate.
*)
  Lemma In_seq : forall a c b,
                   In a (seq b c) <-> (b <= a /\ a < b + c).
  Proof.
    clear.
    induction c; simpl; intros.
    { split. destruct 1. intros. omega. }
    { split; intros.
      { destruct H. subst. omega. eapply IHc in H. omega. }
      { consider (b ?[ eq ] a).
        { intros. subst; auto. }
        { right. eapply IHc. omega. } } }
  Qed.

(*
  Lemma sem_preserves_if_substD
  : forall tus tvs s sD,
      WellFormed_subst s ->
      substD tus s = Some sD ->
      sem_preserves_if tus sD (fun u => lookup u s).
  Proof.
    red. intros.
    eapply substD_lookup in H1; eauto.
    forward_reason.
    rewrite H2 in H1.
    inv_all; subst.
    eapply nth_error_get_hlist_nth_Some in H2.
    forward_reason. simpl in *.
    eexists; split; eauto.
  Qed.

  Theorem pull_for_instantiate_sound
  : forall (Hnormalized : NormalizedSubstOk) tus tus' tvs s s',
      pull (length tus) (length tus') s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall sD,
        substD (tus ++ tus') tvs s = Some sD ->
        exists sD',
          substD tus tvs s' = Some sD' /\
          (forall e t eD,
             exprD' (tus ++ tus') tvs e t = Some eD ->
             exists eD',
               exprD' tus tvs (instantiate (fun u => lookup u s) 0 e) t = Some eD' /\
               forall us vs us',
                 sD (hlist_app us us') vs ->
                 eD (hlist_app us us') vs = eD' us vs) /\
          forall us vs,
            exists us',
              sD' us vs <->
              sD (hlist_app us us') vs.
  Proof.
    intros.
    eapply pull_sound in H; eauto.
    forward_reason; split; auto.
    intros. specialize (H1 _ _ _ _ eq_refl eq_refl H2).
    forward_reason.
    eexists; split; eauto.
    split.
    { intros.
      red in exprD'_instantiate.
      eapply exprD'_instantiate with (tvs' := nil) in H8.
      revert H8.
      instantiate (1 := sD).
      instantiate (1 := (fun u : uvar => lookup u s)).
      simpl. intros.
      forward_reason.
      eapply exprD'_strengthenU_multi in H8; try eassumption.
      { forward_reason.
        eexists; split; eauto.
        intros.
        specialize (H10 us vs us').
        specialize (H9 (hlist_app us us') vs Hnil).
        simpl in H9.
        etransitivity; [ | eassumption ].
        auto. }
      { intros.
        match goal with
          | |- ?X = _ => consider X; auto
        end.
        intros. exfalso.
        red in instantiate_mentionsU.
        rewrite instantiate_mentionsU in H11.
        eapply mapT_success with (x := length tus + u) in H1.
        { forward_reason.
          destruct H11.
          { forward_reason; congruence. }
          { forward_reason.
            eapply Hnormalized in H0.
            2: eapply H11.
            2: eapply H1.
            congruence. } }
        { eapply In_seq. omega. } }
      { eapply sem_preserves_if_substD; eauto. } }
    { intros. eauto. }
  Qed.
*)
End subst.

Arguments pull {T expr SU} _ _ _ : rename.
