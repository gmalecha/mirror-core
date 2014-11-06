Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint hlist_build {T U} (F : T -> Type) (f : forall x : T, U -> option (F x))
           (ls : list T) (ls' : list U)
: option (hlist F ls) :=
  match ls as ls , ls' return option (hlist F ls) with
    | nil , nil => Some Hnil
    | l :: ls , l' :: ls' =>
      match hlist_build F f ls ls' with
        | None => None
        | Some res =>
          match f l l' with
            | None => None
            | Some x =>
              Some (Hcons x res)
          end
      end
    | _ , _ => None
  end.

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
  Variable expr : Type.
  Context {RType_type : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk _}.

  Let uvar : Type := nat.

  Class Subst :=
  { subst_lookup : uvar -> T -> option expr
  ; subst_domain : T -> list uvar
  }.

  Class SubstOk (S : Subst) : Type :=
  { WellFormed_subst : T -> Prop
  ; substD : forall (tus tvs : tenv typ), T -> option (exprT tus tvs Prop)
  ; substD_lookup
    : forall s uv e,
        WellFormed_subst s ->
        subst_lookup uv s = Some e ->
        forall tus tvs sD,
          substD tus tvs s = Some sD ->
          exists t val get,
            nth_error_get_hlist_nth _ tus uv = Some (@existT _ _ t get) /\
            exprD' tus tvs e t = Some val /\
            forall us vs,
              sD us vs ->
              get us = val us vs
  ; WellFormed_domain : forall s ls,
      WellFormed_subst s ->
      subst_domain s = ls ->
      (forall n, In n ls <-> subst_lookup n s <> None)
  ; lookup_normalized : forall s e u,
      WellFormed_subst s ->
      subst_lookup u s = Some e ->
      forall u' e',
        subst_lookup u' s = Some e' ->
        mentionsU u' e = false
  }.

  Class SubstWeakenable :=
  { subst_weakenU : nat -> T -> T }.

  Class SubstWeakenableOk S (SOk : SubstOk S) (SW : SubstWeakenable) :=
  { substD_weakenU
    : forall n s s',
        subst_weakenU n s = s' ->
        forall tus tvs tus' s sD,
          n = length tus' ->
          substD tus tvs s = Some sD ->
          exists sD',
            substD (tus ++ tus') tvs s' = Some sD' /\
            forall us us' vs,
              sD us vs <-> sD' (hlist_app us us') vs
  }.

  Class SubstUpdate :=
  { subst_set : uvar -> expr -> T -> option T
  ; subst_empty : T
    (** NOTE: This doesn't seem to be used! It really should be specific to
     *  the particular implementation
     *)
  }.

  Class SubstUpdateOk (S : Subst) (SU : SubstUpdate) (SOk : SubstOk S) :=
  { substR : forall (tus tvs : tenv typ), T -> T -> Prop
  ; WellFormed_empty : WellFormed_subst subst_empty
  ; substD_empty
    : forall tus tvs,
      exists P,
        substD tus tvs subst_empty = Some P /\
        forall us vs, P us vs
  ; set_sound
      (** TODO(gmalecha): This seems to need to be rephrased as well **)
    : forall uv e s s',
        subst_set uv e s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (subst_lookup uv s = None -> (* How important is this? *)
         forall tus tvs t val get sD,
           substD tus tvs s = Some sD ->
           nth_error_get_hlist_nth typD tus uv = Some (@existT _ _ t get) ->
           exprD' tus tvs e t = Some val ->
           exists sD',
             substD tus tvs s' = Some sD' /\
             substR tus tvs s s' /\
             forall us vs,
               sD' us vs <->
               (sD us vs /\ get us = val us vs))
  }.

  Class SubstInstantiatable :=
  { subst_instantiate : (uvar -> option expr) -> T -> T }.

  (** the range of [f] does not include anything in the domain of s **)
  Definition disjoint_from (f : uvar -> option expr) (ls : list uvar) : Prop :=
    (forall u, In u ls -> f u = None) /\
    (forall u e, f u = Some e ->
                 forall u', In u' ls -> mentionsU u' e = false).

  Class SubstInstantiatableOk (S : Subst) (SO : SubstOk S) (SI : SubstInstantiatable) :=
  { instantiate_sound
    : forall f s s',
        subst_instantiate f s = s' ->
        WellFormed_subst s ->
        forall tus tvs P sD,
          sem_preserves_if tus tvs P f ->
          substD tus tvs s = Some sD ->
          exists s'D,
            substD tus tvs s' = Some s'D /\
            forall us vs,
              P us vs ->
              (sD us vs <-> s'D us vs)
  ; WellFormed_instantiate
    : forall f s s',
        subst_instantiate f s = s' ->
        WellFormed_subst s ->
        disjoint_from f (subst_domain s) ->
        WellFormed_subst s'
  }.


  Class SubstOpen : Type :=
  { (* drop : uvar -> T -> option T *)
    split : uvar -> nat -> T -> option (T * T)
  ; strengthenV : nat -> nat -> T -> option T
  }.

  Fixpoint models (tus tvs : tenv typ) (tus' : tenv typ) (es : list (option expr))
  : option (hlist typD tus' -> exprT tus tvs Prop) :=
    match tus' as tus' , es
          return option (hlist typD tus' -> exprT tus tvs Prop)
    with
      | nil , nil => Some (fun _ _ _ => True)
      | tu' :: tus' , None :: es =>
        match models (tus ++ tu' :: nil) tvs tus' es with
          | None => None
          | Some x => Some (fun h us vs =>
                              x (hlist_tl h) (hlist_app us (Hcons (hlist_hd h) Hnil)) vs)
        end
      | tu' :: tus' , Some e :: es =>
        match models (tus ++ tu' :: nil) tvs tus' es with
          | None => None
          | Some x =>
            match exprD' (tus ++ tu' :: tus') tvs e tu' with
              | None => None
              | Some eD =>
                Some (fun h us vs =>
                           hlist_hd h = eD (hlist_app us h) vs
                        /\ x (hlist_tl h) (hlist_app us (Hcons (hlist_hd h) Hnil)) vs)
            end
        end
      | _ , _ => None
    end.

  Class SubstOpenOk (S : Subst) (SO : SubstOk S) (OS : SubstOpen) : Type :=
  { split_sound
    : forall u n s s' s'',
        split u n s = Some (s', s'') ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        WellFormed_subst s'' /\
        forall tus tvs tus' sD,
          substD (tus ++ tus') tvs s = Some sD ->
          u = length tus ->
          n = length tus' ->
          (forall uv,
             uv < length tus ->
             subst_lookup uv s' = None) /\
          exists sD' sD'',
            substD tus tvs s' = Some sD' /\
            substD (tus ++ tus') tvs s'' = Some sD'' /\
            forall us vs us',
              sD (hlist_app us us') vs <->
              (sD' us vs /\ sD'' (hlist_app us us') vs)
  ; strengthenV_sound
    : forall s n c s',
        strengthenV n c s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        forall tus tvs tvs' sD,
          substD tus (tvs ++ tvs') s = Some sD ->
          n = length tvs ->
          c = length tvs' ->
          exists sD',
            substD tus tvs s' = Some sD' /\
            forall us vs vs',
              sD us (hlist_app vs vs') <-> sD' us vs
(*
  ; strengthenU_sound
    : forall s n c,
        strengthenU n c s = true ->
        WellFormed_subst s ->
        forall tus tvs tus' sD,
          substD (tus ++ tus') tvs s = Some sD ->
          n = length tus ->
          c = length tus' ->
          exists sD',
            substD tus tvs s = Some sD' /\
            forall us vs us',
              sD (hlist_app us us') vs <-> sD' us vs
*)
  }.

  Context {Subst_subst : Subst}.
  Context {SubstOk_subst : SubstOk Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate}.
  Context {SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst}.
  Context {SubstOpen_subst : SubstOpen}.
  Context {SubstOpenOk_subst : @SubstOpenOk _ _ _}.

  Lemma substD_conv
  : forall tus tus' tvs tvs' (pfu : tus' = tus) (pfv : tvs' = tvs) s,
      substD tus tvs s =
      match pfu in _ = u' return option (exprT u' _ Prop) with
        | eq_refl =>
          match pfv in _ = v' return option (exprT _ v' Prop) with
            | eq_refl => substD tus' tvs' s
          end
      end.
  Proof.
    clear. destruct pfu. destruct pfv. reflexivity.
  Qed.

  Fixpoint all_Some (ls : list (option expr)) : bool :=
    match ls with
      | nil => true
      | None :: _ => false
      | Some _ :: ls => all_Some ls
    end.

  Fixpoint all_defined (from : uvar) (len : nat) (s : T) : bool :=
    match len with
      | 0 => true
      | S len =>
        match subst_lookup from s with
          | None => false
          | Some _ => all_defined (S from) len s
        end
    end.

  Definition subst_pull (from : uvar) (len : nat) (s : T) : option T :=
    match split from len s with
      | None => None
      | Some (t,s') =>
        if all_defined from len s' then Some t else None
    end.

(*
  Lemma substD_weakenU
  : forall tus tvs tus' s sD,
      substD tus tvs s = Some sD ->
      exists sD',
        substD (tus ++ tus') tvs s = Some sD' /\
        forall a b c,
          sD a b <-> sD' (hlist_app a c) b.
  Proof.
    intros.
    eapply substD_weaken with (tvs' := nil) in H.
    revert H.
    instantiate (1 := tus').
    intro. destruct H as [ ? [ ? ? ] ].
    exists (match app_nil_r_trans tvs in _ = t
                  return hlist typD (tus ++ tus') -> hlist typD t -> Prop
            with
              | eq_refl => x
            end).
    split.
    { clear - H. generalize dependent x.
      destruct (app_nil_r_trans tvs). auto. }
    { intros. rewrite H0.
      instantiate (1 := Hnil). instantiate (1 := c).
      rewrite hlist_app_nil_r.
      clear. revert x. revert b.
      destruct (app_nil_r_trans tvs). reflexivity. }
  Qed.

  Lemma substD_weakenV
  : forall tus tvs tvs' s sD,
      substD tus tvs s = Some sD ->
      exists sD',
        substD tus (tvs ++ tvs') s = Some sD' /\
        forall a b c,
          sD a b <-> sD' a (hlist_app b c).
  Proof.
    intros.
    eapply substD_weaken with (tus' := nil) in H.
    revert H.
    instantiate (1 := tvs').
    intro. destruct H as [ ? [ ? ? ] ].
    exists (match app_nil_r_trans tus in _ = t
                  return hlist typD t -> hlist typD _ -> Prop
            with
              | eq_refl => x
            end).
    split.
    { clear - H. generalize dependent x.
      destruct (app_nil_r_trans tus). auto. }
    { intros. rewrite H0.
      instantiate (1 := c). instantiate (1 := Hnil).
      rewrite hlist_app_nil_r.
      clear. revert x. revert a.
      destruct (app_nil_r_trans tus). reflexivity. }
  Qed.
*)

  Fixpoint seq (start : nat) (len : nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

  Inductive hlist_Forall2 T (F G : T -> Type) (P : forall t, F t -> G t -> Prop)
  : forall ls, hlist F ls -> hlist G ls -> Prop :=
  | hlist_Forall2_nil : hlist_Forall2 P Hnil Hnil
  | hlist_Forall2_cons : forall l ls x xs y ys,
                           @P l x y ->
                           hlist_Forall2 (ls := ls) P xs ys ->
                           hlist_Forall2 P (Hcons x xs) (Hcons y ys).

  Lemma pull_sound_syn
  : forall n s s' u,
      subst_pull u n s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall tus tus' tvs sD,
        u = length tus ->
        n = length tus' ->
        substD (tus ++ tus') tvs s = Some sD ->
        exists eus',
          mapT (fun u => subst_lookup u s) (seq u n) = Some eus' /\
          (forall u', u' < u \/ u' > u + n -> subst_lookup u' s = subst_lookup u' s') /\
          (forall u', u' < n -> subst_lookup (u + u') s' = None).
  Proof.
    unfold subst_pull.
    intros. forward.
    subst. inv_all; subst.
    eapply split_sound in H1; eauto.
    forward_reason; split; eauto.
    intros; subst.
    specialize (H3 _ _ _ _ H6 eq_refl eq_refl).
    forward_reason.
  Abort.


  Theorem subst_pull_sound
  : forall n s s' u,
      subst_pull u n s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall tus tus' tvs sD,
        u = length tus ->
        n = length tus' ->
        substD (tus ++ tus') tvs s = Some sD ->
        exists eus',
          mapT (fun u => subst_lookup u s) (seq u n) = Some eus' /\
          (forall u', u' < u \/ u' > u + n -> subst_lookup u' s = subst_lookup u' s') /\
          (forall u', u' < n -> subst_lookup (u + u') s' = None) /\
        exists sD',
          substD tus tvs s' = Some sD' /\
          exists us' : hlist (fun t => hlist typD tus -> hlist typD tvs -> typD t) tus',
            @hlist_build _ _ _ (fun t e => exprD' tus tvs e t) tus' eus' = Some us' /\
            forall us vs,
              let us' := hlist_map (fun t (x : hlist typD tus -> hlist typD tvs -> typD t) => x us vs) us' in
              sD' us vs <->
              sD (hlist_app us us') vs.
  Proof.
(*
    Opaque mapT.
    unfold pull; intros; forwardy.
    eapply split_sound in H; eauto.
    forward; inv_all; subst.
    forward_reason.
    split; eauto.
    intros; subst.
    




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
      rewrite substD_conv with (pfu := eq_sym (app_nil_r_trans tus)) (pfv := eq_refl) in H2.
      autorewrite with eq_rw in H2.
      forwardy.
      eexists; split; eauto.
      simpl. eexists; split; eauto.
      inv_all. subst.
      simpl. intros. rewrite hlist_app_nil_r.
      autorewrite with eq_rw. reflexivity. }
    { simpl. intros. forward.
      eapply IHn in H; clear IHn; auto.
      forward_reason.
      eapply drop_sound in H1; auto.
      forward_reason; split; auto.
      intros; subst.
      rewrite list_mapT_cons.
      destruct tus'; try solve [ simpl in *; congruence ].
      specialize (H2 (tus ++ t0 :: nil) tus' tvs).
      rewrite substD_conv with (pfv := eq_refl)
                               (pfu := app_ass_trans tus (t0 :: nil) tus') in H9.
      autorewrite with eq_rw in H9.
      forwardy.
      assert (S (length tus) = length (tus ++ t0 :: nil)).
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
      { specialize (H6 tus _ tvs _ eq_refl H12).
        forward_reason.
        eexists; split; eauto.
        simpl. rewrite H15.
        assert (exists us',
                  hlist_build
                    (fun t1 : typ =>
                       hlist typD tus -> hlist typD tvs -> typD t1)
                    (fun (t1 : typ) (e : expr) => exprD' tus tvs e t1) tus' x0 = Some us' /\
                  forall us vs val,
                    hlist_Forall2 (fun (t : typ)
                                       (x : hlist typD tus -> hlist typD tvs -> typD t)
                                       (y : hlist typD (tus ++ _ :: nil) -> hlist typD tvs -> typD t) =>
                                     x us vs = y (hlist_app us (Hcons val Hnil)) vs) us' x2).
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
            assert (exists val, exprD' tus tvs a t1 = Some val /\
                                forall us vs v,
                                  val us vs = y1 (hlist_app us (Hcons v Hnil)) vs).
            { eapply exprD'_strengthenU_single in H7; eauto.
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
          autorewrite with eq_rw.
          match goal with
            | |- _ ?X _ <-> _ ?Y _ =>
              cutrewrite (X = Y); try reflexivity
          end.
          apply match_eq_match_eq.
          f_equal. f_equal.
          revert H13 H17.
          specialize (H18 us vs (x4 us vs)).
          clear - H18.
          generalize dependent x0.
          revert H18; revert x2; revert x5; revert tus'.
          refine (@hlist_Forall2_ind _ _ _ _ _ _ _).
          { simpl. reflexivity. }
          { simpl; intros.
            destruct x0; try congruence.
            specialize (H1 x0).
            repeat match goal with
                     | H : context [ ?X ] , H' : match ?Y with _ => _ end = _ |- _ =>
                       change Y with X in H' ; destruct X ; try congruence
                   end.
            forwardy. inv_all. subst.
            rewrite H1; auto. rewrite H. reflexivity. } } } }
*)
  Abort.

  Theorem subst_pull_sound_sem
  : forall  n s s' u,
      subst_pull u n s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      forall tus tus' tvs sD,
        u = length tus ->
        n = length tus' ->
        substD (tus ++ tus') tvs s = Some sD ->
        exists sD',
          substD tus tvs s' = Some sD' /\
          exists us' : hlist (fun t => exprT tus tvs (typD t)) tus',
            forall us vs,
              let us' := hlist_map (fun t (x : exprT tus tvs (typD t)) => x us vs) us' in
              sD' us vs <->
              sD (hlist_app us us') vs.
  Proof.
    Opaque mapT.
    unfold subst_pull; intros; forwardy.
    eapply split_sound in H; eauto.
    forward; inv_all; subst.
    forward_reason.
    split; eauto.
    intros; subst.
  Admitted.


  Variable instantiate : (uvar -> option expr) -> nat -> expr -> expr.

  Hypothesis exprD'_instantiate : InstantiateI.exprD'_instantiate _ _ instantiate.

  Hypothesis instantiate_mentionsU : instantiate_mentionsU _ _ instantiate.

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

  Lemma sem_preserves_if_substD
  : forall tus tvs s sD,
      WellFormed_subst s ->
      substD tus tvs s = Some sD ->
      sem_preserves_if tus tvs sD (fun u => subst_lookup u s).
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

(*
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

Arguments subst_pull {T expr SS SO} _ _ _ : rename.
(*Arguments NormalizedSubstOk {_ _ _ _ _} _ {_} : rename.*)

(*
  Definition drop (from : uvar) (s : T) : option T :=
    let (nsub,val) := forget from s in
    match val with
      | None => None
      | Some _ => Some nsub
    end.

  Theorem drop_sound
  : forall s s' u,
      drop u s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      exists e,
        lookup u s = Some e /\
        lookup u s' = None /\
        (forall u', u' <> u -> lookup u' s = lookup u' s') /\
        forall tus tu tvs sD,
          u = length tus ->
          substD (tus ++ tu :: nil) tvs s = Some sD ->
          exists sD',
            substD tus tvs s' = Some sD' /\
            exists eD,
              exprD' tus tvs e tu = Some eD /\
              forall us vs,
                sD' us vs <->
                sD (hlist_app us (Hcons (eD us vs) Hnil)) vs.
*)

(*
  (** This is the "obvious" extension of [drop] **)
  Fixpoint pull (from : uvar) (len : nat) (s : T) : option T :=
    match len with
      | 0 => Some s
      | S len' => match pull (S from) len' s with
                   | None => None
                   | Some s' => drop from s'
                  end
    end.
*)
(*
  Definition Subst_Extends (a b : T) : Prop :=
    forall tus tvs P Q,
      substD tus tvs b = Some P ->
      substD tus tvs a = Some Q ->
      forall us vs, P us vs -> Q us vs.
*)
