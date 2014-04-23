Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI2.
Require Import MirrorCore.EProver.
Require Import MirrorCore.Subst.FastSubst.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.LemmaExt.
Require Import MirrorCore.Ext.ExprUnifySyntactic2.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

(** NOTE: This entire prover could be over an arbitrary logic if we change
 **       lemma to be over an arbitrary ILogic
 **)
Section parameterized.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : SymI.RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.

  Let Expr_expr := @Expr_expr ts func RSym_func.
  Local Existing Instance Expr_expr.

  Record Hints : Type :=
  { Apply : list (lemma func (expr func))
  ; Extern : @EProver typ (expr func)
  }.

  Record HintsOk (h : Hints) : Type :=
  { ApplyOk : Forall (@lemmaD ts func (expr func)
                              (fun us tvs g =>
                                 @exprD' ts _ RSym_func us tvs g tyProp)
                              RSym_func
                              nil nil) h.(Apply)
  ; ExternOk : @EProverOk _ (typD ts) (expr func) _ tyProp (fun x => x) h.(Extern)
  }.

  Section get_applicable.
    Variable subst : Type.
    Variable Subst_subst : Subst subst (expr func).
    Variable goal : expr func.

    Variable applicable : forall (l : lemma func (expr func)) (g : expr func),
      option subst.

    Fixpoint get_applicable (ls : list (lemma func (expr func)))
    : list (lemma func (expr func) * subst) :=
        match ls with
          | nil => nil
          | l :: ls =>
            match applicable l goal with
              | None => get_applicable ls
              | Some s => (l,s) :: get_applicable ls
            end
        end.
  End get_applicable.

  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr func).
  Variable SubstOk_subst : SubstOk _ Subst_subst.
  Variable SU : SubstUpdate subst (expr func).
  Variable SubstUpdateOk : SubstUpdateOk SU _.

  Variable hints : Hints.

  Fixpoint openOver (e : expr func) (skip add : nat) : expr func :=
    match e with
      | Var v =>
        if v ?[ lt ] skip then Var v
        else UVar (v - skip + add)
      | UVar _
      | Inj _ => e
      | App l r => App (openOver l skip add) (openOver r skip add)
      | Abs t e => Abs t (openOver e (S skip) add)
    end.

  Theorem openOver_typeof_expr (Z : SymI.RSym (typD ts) func)
  : forall tus e tvs tvs' t,
      typeof_expr tus (tvs ++ tvs') e = Some t ->
      typeof_expr (tus ++ tvs') tvs (openOver e (length tvs) (length tus)) = Some t.
  Proof.
    clear. induction e; simpl; intros; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { simpl. rewrite ListNth.nth_error_app_L in H; auto. }
      { simpl. rewrite ListNth.nth_error_app_R in H; auto. 2: omega.
        rewrite ListNth.nth_error_app_R; try omega.
        replace (v - length tvs + length tus - length tus) with (v - length tvs) by omega.
        auto. } }
    { forward. erewrite IHe1; eauto. erewrite IHe2; eauto. }
    { forward. eapply (IHe (t :: tvs) tvs') in H.
      simpl in *.
      rewrite H in *. auto. }
    { apply ListNth.nth_error_weaken; auto. }
  Qed.

  Lemma nth_error_join_env
  : forall ls (hls : HList.hlist (typD ts nil) ls) v t,
      nth_error ls v = Some t ->
      exists val,
        nth_error (EnvI.join_env hls) v = Some (@existT _ _ t val).
  Proof.
    clear.
    induction hls; simpl; intros.
    { destruct v; inversion H. }
    { destruct v; simpl in *; eauto.
      inversion H; clear H; subst. eauto. }
  Qed.

  Theorem openOver_exprD' (Z : SymI.RSym (typD ts) func)
  : forall tus e tvs t tvs' val,
      exprD' tus (tvs ++ tvs') e t = Some val ->
      exists val',
        exprD' (tus ++ tvs') tvs (openOver e (length tvs) (length tus)) t = Some val' /\
        forall us vs' vs, val us (HList.hlist_app vs vs') =
                          val' (HList.hlist_app us vs') vs.
  Proof.
(*
    clear. induction e; simpl; intros.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize (@exprD'_Var_App_L _ _ _ us tvs' t tvs v H0).
        rewrite H. intros; forward.
        red_exprD. forward. rewrite H1.
        eauto. }
      { red_exprD.
        eexists. split.
        2: reflexivity.
        unfold EnvI.lookupAs.
        rewrite ListNth.nth_error_app_R by omega.
        replace (v - length tvs + length us - length us) with (v - length tvs) by omega.
        revert H. gen_refl.
        pattern (nth_error (tvs ++ tvs') v) at 1 3.
        destruct (nth_error (tvs ++ tvs') v); try congruence.
        intros; forward. inv_all; subst.
        assert (nth_error tvs' (v - length tvs) = Some t).
        { rewrite ListNth.nth_error_app_R in e; eauto. omega. }
        generalize H.
        eapply  nth_error_join_env in H. intro.
        destruct H. rewrite H.
        simpl. red_exprD.
        f_equal.
        apply functional_extensionality.
        intros.
        rewrite HList.hlist_nth_hlist_app; eauto with typeclass_instances.
        cut (nth_error tvs v = None); intros.
        { gen_refl.
          generalize dependent (HList.cast1 tvs tvs' v).
          generalize dependent (HList.cast2 tvs tvs' v).
          change (let ZZZ := (HList.hlist_nth x0 v) in forall
                    (e0 : nth_error tvs v = None ->
                          nth_error tvs' (v - length tvs) = nth_error (tvs ++ tvs') v)
                    (e1 : forall v0 : typ,
                            nth_error tvs v = Some v0 -> Some v0 = nth_error (tvs ++ tvs') v)
                    (e2 : nth_error tvs v = nth_error tvs v),
                    x =
                    match
                      e in (_ = t'')
                      return
                      (match t'' with
                         | Some t0 => typD ts nil t0
                         | None => unit
                       end -> typD ts nil t)
                    with
                      | eq_refl => fun x1 : typD ts nil t => x1
                    end
                      (match
                          nth_error tvs v as k
                          return
                          (nth_error tvs v = k ->
                           match nth_error (tvs ++ tvs') v with
                             | Some t0 => typD ts nil t0
                             | None => unit
                           end)
                        with
                          | Some i =>
                            fun pf : nth_error tvs v = Some i =>
                              match
                                e1 i pf in (_ = z)
                                return
                                (match nth_error tvs v with
                                   | Some t0 => typD ts nil t0
                                   | None => unit
                                 end ->
                                 match z with
                                   | Some t0 => typD ts nil t0
                                   | None => unit
                                 end)
                              with
                                | eq_refl =>
                                  match
                                    eq_sym pf in (_ = w)
                                    return
                                    (match w with
                                       | Some t0 => typD ts nil t0
                                       | None => unit
                                     end -> typD ts nil i)
                                  with
                                    | eq_refl => fun x1 : typD ts nil i => x1
                                  end
                              end ZZZ
                          | None =>
                            fun pf : nth_error tvs v = None =>
                              match
                                e0 pf in (_ = z)
                                return
                                match z with
                                  | Some t0 => typD ts nil t0
                                  | None => unit
                                end
                              with
                                | eq_refl => HList.hlist_nth vs' (v - length tvs)
                              end
                        end e2)).
          intro. clearbody ZZZ. revert ZZZ.
          rewrite H2. intros.
          generalize (e0 e2).
          generalize dependent (nth_error (tvs ++ tvs') v).
          intros; subst.
          eapply EnvI.split_env_nth_error in H.
          rewrite EnvI.split_env_join_env in *. simpl in *.
          match goal with
            | _ : _ ?X |- _ = match _ with eq_refl => ?Y end =>
              change Y with X; generalize dependent X
          end.
          clear - H1. revert e4. rewrite H1. intros.
          uip_all.
          inv_all; subst. reflexivity. }
        { apply ListNth.nth_error_past_end. omega. } } }
    { red_exprD.
      forward.
      inv_all; subst.
      eexists; split; eauto. }
    { red_exprD.
      forward. inv_all; subst.
      eapply openOver_typeof_expr in H0.
      rewrite typeof_env_app.
      rewrite EnvI.typeof_env_join_env.
      rewrite typeof_env_length in *.
      rewrite H0.
      specialize (IHe1 _ _ _ _ H1 vs').
      specialize (IHe2 _ _ _ _ H2 vs').
      repeat match goal with
               | H : exists x, _ |- _ =>
                 destruct H
               | H : _ /\ _ |- _ => destruct H
             end.
      Cases.rewrite_all_goal.
      red_exprD.
      eexists; split; eauto.
      intros. simpl.
      rewrite <- H5. rewrite <- H4. reflexivity. }
    { red_exprD.
      forward. inv_all; subst.
      destruct (IHe (t :: tvs) _ _ _ H1 vs') as [ ? [ ? ? ] ].
      simpl in *.
      rewrite H. eexists; eauto; split; eauto.
      intros. simpl.
      eapply functional_extensionality. intros.
      rewrite <- H0. simpl. reflexivity. }
    { red_exprD.
      forward. inv_all; subst.
      eapply EnvI.lookupAs_weaken in H.
      rewrite H. eauto. }
  Qed. *)
  Admitted.

  Definition applicable (s : subst) (tus tvs : EnvI.tenv typ)
             (lem : lemma func (expr func)) (e : expr func)
  : option subst :=
    let pattern := openOver lem.(concl) 0 (length tus) in
    let fuel := 100 in
    @exprUnify subst _ _ RSym_func Subst_subst SU fuel (tus ++ lem.(vars)) tvs 0 s pattern e tyProp.

  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      applicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      (@lemmaD ts func (expr func) (fun us tvs e => @exprD' ts func _ us tvs e tyProp) _ nil nil l0 ->

      WellTyped_subst tus tvs s ->
      WellTyped_expr tus tvs g tyProp ->
      WellTyped_subst (tus ++ l0.(vars)) tvs s1 /\
      forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
        substD (join_env us ++ join_env us') (join_env vs) s1 ->
        exprD (join_env us) (join_env us' ++ join_env vs) l0.(concl) tyProp =
        exprD (join_env us) (join_env us' ++ join_env vs) g tyProp
        /\ substD (join_env us ++ join_env us') (join_env vs) s).
  Proof.
(*
    unfold applicable.
    intros.
    generalize exprUnify_sound.
    unfold unify_sound, unify_sound_ind.
    intro XXX; eapply XXX with (tv' := nil) in H; clear XXX;
    eauto with typeclass_instances.
    (** TODO : WellTyped_subst weaken, substD_weaken **)
  Qed.
*)
  Admitted.

  Definition Subst1_subst : SubstI.Subst subst (expr func) :=
    {| SubstI.set := @set _ _ SU
     ; SubstI.empty := @empty _ _ SU
     ; SubstI.lookup := @lookup _ _ Subst_subst
    |}.

  Instance Subst1Ok_subst : SubstI.SubstOk _ Subst1_subst :=
    { substD := @substD _ _ _ _ _ _ _
    ; WellTyped_subst := @WellTyped_subst _ _ _ _ _ _ _
    }.
  admit. admit. admit. admit. admit. admit.
  Defined.

  Section iteration.
    Context (T U : Type) (f : T -> option U).

    Fixpoint first_success  (ls : list T) : option U :=
      match ls with
        | nil => None
        | l :: ls =>
          match f l with
            | None => first_success ls
            | x => x
          end
      end.

    Lemma first_success_sound
    : forall ls val,
        first_success ls = Some val ->
        exists l,
          In l ls /\ f l = Some val.
    Proof.
      induction ls; simpl; intros.
      - congruence.
      - consider (f a); intros.
        + exists a. inv_all; subst. auto.
        + apply IHls in H0. destruct H0. intuition. eauto.
    Qed.

    Variable (f' : T -> U -> option U).

    Fixpoint all_success (ls : list T) (acc : U)
    : option U :=
      match ls with
        | nil => Some acc
        | l :: ls =>
          match f' l acc with
            | None => None
            | Some x => all_success ls x
          end
      end.

    Lemma all_success_sound
    : forall (P : T -> Prop) (Q : U -> Prop),
        (forall x y z,
           P x -> Q y ->
           f' x y = Some z -> Q z) ->
        forall ls,
          Forall P ls ->
          forall acc res,
          Q acc ->
          all_success ls acc = Some res ->
          Q res.
    Proof.
      clear.
      induction 2; simpl; intros.
      { inv_all; subst; auto. }
      { forward. eauto. }
    Qed.

  End iteration.

  Definition auto_prove_rec
             (auto_prove : hints.(Extern).(Facts) -> EnvI.tenv typ -> EnvI.tenv typ -> expr func -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus tvs : EnvI.tenv typ) (g : expr func) (s : subst) : option subst :=
    match @Prove _ _ hints.(Extern) subst Subst1_subst facts tus tvs s g with
      | Some s =>
        (** solved by extern **)
        Some s
      | None =>
        (** try resolution **)
        let len_tus := length tus in
        let check lem_sub :=
            (** check to make sure that all of the premises are provable **)
            let '(lem,sub) := lem_sub in
            let from := length lem.(vars) in
            match
              all_success (fun h sub =>
                             let e :=
                                 instantiate (fun x => lookup x sub)
                                             (openOver h 0 len_tus)
                             in
                             auto_prove facts (tus ++ lem.(vars)) tvs e sub)
                          lem.(premises)
                          sub
            with
              | None => None
              | Some sub =>
                (** TODO: I need to post-process this, i.e. check that all new
                 **       unification variables are solved.
                 ** Then I need to remove them
                 **)
                pull len_tus from sub
            end
        in
        first_success check
                      (@get_applicable subst g (applicable s tus tvs) hints.(Apply))
    end.

  Fixpoint auto_prove (fuel : nat)
           (facts : hints.(Extern).(Facts))
           (tus tvs : EnvI.tenv typ) (g : expr func) (s : subst) : option subst :=
    match fuel with
      | 0 => None
      | S fuel =>
        auto_prove_rec
          (fun facts a b c d => auto_prove fuel facts a b c d)
          facts tus tvs g s
    end.

  Definition auto_prove_sound_ind
             (auto_prove : forall (facts : hints.(Extern).(Facts))
                                  (tus tvs : EnvI.tenv typ) (g : expr func)
                                  (s : subst), option subst)
  := forall facts tus tvs g s s' (Hok : HintsOk hints),
       auto_prove facts tus tvs g s = Some s' ->
       WellFormed_subst s ->
       WellFormed_subst s' /\
       (WellTyped_subst tus tvs s ->
        match exprD' tus tvs g tyProp with
          | None => True
          | Some valG =>
            forall us vs,
              Valid Hok.(ExternOk) (EnvI.join_env us) (EnvI.join_env vs) facts ->
              substD (EnvI.join_env us) (EnvI.join_env vs) s' ->
              valG us vs /\ substD (EnvI.join_env us) (EnvI.join_env vs) s
        end).


  Lemma get_applicable_sound
  : forall g app lems,
      Forall (fun ls : (lemma func (expr func) * subst) =>
                let '(l,s) := ls in
                In l lems /\ app l g = Some s)
             (get_applicable g app lems).
  Proof.
    clear. induction lems; simpl; intros.
    { constructor. }
    { consider (app a g); intros.
      { constructor; eauto.
        eapply Forall_impl; eauto.
        simpl in *. destruct a0. intuition. }
      { eapply Forall_impl; eauto.
        simpl in *. destruct a0. intuition. } }
  Qed.

  Lemma auto_prove_rec_sound
  : forall recurse,
      auto_prove_sound_ind recurse ->
      auto_prove_sound_ind (auto_prove_rec recurse).
  Proof.
    red. unfold auto_prove_rec. intros.
    split.
    { match goal with
        | _ : match ?X with _ => _ end = _ |- _ =>
          consider X; intros; inv_all; subst; auto
      end.
      { admit. }
      { eapply first_success_sound in H2.
        forward_reason.
        destruct x. forward.
        eapply WellFormed_pull in H4; eauto.
        generalize (get_applicable_sound g (applicable s tus tvs) (Apply hints)).
        intro. eapply Forall_forall in H5. 2: eassumption.
        simpl in *.
        destruct H5.
        eapply all_success_sound in H3.
        eapply H3.
        { instantiate (1 := fun _ => True). simpl.
          intros. eapply H in H9.
          apply H9 in H8. intuition. }
        { apply Forall_forall. auto. }
        { destruct (applicable_sound _ _ _ _ _ H6 H1). auto. } } }
    intros.
    forward.
    match goal with
      | H : match ?X with _ => _ end = _ |- _ =>
        consider X; intros
    end.
    { intros; inv_all; subst.
      generalize (Hok.(ExternOk).(Prove_correct) Subst1Ok_subst (EnvI.join_env us) (EnvI.join_env vs) facts H4 g s).
      repeat rewrite EnvI.typeof_env_join_env.
      intro XXX. specialize (XXX _ H0 H2 H5).
      simpl in *. unfold exprD in XXX.
      repeat rewrite EnvI.split_env_join_env in XXX.
      simpl in *.
      rewrite H3 in *. assumption. }
    { clear H0.
      revert H6.
      generalize (get_applicable_sound g (applicable s tus tvs) (Apply hints)).
      generalize dependent (get_applicable g (applicable s tus tvs) (Apply hints)).
      induction 1.
      { simpl. congruence. }
      { simpl; intros.
        forward. inv_all; subst.
        admit. }
  Admitted.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.

