Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.EProver.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.LemmaExt.
Require Import MirrorCore.Ext.ExprSubst.
Require Import MirrorCore.Ext.ExprUnifySyntactic.

(** TODO **)
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
      forall vs' : HList.hlist _ tvs',
      exists val',
        exprD' (tus ++ tvs') tvs (openOver e (length tvs) (length tus)) t = Some val' /\
        forall us vs, val us (HList.hlist_app vs vs') = val' (HList.hlist_app us vs') vs.
  Proof.
(*
    clear. induction e; simpl; intros.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize (@exprD'_Var_App_L _ _ _ tus tvs' t tvs v H0).
        rewrite H. intros; forward.
        red_exprD. forward.
        subst. eexists; split; eauto. intros.
        inv_all; subst. auto. }
      { red_exprD.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_appR in H1; eauto with typeclass_instances. 2: omega.
        destruct H1.
        simpl in *.
        match goal with
          | |- context [ match ?X with _ => _ end ] =>
            consider X
        end; intros.
        { destruct s. simpl in *.
          eapply nth_error_get_hlist_nth_appR in H1; eauto with typeclass_instances. 2: omega.
          simpl in *. forward_reason.
          replace (v - length tvs + length tus - length tus) with (v - length tvs) in * by omega.
          simpl in *.
          match goal with
            | H : ?X = _ , H' : ?Y = _ |- _ =>
              change Y with X in H' ; rewrite H in H'
          end.
          inv_all. subst.
          rewrite typ_cast_typ_refl.
          eexists; split; eauto. simpl.
          intros. rewrite H2. auto. }
        { exfalso.
          apply nth_error_get_hlist_nth_None in H1.
          rewrite ListNth.nth_error_app_R in H1 by omega.
          replace (v - length tvs + length tus - length tus) with (v - length tvs) in * by omega.
          destruct H.
          eapply ExprDI.nth_error_get_hlist_nth_Some in H.
          destruct H. simpl in *. congruence. } } }
    { red_exprD.
      forward.
      inv_all; subst.
      eexists; split; eauto. }
    { red_exprD.
      forward. inv_all; subst.
      eapply openOver_typeof_expr in H0.
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
      eapply ExprDI.nth_error_get_hlist_nth_weaken with (ls' := tvs') in H0.
      simpl in *.
      forward_reason.
      rewrite H.
      rewrite typ_cast_typ_refl.
      eexists; split; eauto. simpl. intros. eauto. }
*)
  Admitted.

  Definition applicable (s : subst) (tus tvs : EnvI.tenv typ)
             (lem : lemma func (expr func)) (e : expr func)
  : option subst :=
    let pattern := openOver lem.(concl) 0 (length tus) in
    let fuel := 100 in
    @exprUnify subst _ _ RSym_func Subst_subst fuel (tus ++ lem.(vars)) tvs 0 s pattern e tyProp.

  Fixpoint copy_into (from len : nat) (src : subst) (acc : subst) : subst :=
    match len with
      | 0 => acc
      | S len => match lookup (from + len) src with
                   | None => copy_into from len src acc
                   | Some e => match set (from + len) e acc with
                                 | None => copy_into from len src acc
                                 | Some acc => copy_into from len src acc
                               end
                 end
    end.

  Fixpoint check_instantiated (from len : nat) (s : subst) : bool :=
    match len with
      | 0 => true
      | S len => match lookup (from + len) s with
                   | None => false
                   | Some _ => check_instantiated from len s
                 end
    end.

  Fixpoint check_and_drop (from len : nat) (s : subst) : option subst :=
    if check_instantiated from len s then
      Some (copy_into 0 from s (@empty subst (expr func) _))
    else
      None.

  Definition auto_prove_rec
             (auto_prove : hints.(Extern).(Facts) -> EnvI.tenv typ -> EnvI.tenv typ -> expr func -> subst -> option subst)
             (facts : hints.(Extern).(Facts))
             (tus tvs : EnvI.tenv typ) (g : expr func) (s : subst) : option subst :=
    match @Prove _ _ hints.(Extern) subst _ facts tus tvs s g with
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
              fold_right (fun h acc =>
                            match acc with
                              | None => None
                              | Some sub =>
                                let e :=
                                    instantiate (fun x => lookup x sub) 0
                                                (openOver h 0 len_tus)
                                in
                                auto_prove facts (tus ++ lem.(vars)) tvs e sub
                            end)
                         (Some sub)
                         lem.(premises)
            with
              | None => None
              | Some sub =>
                (** TODO: I need to post-process this, i.e. check that all new
                 **       unification variables are solved.
                 ** Then I need to remove them
                 **)
                check_and_drop len_tus from sub
            end
        in
        fold_right (fun x acc =>
                      match acc with
                        | None =>
                          check x
                        | Some res => Some res
                      end) None
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
       WellTyped_subst tus tvs s ->
       match exprD' tus tvs g tyProp with
         | None => True
         | Some valG =>
           forall us vs,
             Valid Hok.(ExternOk) (EnvI.join_env us) (EnvI.join_env vs) facts ->
             substD (EnvI.join_env us) (EnvI.join_env vs) s' ->
             valG us vs /\ substD (EnvI.join_env us) (EnvI.join_env vs) s
       end.

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
    forward.
    consider (Prove (Extern hints) facts tus tvs s g).
    { intros; inv_all; subst.
      generalize (Hok.(ExternOk).(Prove_correct) _ (EnvI.join_env us) (EnvI.join_env vs) facts H3 g s).
      repeat rewrite EnvI.typeof_env_join_env in *.
      intro XXX. specialize (XXX _ H0 H1 H4).
      simpl in *. unfold exprD in XXX.
      repeat rewrite EnvI.split_env_join_env in XXX.
      simpl in *.
      rewrite H2 in *. assumption. }
    { intro XXX; clear XXX.
      admit. }
  Qed.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.
