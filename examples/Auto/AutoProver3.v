Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver3.
Require Import MirrorCore.Subst.FastSubst.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.LemmaExt.
Require Import MirrorCore.Ext.ExprUnifySyntactic3.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section lem.
  Variables (ts : types) (func conclusion : Type).

  Record lemma : Type := Build_lemma
  { vars : list typ
  ;  premises : list (expr func)
  ;  concl : conclusion }.

  Variables (conclusionD : forall us vs : list typ,
                            conclusion ->
                            option
                              (hlist (typD ts nil) us -> hlist (typD ts nil) vs -> Prop))
           (RSym_func : RSym (typD ts) func).

  (** This is an alternative [lemmaD] **)
  Definition lemmaD' (tus tvs : tenv typ) (l : lemma)
  : ResType (typD ts) tus tvs Prop :=
    match
      Traversable.mapT (fun e : expr func => exprD' tus (vars l ++ tvs) e tyProp)
                       (premises l)
      , conclusionD tus (vars l ++ tvs) (concl l)
    with
      | Some prems , Some concl =>
        Some (fun us vs =>
                foralls ts
                        (fun h : hlist (typD ts nil) (vars l) =>
                           let vs' := hlist_app h vs in
                           impls
                             (map
                                (fun
                                    x : hlist (typD ts nil) tus ->
                                        hlist (typD ts nil) (vars l ++ tvs) -> Prop =>
                                    x us vs') prems) (concl us vs')))
      | _ , _ => None
    end.

  Lemma lemmaD'_weaken
  : forall tus tvs l lD,
      lemmaD' tus tvs l = Some lD ->
      forall tus' tvs',
        exists lD',
          lemmaD' (tus ++ tus') (tvs ++ tvs') l = Some lD' /\
          forall us us' vs vs',
            lD us vs <-> lD' (hlist_app us us') (hlist_app vs vs').
  Proof.
  Admitted.

  Definition lemmaD (us vs : env (typD ts)) (l : lemma) : Prop :=
    let (tus,us) := split_env us in
    let (tvs,vs) := split_env vs in
    match lemmaD' tus tvs l with
      | None => False
      | Some P => P us vs
    end.
End lem.

(** NOTE: This entire prover could be over an arbitrary logic if we change
 **       lemma to be over an arbitrary ILogic
 **)
Section parameterized.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : SymI.RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.

  (** TODO: This should be generalized **)
  Let Expr_expr := @Expr_expr ts func RSym_func.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

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
  Hypothesis hintsOk : HintsOk hints.

  (** TODO: This is already implemented elsewhere! **)
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

(*
  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      applicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        @lemmaD' ts func (expr func) (fun us tvs e => @exprD' ts func _ us tvs e tyProp) _ nil nil l0 = Some lD ->
        substD tus tvs s = sD ->
        exprD' tus tvs g tyProp = Some gD ->
        exists s1D,
          substD (tus ++ l0.(vars)) tvs s1 = Some s1D /\
          forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            exprD (join_env us) (join_env us' ++ join_env vs) l0.(concl) tyProp =
            exprD (join_env us) (join_env us' ++ join_env vs) g tyProp
            /\ substD (join_env us ++ join_env us') (join_env vs) s.
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
*)
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
    : forall (P : T -> Prop) (Q : U -> T -> Prop) (R : U -> U -> Prop),
        Reflexive R -> Transitive R ->
        (forall x y z,
           P x ->
           f' x y = Some z ->
           Q z x /\ R y z) ->
        (forall y z a,
           R y z -> P a -> Q y a -> Q z a) ->
        forall ls,
          Forall P ls ->
          forall acc res,
          all_success ls acc = Some res ->
          R acc res /\ Forall (Q res) ls.
    Proof.
      clear. admit. (*
      induction 4; simpl; intros.
      { inv_all; subst; auto. }
      { forward. admit. (*
        fill_holes.
        specialize (H1 _ _ _ H3 H5).
        specialize (IHForall _ _ H6). intuition.
        etransitivity; eauto.
        constructor; eauto. *) } *)
    Qed.

  End iteration.

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
       forall fD sD gD,
         factsD Hok.(ExternOk) tus tvs facts = Some fD ->
         substD tus tvs s = Some sD ->
         exprD' tus tvs g tyProp = Some gD ->
         exists sD',
           substD tus tvs s' = Some sD' /\
           forall us vs,
             fD us vs ->
             sD' us vs ->
             gD us vs /\ sD us vs.

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

  Ltac fill_holes :=
    let is_prop P := match type of P with
                       | Prop => idtac
                       | _ => fail
                     end
    in
    repeat match goal with
             | |- _ => progress intros
             | H : exists x , _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | |- exists x, _ /\ _ =>
               eexists; split; [ solve [ eauto ] | ]
             | |- _ /\ _ =>
               (split; eauto); [ ]
             | [ H : _ -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 specialize (H H')
             | [ H : forall x, @?X x -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 specialize (@H _ H')
             | [ H : forall x y, @?X x y -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ H')
                       | specialize (fun y => @H _ y H')
                       | specialize (fun x => @H x _ H')
                       | specialize (@H _ _ eq_refl)
                       | specialize (fun y => @H _ y eq_refl)
                       | specialize (fun x => @H x _ eq_refl)
                       ]
             | [ H : forall x y z, @?X x y z -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ _ H')
                       | specialize (fun x => @H x _ _ H')
                       | specialize (fun y => @H _ y _ H')
                       | specialize (fun z => @H _ _ z H')
                       | specialize (fun x y => @H x y _ H')
                       | specialize (fun y z => @H _ y z H')
                       | specialize (fun x z => @H x _ z H')
                       | specialize (@H _ _ _ eq_refl)
                       | specialize (fun x => @H x _ _ eq_refl)
                       | specialize (fun y => @H _ y _ eq_refl)
                       | specialize (fun z => @H _ _ z eq_refl)
                       | specialize (fun x y => @H x y _ eq_refl)
                       | specialize (fun y z => @H _ y z eq_refl)
                       | specialize (fun x z => @H x _ z eq_refl)
                       ]
             | [ H : forall x y z a, @?X x y z a -> _ , H' : ?P |- _ ] =>
               is_prop P ;
                 first [ specialize (@H _ _ _ _ H')
                       | specialize (fun x => @H x _ _ _ H')
                       | specialize (fun y => @H _ y _ _ H')
                       | specialize (fun z => @H _ _ z _ H')
                       | specialize (fun a => @H _ _ _ a H')
                       | specialize (fun x y => @H x y _ _ H')
                       | specialize (fun y z => @H _ y z _ H')
                       | specialize (fun z a => @H _ _ z a H')
                       | specialize (fun x a => @H x _ _ a H')
                       | specialize (fun x y z => @H x y z _ H')
                       | specialize (fun y z a => @H _ y z a H')
                       | specialize (fun x z a => @H x _ z a H')
                       | specialize (fun x y a => @H x y _ a H')
                       | specialize (fun x => @H x _ _ _ eq_refl)
                       | specialize (fun y => @H _ y _ _ eq_refl)
                       | specialize (fun z => @H _ _ z _ eq_refl)
                       | specialize (fun a => @H _ _ _ a eq_refl)
                       | specialize (fun x y => @H x y _ _ eq_refl)
                       | specialize (fun y z => @H _ y z _ eq_refl)
                       | specialize (fun z a => @H _ _ z a eq_refl)
                       | specialize (fun x a => @H x _ _ a eq_refl)
                       | specialize (fun x y z => @H x y z _ eq_refl)
                       | specialize (fun y z a => @H _ y z a eq_refl)
                       | specialize (fun x z a => @H x _ z a eq_refl)
                       | specialize (fun x y a => @H x y _ a eq_refl)
                       ]
           end.

  Lemma applicable_sound
  : forall s tus tvs l0 g s1,
      applicable s tus tvs l0 g = Some s1 ->
      WellFormed_subst s ->
      WellFormed_subst s1 /\
      forall lD sD gD,
        @lemmaD' ts func (expr func) (fun us tvs e => @exprD' ts func _ us tvs e tyProp) _ nil nil l0 = Some lD ->
        substD tus tvs s = Some sD ->
        exprD' tus tvs g tyProp = Some gD ->
        exists s1D,
          substD (tus ++ l0.(vars)) tvs s1 = Some s1D /\
          forall (us : hlist _ tus) (us' : hlist _ l0.(vars)) (vs : hlist _ tvs),
            s1D (hlist_app us us') vs ->
            exprD (join_env us) (join_env us' ++ join_env vs) l0.(concl) tyProp =
            Some (gD us vs)
            /\ sD us vs.
  Proof.
  Admitted.

  Lemma substD_weakenU
  : forall tus tvs tus' s sD,
      substD tus tvs s = Some sD ->
      exists sD',
        substD (tus ++ tus') tvs s = Some sD' /\
        forall a b c,
          sD a b <-> sD' (hlist_app a c) b.
  Proof.
  Admitted.

  Lemma list_mapT_cons
  : forall T U (F : T -> option U) ls a,
      Traversable.mapT F (a :: ls) =
      match match F a with
              | Some x => Some (cons x)
              | None => None
            end with
        | Some f =>
          match Traversable.mapT F ls with
            | Some x => Some (f x)
            | None => None
          end
        | None => None
      end.
  Proof. reflexivity. Qed.

  Lemma list_mapT_nil
  : forall T U (F : T -> option U),
      Traversable.mapT F nil = Some nil.
  Proof. reflexivity. Qed.

  Lemma auto_prove_rec_sound
  : forall recurse,
      auto_prove_sound_ind recurse ->
      auto_prove_sound_ind (auto_prove_rec recurse).
  Proof.
    red. unfold auto_prove_rec. intros.
    match goal with
      | _ : match ?X with _ => _ end = _ |- _ =>
        consider X; intros; inv_all; subst; auto
    end.
    { (** Extern **)
      eapply (@Prove_sound _ _ _ _ _ _ _ Hok.(ExternOk)) in H0.
      forward_reason.
      split; auto. intros.
      specialize (H2 _ _ _ H3 H4 H5).
      forward_reason.
      eexists; split; eauto.
      intros.
      specialize (H6 _ _ H7). intuition. }
    { (** Apply **)
      clear H0.
      eapply first_success_sound in H2.
      forward_reason.
      forward. subst.
      generalize (get_applicable_sound g (applicable s tus tvs) (Apply hints)).
      intro. eapply Forall_forall in H2; [ | eassumption ].
      simpl in *. clear H0. forward_reason.
      specialize (proj1 (Forall_forall _ _) (ApplyOk Hok) _ H0); intro.
      red in H5. simpl in *.
      forward.
      eapply applicable_sound in H2; eauto.
      simpl in *; forward_reason.
      specialize (fun sD gD => H7 _ sD gD H5).
      eapply lemmaD'_weaken with (tus' := tus) (tvs' := tvs) in H5.
      simpl in *. forward_reason.
      unfold lemmaD' in H5. forward.
      inv_all; subst. Opaque Traversable.mapT impls.
      specialize (fun us' vs' => H8 Hnil us' Hnil vs'). simpl in *.
      assert (forall us' vs',
                foralls ts
                        (fun h : hlist (typD ts nil) (vars l) =>
                           impls
                             (map
                                (fun x =>
                                   x us' (hlist_app h vs')) l0) (t us' (hlist_app h vs')))).
      { clear - H8 H6.
        intros. rewrite <- H8. assumption. }
      clear H8 H6.
      (** Before cutting this, I need to do pull_sound, that is what manifests
       ** the other environment...
       **)
      cut (
          WellFormed_subst s1 /\
          (forall fD sD gD,
              factsD (ExternOk Hok) tus tvs facts = Some fD ->
              substD (tus ++ vars l) tvs s0 = Some sD ->
              exprD' tus (vars l ++ tvs) (concl l) tyProp = Some gD ->
              exists sD',
                substD (tus ++ vars l) tvs s1 = Some sD' /\
                (forall (us : hlist (typD ts nil) tus)
                        (vs : hlist (typD ts nil) tvs)
                        (vs' : hlist (typD ts nil) (vars l)),
                   fD us vs ->
                   sD' (hlist_app us vs') vs ->
                      (impls
                         (map (fun x => x us (hlist_app vs' vs)) l0)
                         (gD us (hlist_app vs' vs)) ->
                       gD us (hlist_app vs' vs))
                   /\ sD (hlist_app us vs') vs))).
      { clear H3 H5 H recurse H0.
        intros.
        forward_reason.
        eapply pull_sound in H4; eauto.
        forward_reason.
        split; auto. intros.
        progress fill_holes.
        repeat match goal with
                 | H : _ |- _ => specialize (H us vs)
               end.
        match goal with
          | _ : let x := ?X in _ |- _ => remember X
        end.
        simpl in *.
        specialize (H12 h).
        fill_holes.
        unfold exprD in H11.
        rewrite split_env_app in H11.
        repeat rewrite split_env_join_env in H11.
        simpl in *.
        rewrite H9 in H11.
        inv_all.
        rewrite <- H11; clear H11.
        apply H12; clear H12.
        rewrite foralls_sem in H10.
        eapply H10. }
      { clear H4 H7 H10.
        generalize dependent l0.
        generalize dependent s0.
        generalize dependent (premises l).
        induction l0.
        { simpl. intros; inv_all; subst.
          rewrite list_mapT_nil in H5.
          inv_all; subst.
          split; auto. intros.
          eexists; split; eauto. }
        { simpl. intros.
          rewrite list_mapT_cons in H5.
          forward.
          specialize (H _ _ _ _ _ _ Hok H3 H2); clear H3.
          inv_all; subst.
          destruct H.
          specialize (IHl0 _ H8 H _ eq_refl).
          forward_reason. split; auto.
          intros.
          assert (exists fD',
                      factsD (ExternOk Hok) (tus ++ vars l) tvs facts = Some fD'
                      /\ forall a b c,
                           fD a b <-> fD' (hlist_app a c) b).
          { admit. }
          destruct H13 as [ ? [ ? ? ] ].
          assert (exists gD',
                    exprD' (tus ++ vars l) tvs
                           (instantiate (fun x : uvar => lookup x s0)
                                        (openOver a 0 (length tus))) tyProp = Some gD'
                    /\ forall a b c,
                         t0 a (hlist_app c b) <-> gD' (hlist_app a c) b).
          { admit. }
          destruct H15 as [ ? [ ? ? ] ].
          fill_holes.
          clear - H17 H18 H14 H16 H19 H20.
          eapply H14 in H19; clear H14.
          eapply H17 in H19; clear H17.
          destruct H19. split; auto.
          intros. eapply H18.
          eapply impls_sem. intros.
          rewrite impls_sem in H1. eapply H1.
          rewrite Forall_map in *.
          constructor; auto.
          apply H16. assumption. } } }
  Qed.

  Theorem auto_prove_sound
  : forall fuel, auto_prove_sound_ind (auto_prove fuel).
  Proof.
    induction fuel.
    { simpl. red. congruence. }
    { eapply auto_prove_rec_sound. eapply IHfuel. }
  Qed.

End parameterized.
