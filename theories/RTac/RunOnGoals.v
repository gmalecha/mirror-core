Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Section runOnGoals.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

(*
  Fixpoint forgets (from : nat) (ts : list typ) (s : FMapSubst.SUBST.raw expr)
  : list (option expr) :=
    match ts with
      | nil => nil
      | t :: ts =>
        let rr := forgets (S from) ts s in
        let ne := subst_lookup from s in
        ne :: rr
    end.

  Fixpoint remembers (from : nat) (tes : list (typ * option expr)) (s : subst)
  : option subst :=
    match tes with
      | nil => Some s
      | (_,None) :: tes' => remembers (S from) tes' s
      | (_,Some e) :: tes' =>
        (* This should not be necessary but to eliminate it, we must have a
         * syntactic soundness condition for [set] *)
        match subst_lookup from s with
          | None =>
            match subst_set from e s with
              | None => None
              | Some s' => remembers (S from) tes' s'
            end
          | Some _ => None
        end
    end.
*)

  Lemma iff_to_eq : forall P Q : Prop, P = Q -> (P <-> Q).
  Proof. clear; intros; subst; reflexivity. Qed.

(*
  Lemma remembers_spec
  : forall l tus tvs s s' sD gsD,
      WellFormed_subst s ->
(*      (forall x, x >= length tus -> lookup x s = None) -> *)
      remembers (length tus) l s = Some s' ->
      substD (tus ++ map fst l) tvs s = Some sD ->
      goal_substD tus tvs (map fst l) (map snd l) = Some gsD ->
      exists s'D,
        substD (tus ++ map fst l) tvs s' = Some s'D /\
        forall us vs, (gsD us vs /\ sD us vs) <-> s'D us vs.
  Proof.
    induction l; simpl; intros.
    { forward_reason; inv_all; subst.
      eexists; split; eauto. intros. tauto. }
    { forward_reason; inv_all; subst.
      destruct a; simpl in *.
      destruct o; forward; inv_all; subst.
      { replace (S (length tus)) with (length (tus ++ t :: nil)) in H6
          by (rewrite app_length; simpl; omega).
        rewrite substD_conv with (pfu := app_ass_trans tus (t :: nil) (map fst l))
                                   (pfv := eq_refl) in H1.
        rewrite exprD'_conv with (pfu := app_ass_trans tus (t :: nil) (map fst l))
                                   (pfv := eq_refl) in H2.
        autorewrite with eq_rw in H1.
        autorewrite with eq_rw in H2.
        forward; inv_all; subst.
        specialize (@IHl (tus ++ t :: nil) tvs).
        eapply set_sound in H5; eauto. destruct H5.
        assert (subst_lookup (length tus) s = None) by eauto.
        specialize (fun x y => H5 H7 _ _ t _ x _ H1 y H2); clear H7.
        assert (exists get,
                  nth_error_get_hlist_nth typD ((tus ++ t :: nil) ++ map fst l)
                                          (length tus) =
                  Some
                    (existT
                       (fun t0 : typ =>
                          hlist typD ((tus ++ t :: nil) ++ map fst l) -> typD t0) t get) /\
                  forall us us',
                    get (hlist_app us us') = hlist_get_cons_after_app us).
        { clear.
          induction tus; simpl.
          { eexists; split; eauto.
            unfold hlist_get_cons_after_app. simpl.
            intros. rewrite (hlist_eta us). reflexivity. }
          { destruct IHtus as [ ? [ ? ? ] ].
            rewrite H. eexists; split; eauto.
            intros. unfold hlist_get_cons_after_app.
            simpl. rewrite (hlist_eta us). simpl.
            rewrite H0.
            unfold hlist_get_cons_after_app.
            reflexivity. } }
        destruct H7 as [ ? [ ? ? ] ].
        eapply H5 in H7; clear H5.
        forward_reason.
        specialize (IHl _ _ _ _ H4 H6 H5 H3).
        forward_reason.
        rewrite substD_conv with (pfu := eq_sym (app_ass_trans tus (t :: nil) (map fst l)))
                                   (pfv := eq_refl) in H10.
        autorewrite with eq_rw in H10. simpl in *.
        forward.
        eexists; split; eauto.
        inv_all; subst. intros.
        autorewrite with eq_rw.
        specialize (H11 (hlist_app (hlist_app (fst (hlist_split _ _ us))
                                              (Hcons (hlist_hd (snd (hlist_split _ _ us))) Hnil))
                                   (hlist_tl (snd (hlist_split _ _ us)))) vs).
        specialize (H9 (hlist_app (hlist_app (fst (hlist_split _ _ us))
                                              (Hcons (hlist_hd (snd (hlist_split _ _ us))) Hnil))
                                   (hlist_tl (snd (hlist_split _ _ us)))) vs).
        specialize (H8 (hlist_app (fst (hlist_split _ _ us))
                                  (Hcons (hlist_hd (snd (hlist_split _ _ us))) Hnil))
                                   (hlist_tl (snd (hlist_split _ _ us)))).
        rewrite <- (hlist_app_hlist_split _ _ us).
        revert H9. revert H8. revert H11.
        clear. rewrite hlist_app_assoc.
        simpl.
        generalize dependent (app_ass_trans tus (t :: nil) (map fst l)).
        generalize dependent (hlist_split tus (t :: map fst l) us).
        clear.
        generalize dependent ((tus ++ t :: nil) ++ map fst l).
        intros; subst. simpl in *.
        assert ((Hcons (hlist_hd (snd p)) (hlist_tl (snd p))) = snd p).
        { rewrite (hlist_eta (snd p)). f_equal. }
        rewrite H in *.
        rewrite and_comm.
        rewrite and_assoc. rewrite and_comm in H11.
        rewrite <- H11; clear H11.
        rewrite H8 in H9; clear H8.
        rewrite H9; clear H9.
        repeat rewrite <- and_assoc.
        eapply and_iff. reflexivity.
        intro. rewrite and_comm.
        eapply and_iff; eauto.
        { eapply iff_to_eq. f_equal. rewrite <- H. simpl.
          clear.
          generalize dependent (fst p).
          generalize dependent (hlist_hd (snd p)).
          generalize dependent (hlist_tl (snd p)).
          clear.
          induction h0.
          { reflexivity. }
          { simpl. unfold hlist_get_cons_after_app in *. simpl.
            eauto. } }
        { intros. reflexivity. } }
      { autorewrite with eq_rw in H2. forward; inv_all; subst.
        replace (S (length tus)) with (length (tus ++ t :: nil)) in H0
          by (rewrite app_length; simpl; omega).
        rewrite substD_conv with (pfu := app_ass_trans tus (t :: nil) (map fst l))
                                   (pfv := eq_refl) in H1.
        autorewrite with eq_rw in H1. forward; inv_all; subst.
        specialize (@IHl (tus ++ t :: nil) tvs _ _ _ _ H H0 H1 H2).
        forward_reason.
        rewrite substD_conv with (pfu := eq_sym (app_ass_trans tus (t :: nil) (map fst l)))
                                   (pfv := eq_refl) in H3.
        autorewrite with eq_rw in H3.
        forward; inv_all; simpl in *; subst.
        eexists; split; eauto.
        intros.
        autorewrite with eq_rw.
        etransitivity; [ eapply H4 | clear H4 ].
        autorewrite with eq_rw. reflexivity. } }
  Qed.
*)

  Lemma map_fst_combine : forall {T U} (ts : list T) (us : list U),
                            length ts = length us ->
                            map fst (combine ts us) = ts.
  Proof.
    clear.
    induction ts; simpl; intros; auto.
    destruct us. inversion H.
    simpl. f_equal. auto.
  Qed.

  Lemma map_snd_combine : forall {T U} (ts : list T) (us : list U),
                            length ts = length us ->
                            map snd (combine ts us) = us.
  Proof.
    clear.
    induction ts; destruct us; simpl; intros; auto.
    congruence. f_equal. auto.
  Qed.

(*
  Lemma forgets_length : forall z y x,
                           length y = length (forgets x y z).
  Proof.
    induction y; simpl; auto.
  Qed.

  Lemma forgets_spec
  (** TODO: There needs to be an extra requirement here that says that
   ** the domain of s is in some way related to the range.
   **)
  : forall tvs ts tus s sD,
      WellFormed_subst s ->
      substD (tus ++ ts) tvs s = Some sD ->
      exists s'D,
        goal_substD tus tvs ts (forgets (length tus) ts s) = Some s'D /\
        forall us vs,
          s'D us vs <-> sD us vs.
  Proof.
(*
    induction ts; simpl; intros.
    { admit. (* eexists; split; eauto. simpl; auto. *) }
    { consider (lookup (length tus) s); intros.
      { admit. (*eapply substD_lookup in H1; eauto.
                forward_reason.
                assert (x = a) by admit.
                subst.
                rewrite substD_conv with (pfu := app_ass_trans tus (a :: nil) ts)
                                         (pfv := eq_refl) in H0.
                autorewrite with eq_rw in H0.
                forward; inv_all; subst.
                specialize (IHts (tus ++ a :: nil) s _ H H0).
                forward_reason.
                rewrite app_length in H4. simpl in H4.
                rewrite Plus.plus_comm in H4.
                simpl in H4.
                rewrite H4.
                eexists; split; eauto.
                intros us vs H'; generalize (H3 us vs H'); clear H3.
                autorewrite with eq_rw.
                intros.
                split.
                { eapply H5. revert H'.
                  autorewrite with eq_rw.
                  clear.
                  Lemma eq_sym_eq_sym : forall T (x y : T) (pf : x = y),
                                          eq_sym (eq_sym pf) = pf.
                  Proof.
                    clear. destruct pf. reflexivity.
                  Qed.
                  rewrite eq_sym_eq_sym.
                  tauto. }
                { unfold hlist_get_cons_after_app.
                  rewrite <- H3. revert H1. clear. intro.
                  induction tus; simpl.
                  { simpl in *. inv_all; subst.
                    unfold hlist_nth. rewrite (hlist_eta us); simpl.
                    rewrite <- (hlist_eta us).
                    rewrite H.
                    clear. autorewrite with eq_rw.
                    admit. (** UIP: There should be a more natural phrasing **) }
                  { admit. } } *) }
      { admit. } }
*)
  Admitted.
*)

  Lemma eta_ctx_subst_exs c ts (s : ctx_subst (CExs c ts))
  : exists y z,
      s = ExsSubst (typ:=typ) (expr:=expr) z y.
  Proof.
    refine (match s in @ctx_subst _ _ X
                  return match X as X return @ctx_subst _ _ X -> Prop with
                           | CExs c ts => fun s =>
                             exists (y : _) (z : ctx_subst  c), s = ExsSubst z y
                           | _ => fun _ => True
                         end s
            with
              | ExsSubst _ _ _ s => _
              | _ => I
            end).
    eauto.
  Qed.
(*
  Instance Injective_WellFormed_ctx_subst_ExsSubst ctx ts c s
  : Injective (WellFormed_ctx_subst (c:=CExs ctx ts) (ExsSubst c s)) :=
    { result := WellFormed_ctx_subst c /\ WellFormed_subst s }.
  intro.
  refine match H in @WellFormed_ctx_subst _ _ _ _ _ _ _ C S
               return match C as C return ctx_subst subst C -> Prop with
                        | CExs _ _ => fun s' =>
                                        let (s,c) := fromExs s' in
                                        WellFormed_ctx_subst c /\ WellFormed_subst s
                        | _ => fun _ => True
                      end S
         with
           | WF_ExsSubst t c s s' pfs' pfs => conj  pfs pfs'
           | _ => I
         end.
  Defined.
*)

  Variable tac : rtac typ expr.

  Fixpoint all_instantiated (tes : list (typ * option expr)) : bool :=
    match tes with
      | nil => true
      | (_,None) :: _ => false
      | (_,Some _) :: tes => all_instantiated tes
    end.

  Fixpoint runOnGoals (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst ctx) (g : Goal typ expr)
           {struct g}
  : Result ctx :=
    match g with
      | GGoal e => @tac tus tvs nus nvs ctx s e
      | GSolved => Solved s
      | GAll t g =>
        match @runOnGoals tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromAll s)
          | More_ s g => More (fromAll s) (GAll t g)
        end
      | GExs ts sub g =>
        let s' := ExsSubst s sub in
        match @runOnGoals (tus ++ ts) tvs (length ts + nus) nvs (CExs ctx ts) s' g with
          | Fail => Fail
          | Solved s'' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I can drop anything that is already instantiated. **)
            More_ cs' (GExs ts shere GSolved)
          | More_ s'' g' =>
            let '(shere,cs') := fromExs s'' in
            (** Here I need to drop already instantiated vars and
             ** substitute through. Ideally, I should collapse as much
             ** as possible.
             **)
            More_ cs' (GExs ts shere g')
        end
      | GHyp h g =>
        match @runOnGoals tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
          | Fail => Fail
          | Solved s => Solved (fromHyp s)
          | More_ s g => More_ (fromHyp s) (GHyp h g)
        end
      | GConj_ l r =>
        (** NOTE: It would be nice if I could eagerly
         ** instantiate [r] with any results that came
         ** from [l].
         **)
        match @runOnGoals tus tvs nus nvs ctx s l with
          | Fail => Fail
          | Solved s' => @runOnGoals tus tvs nus nvs ctx s' r
          | More_ s' g' =>
            match @runOnGoals tus tvs nus nvs ctx s' r with
              | Fail => Fail
              | Solved s'' => More s'' g'
              | More_ s'' g'' => More_ s'' (GConj_ g' g'')
            end
        end
    end.

  Fixpoint runOnGoals_list (tacs : list (rtac typ expr)) (tus tvs : tenv typ) (nus nvs : nat)
           (ctx : Ctx typ expr) (s : ctx_subst ctx) (g : Goal typ expr)
           {struct g}
  : Result ctx * list (rtac typ expr) :=
    match g with
      | GGoal e =>
        match tacs with
          | nil => (Fail, nil)
          | tac :: tacs => (@tac tus tvs nus nvs ctx s e, tacs)
        end
      | GSolved => (Solved s, tacs)
      | GAll t g =>
        match @runOnGoals_list tacs tus (tvs ++ t :: nil) nus (S nvs) (CAll ctx t) (AllSubst s) g with
          | (Fail, tacs) => (Fail,tacs)
          | (Solved s, tacs) => (Solved (fromAll s), tacs)
          | (More_ s g, tacs) => (More (fromAll s) (GAll t g), tacs)
        end
      | GExs ts sub g =>
        let s' := ExsSubst s sub in
            match @runOnGoals_list tacs (tus ++ ts) tvs (length ts + nus) nvs (CExs ctx ts) s' g with
              | (Fail, tacs) => (Fail, tacs)
              | (Solved s'', tacs) =>
                let '(shere,cs') := fromExs s'' in
                (** Here I can drop anything that is already instantiated. **)
                (More_ cs' (GExs ts shere GSolved), tacs)
              | (More_ s'' g', tacs) =>
                let '(shere,cs') := fromExs s'' in
                (** Here I need to drop already instantiated vars and
                 ** substitute through. Ideally, I should collapse as much
                 ** as possible.
                 **)
                (More_ cs' (GExs ts shere g'), tacs)
            end
      | GHyp h g =>
        match @runOnGoals_list tacs tus tvs nus nvs (CHyp ctx h) (HypSubst s) g with
          | (Fail, tacs) => (Fail, tacs)
          | (Solved s, tacs) => (Solved (fromHyp s), tacs)
          | (More_ s g, tacs) => (More_ (fromHyp s) (GHyp h g), tacs)
        end
      | GConj_ l r =>
        (** NOTE: It would be nice if I could eagerly
         ** instantiate [r] with any results that came
         ** from [l].
         **)
        match @runOnGoals_list tacs tus tvs nus nvs ctx s l with
          | (Fail, tacs) => (Fail, tacs)
          | (Solved s', tacs) => @runOnGoals_list tacs tus tvs nus nvs ctx s' r
          | (More_ s' g', tacs) =>
            match @runOnGoals_list tacs tus tvs nus nvs ctx s' r with
              | (Fail, tacs) => (Fail, tacs)
              | (Solved s'', tacs) => (More s'' g', tacs)
              | (More_ s'' g'', tacs) => (More s'' (GConj_ g' g''), tacs)
            end
        end
    end.

  Variables tus tvs : tenv typ.
  Hypothesis Htac : rtac_sound tus tvs tac.

(*
  Lemma WellFormed_remembers
  : forall b a s s',
      remembers a b s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s'.
  Proof.
    induction b; simpl; intros.
    { inv_all; subst; auto. }
    { forward. subst.
      destruct o; forward.
      { eapply IHb. eauto.
        eapply set_sound in H1; eauto.
        destruct H1; assumption. }
      { eauto. } }
  Qed.
*)

  Local Hint Constructors WellFormed_ctx_subst.
  Lemma WellFormed_ctx_subst_fromAll
  : forall t c cs,
      @WellFormed_ctx_subst typ expr _ _ (CAll c t) cs ->
      @WellFormed_ctx_subst typ expr _ _ c (fromAll cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CAll _ _ => fun x => WellFormed_ctx_subst (fromAll x)
                          | _ => fun _ => True
                        end S
           with
             | WF_AllSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.
  Lemma WellFormed_ctx_subst_fromHyp
  : forall t c cs,
      @WellFormed_ctx_subst typ expr _ _ (CHyp c t) cs ->
      @WellFormed_ctx_subst typ expr _ _ c (fromHyp cs).
  Proof.
    intros.
    refine match H in @WellFormed_ctx_subst _ _ _ _ C S
                 return match C as C return ctx_subst C -> Prop with
                          | CHyp _ _ => fun x => WellFormed_ctx_subst (fromHyp x)
                          | _ => fun _ => True
                        end S
           with
             | WF_HypSubst _ _ _ pf => pf
             | _ => I
           end.
  Qed.
  Local Hint Resolve WellFormed_ctx_subst_fromAll WellFormed_ctx_subst_fromHyp.

  Instance Injective_ExsSubst ts ctx a b c d
  : Injective (ExsSubst (typ:=typ)(expr:=expr)(ts:=ts)(c:=ctx) a b = ExsSubst c d) :=
    { result := a = c /\ b = d }.
  intro pf.
  refine (match pf in _ = X return
                match X with
                  | ExsSubst _ _ c d => fun a b => a = c /\ b = d
                  | _ => True
                end a b
          with
            | eq_refl => conj eq_refl eq_refl
          end).
  Defined.

(*
  Lemma runOnGoals_list_sound_ind
  : forall tacs g ctx s,
      Forall (rtac_sound tus tvs) tacs ->
      @rtac_spec typ expr subst _ _ _ _ _
                 tus tvs ctx s g
                 (@runOnGoals_list tacs
                                   (tus ++ getUVars ctx)
                                   (tvs ++ getVars ctx)
                                   (length tus + countUVars ctx)
                                   (length tvs + countVars ctx)
                                   ctx s g).
*)

  Global Instance Injective_WellFormed_Goal_GAll tus tvs t g
  : Injective (WellFormed_Goal tus tvs (GAll t g)) :=
    { result := WellFormed_Goal tus (tvs ++ t :: nil) g }.
  Proof. inversion 1; auto. Defined.
  Global Instance Injective_WellFormed_Goal_GHyp tus tvs t g
  : Injective (WellFormed_Goal tus tvs (GHyp t g)) :=
    { result := WellFormed_Goal tus tvs g }.
  Proof. inversion 1; auto. Defined.


  Lemma runOnGoals_sound_ind
  : forall g ctx s,
      @rtac_spec typ expr _ _ _
                 tus tvs ctx s g
                 (@runOnGoals (tus ++ getUVars ctx)
                              (tvs ++ getVars ctx)
                              (length tus + countUVars ctx)
                              (length tvs + countVars ctx)
                              ctx s g).
  Proof.
    red. induction g; fold runOnGoals in *.
    { (* All *)
      intros.
      specialize (@IHg (CAll ctx t) (AllSubst s)).
      simpl in *.
      match goal with
        | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X
      end; [ | f_equal ; try solve [ rewrite app_ass_trans ; reflexivity | omega ] ].
      destruct (runOnGoals (tus ++ getUVars ctx) (tvs ++ getVars ctx ++ t :: nil)
                           (length tus + countUVars ctx) (length tvs + S (countVars ctx))
                           (AllSubst s) g);
        auto; intros; forward_reason; inv_all.
      { destruct IHg as [ ? [ ? ? ] ].
        { rewrite app_assoc. assumption. }
        { constructor. auto. }
        split.
        { apply WellFormed_ctx_subst_fromAll; auto. }
        split.
        { constructor. rewrite <- app_assoc; eauto. }
        { generalize (Proper_pctxD_impl tus tvs (fromAll c)).
          simpl in *.
          rewrite goalD_conv with (pfu := eq_refl)
                                    (pfv := eq_sym (app_ass_trans tvs (getVars ctx) (t :: nil))).
          autorewrite with eq_rw.
          forward; inv_all; subst.
          forward_reason.
          inv_all; subst; simpl in *.
          forward; inv_all; subst.
          split; eauto.
          intros us vs.
          eapply H6; [ | reflexivity | reflexivity | eapply H9 ].
          do 6 red. clear.
          do 6 intro; equivs.
          destruct (app_ass_trans tvs (getVars ctx) (t :: nil)); simpl.
          eauto. } }
      { admit. (* generalize (Proper_pctxD_impl tus tvs (fromAll c)).
        simpl in *.
        rewrite goalD_conv with (pfu := eq_refl)
                                  (pfv := eq_sym (app_ass_trans tvs (getVars ctx) (t :: nil))).
        autorewrite with eq_rw.
        forward; inv_all; subst.
        forward_reason.
        inv_all; subst; simpl in *.
        forward; inv_all; subst.
        split; eauto. intros.
        generalize (H6 us vs).
        eapply Fmap_pctxD_impl; eauto; try reflexivity.
        clear.
        do 6 red. intros; equivs.
        destruct (app_ass_trans tvs (getVars ctx) (t :: nil)).
        simpl in *; eauto. } *) } }
    { (* Exs *)
      intros; simpl in *.
      forward.
      specialize (@IHg (CExs _ l) (ExsSubst s r)).
      revert IHg.
      repeat rewrite countUVars_getUVars.
      repeat rewrite countVars_getVars.
      do 2 rewrite <- app_length.
      intros; forward.
      match goal with
        | H : match ?X with _ => _ end |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X;
            [ remember X as X' ; destruct X'
            |  ]
      end; intros; auto.
      { destruct (eta_ctx_subst_exs c) as [ ? [ ? ? ] ]; subst.
        simpl. intros.
        destruct IHg as [ ? [ ? ? ] ].
        { inversion H; subst; auto. simpl in *.
          rewrite app_assoc. assumption. }
        { inversion H; subst. constructor; auto.
          
        generalize (WellFormed_remembers _ _ _ H (@WellFormed_empty _ _ _ _ _ _ _ _ _)); intros.
        forward_reason.
        inv_all; split; auto.
        simpl in *. forward; inv_all; subst.
        destruct (substD_empty ((tus ++ getUVars ctx) ++ map fst l) (tvs ++ getVars ctx)) as [ ? [ ? ? ] ].
        destruct (@remembers_spec _ _ _ _ _ _ _ (@WellFormed_empty _ _ _ _ _ _ _ _ _) H H10 H9) as [ ? [ ? ? ] ].
        rewrite H12 in H8.
        forward; inv_all; subst.
        rewrite map_fst_combine in * by eauto using forgets_length.
        rewrite map_snd_combine in * by eauto using forgets_length.
        Cases.rewrite_all_goal.
        eapply forgets_spec in H8; eauto.
        destruct H8 as [ ? [ ? ? ] ].
        Cases.rewrite_all_goal.
        forward_reason.
        inv_all. subst.
        split; auto.
        { intros us vs.
          specialize (H18 us vs); revert H18.
          rewrite H12 in H15. rewrite H16 in *.
          rewrite H1 in *.
          forwardy.
          eapply forgets_spec in H15; eauto.
          specialize (H18 us vs).
          eapply Ap_pctxD; eauto.
          revert H18.
          eapply Ap_pctxD; eauto.
          eapply Pure_pctxD; eauto.
          intros.
          forward_reason.
          rewrite H8 in H15. inv_all. subst.
          clear - H11 H13 H17 H18 H19 H20 H22.
          rewrite _forall_sem in H19.
          rewrite _exists_sem in H20.
          destruct H20.
          apply _exists_sem. exists x0.
          specialize (H11 (hlist_app us0 x0) vs0).
          specialize (H13 (hlist_app us0 x0) vs0).
          destruct H.
          split.
          { destruct H13. destruct H2; eauto.
            eapply H18. eapply H22. assumption. }
          { eapply H19; auto. apply H17. auto. } } }
      { (** Same Proof as above **)
        destruct (eta_ctx_subst_exs c) as [ ? [ ? ? ] ]; subst.
        simpl. intros.
        generalize (WellFormed_remembers _ _ _ H (@WellFormed_empty _ _ _ _ _ _ _ _ _)); intros.
        forward_reason.
        inv_all; split; auto.
        simpl in *. forward; inv_all; subst.
        destruct (substD_empty ((tus ++ getUVars ctx) ++ map fst l) (tvs ++ getVars ctx)) as [ ? [ ? ? ] ].
        destruct (@remembers_spec _ _ _ _ _ _ _ (@WellFormed_empty _ _ _ _ _ _ _ _ _) H H10 H9) as [ ? [ ? ? ] ].
        rewrite H12 in H8.
        forward; inv_all; subst.
        rewrite map_fst_combine in * by eauto using forgets_length.
        rewrite map_snd_combine in * by eauto using forgets_length.
        Cases.rewrite_all_goal.
        eapply forgets_spec in H8; eauto.
        destruct H8 as [ ? [ ? ? ] ].
        Cases.rewrite_all_goal.
        forward_reason.
        inv_all. subst.
        split; auto.
        { intros us vs.
          specialize (H17 us vs); revert H17.
          repeat match goal with
                   | H : _ = _ , H' : _ |- _ =>
                     rewrite H in H'
                 end.
          forwardy.
          eapply forgets_spec in H14; eauto.
          specialize (H17 us vs).
          eapply Ap_pctxD; eauto.
          revert H17.
          eapply Ap_pctxD; eauto.
          eapply Pure_pctxD; eauto.
          intros.
          forward_reason.
          rewrite H8 in H14. inv_all. subst.
          clear - H21 H17 H18 H16 H19 H13.
          rewrite _forall_sem in H18.
          rewrite _exists_sem in H19.
          destruct H19.
          apply _exists_sem. exists x0.
          specialize (H16 (hlist_app us0 x0) vs0).
          specialize (H21 (hlist_app us0 x0) vs0).
          specialize (H13 (hlist_app us0 x0) vs0).
          destruct H.
          split.
          { destruct H13. destruct H2; eauto.
            eapply H17. eapply H21. assumption. }
          { eapply H18; auto. apply H16. auto. } } }  *)}
    { (* Hyp *)
      simpl; intros.
      specialize (IHg (CHyp ctx e) (HypSubst s)).
      match goal with
        | H : match ?X with _ => _ end
          |- match match ?Y with _ => _ end with _ => _ end =>
          replace Y with X; [ remember X as X' ; destruct X' | f_equal ; simpl ; rewrite map_length; omega ]
      end; auto;
      intros; forward_reason; split; eauto; simpl in *;
      forward; forward_reason; subst; inv_all; subst; simpl in *;
      forward; subst; inv_all; subst.
      { split; auto.
        intros us vs.
        generalize (H7 us vs).
        eapply Fmap_pctxD_impl; try reflexivity; eauto.
        clear; do 6 red; intros.
        equivs; tauto. }
      { split; auto. } }
    { (* Conj *)
      simpl; intros; clear Htac.
      specialize (IHg1 ctx s).
      rename g1 into A.
      rename g2 into B.
      match goal with
        | H : match ?X with _ => _ end
          |- context [ match ?Y with _ => _ end ] =>
          change Y with X ; destruct X; auto
      end.
      { rename g into A'.
        specialize (IHg2 ctx c).
        match goal with
          | H : match ?X with _ => _ end
            |- context [ match ?Y with _ => _ end ] =>
            change Y with X ; destruct X; auto
        end.
        { rename g into B'.
          intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H11 us vs).
          specialize (H12 us vs).
          revert H11.
          eapply (Applicative_pctxD _ H8).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H12.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. }
        { change (rtac_spec tus tvs s (GConj_ A B) (More c0 A')).
          eapply Proper_rtac_spec; [ reflexivity | eapply More_More_ | ].
          reflexivity.
          simpl.
          intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H11 us vs).
          specialize (H10 us vs).
          revert H10.
          eapply (Applicative_pctxD _ H8).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H11.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. } }
      { specialize (IHg2 ctx c).
        match goal with
          | H : match ?X with _ => _ end
            |- context [ match ?Y with _ => _ end ] =>
            change Y with X ; destruct X; auto
        end.
        { rename g into B'.
          intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H10 us vs).
          specialize (H11 us vs).
          revert H10.
          eapply (Applicative_pctxD _ H7).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H11.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. }
        { intros; forward_reason; split; auto.
          simpl. forward. forward_reason.
          split; [ etransitivity; eassumption | ].
          intros us vs.
          specialize (H9 us vs).
          specialize (H10 us vs).
          revert H9.
          eapply (Applicative_pctxD _ H7).
          eapply pctxD_SubstMorphism.
          3: eassumption. eassumption. eassumption.
          revert H10.
          eapply (Fmap_pctxD_impl _ H3); try reflexivity.
          clear. do 6 red.
          intros. equivs. firstorder. } } }
    { (* Goal *)
      clear - Htac; simpl; intros.
      red in Htac.
      specialize (@Htac ctx s e _ eq_refl).
      rewrite countUVars_getUVars.
      rewrite countVars_getVars.
      do 2 rewrite <- app_length.
      eauto. }
    { (* Solved *)
      clear. simpl.
      intros. split; auto.
      forward. split; [ reflexivity | ].
      intros.
      eapply (@Applicative_pctxD _ _ _ _ _ _ _ _ tus tvs ctx s); eauto. }
  Qed.

End runOnGoals.

Arguments runOnGoals {typ expr subst _ _} tac tus tvs nus nvs ctx csub goal : rename.

Section runOnGoals_proof.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Theorem runOnGoals_sound
  : forall tus tvs tac,
      rtac_sound tus tvs tac -> rtacK_sound tus tvs (runOnGoals tac).
  Proof.
    intros.
    generalize (@runOnGoals_sound_ind typ expr subst _ _ _ _ _ _ tac tus tvs H).
    red. intros; subst.
    specialize (H0 g ctx s). revert H0; clear.
    unfold rtac_spec, rtacK_spec.
    rewrite countUVars_getUVars.
    rewrite countVars_getVars.
    do 2 rewrite <- app_length.
    exact (fun x => x).
  Qed.
End runOnGoals_proof.