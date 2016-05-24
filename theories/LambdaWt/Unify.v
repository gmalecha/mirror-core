Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.LambdaWt.DepUtil.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.WtMigrator.
Require Import MirrorCore.LambdaWt.SubstWt.

Set Implicit Arguments.
Set Strict Implicit.

Section unify.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.
  Let type := type Tsymbol.
  Variable Esymbol : type -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.
  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  Let wtexpr := wtexpr Esymbol.
  Let Tuvar := Tuvar Tsymbol.

  Variable Inst : list Tuvar -> Type.
  Context {Inst_Inst : Instantiation TsymbolD Esymbol Inst}.

(*
  Inductive Unifiable {tus} (s : Inst tus) (tvs : list type) (t : type)
    : wtexpr tus tvs t -> wtexpr tus tvs t -> Prop :=
  | Unif_UVar : forall ts (u : member (ts,t) tus) xs e,
      Inst_lookup s u = Some e ->
      @Unifiable tus s tvs t (wtUVar u xs) (subst xs e).
*)

  Definition Unifiable_eq {tus} s tvs t a b : Prop :=
    @Unifiable _ _ _ _ _ tus s tvs t a b \/ @Unifiable _ _ _ _ _ tus s tvs t b a.

  Global Instance Symmetric_Unifiable_eq tus tvs t (i : Inst tus)
  : Symmetric (Unifiable_eq i (tvs:=tvs) (t:=t)).
  Proof.
    red. destruct 1; (left + right); solve [ eauto ].
  Qed.

  (** This is probably not an ideal definition **)
(*
  Definition Inst_evolves {tus} (i1 i2 : Inst tus) : Prop :=
    forall tvs t (e1 e2 : wtexpr tus tvs t),
      wtexpr_equiv (Unifiable_eq i1) e1 e2 ->
      wtexpr_equiv (Unifiable_eq i2) e1 e2.
*)

  Theorem Inst_lookup_ok : forall tus tvs ts t (u : member (ts,t) tus) s e,
      Inst_lookup s u = Some e ->
      forall xs, Unifiable s (wtUVar u xs) (subst (tvs:=tvs) xs e).
  Proof. constructor; eauto. Qed.

  Definition check_set {tus tvs} {ts t}
             (unify : wtexpr tus tvs t -> Inst tus -> option (Inst tus))
             (u : member (ts, t) tus) (xs : hlist (wtexpr tus tvs) ts)
             (e : wtexpr tus tvs t) (s : Inst tus)
    : option (Inst tus) :=
    match Inst_lookup s u with
    | None => match pattern_expr Tsymbol_eq_dec Esymbol_eq_dec e xs with
              | None => None
              | Some e' => Some (Inst_set u e' s)
              end
    | Some e' => unify (subst xs e') s
    end.

  Definition unify_spec {tus} (i i' : Inst tus) {tvs t}
             (e1 e2 : wtexpr tus tvs t)
  : Prop :=
    Inst_evolves migrator_id i i' /\ wtexpr_equiv (Unifiable_eq i') e1 e2.


  Lemma subst_lift'
  : forall (tus : list Tuvar) t tux
           (e : wtexpr tus tux t)
           tvsX tvs tvs' tvs''
           (xs : hlist (wtexpr tus tvsX) tvs)
           (xs' : hlist (wtexpr tus tvsX) tvs')
           (xs'' : hlist (wtexpr tus tvsX) tvs'')
           (pf : tux = (List.app tvs'' tvs)),
      subst (hlist_app xs'' (hlist_app xs' xs))
            (wtexpr_lift tvs' tvs'' match pf in _ = X return wtexpr _ X _ with
                                    | eq_refl => e
                                    end) =
      subst (hlist_app xs'' xs) match pf with
                                | eq_refl => e
                                end.
  Proof.
    clear.
    induction e.
    { intros. subst. simpl.
      eapply hlist_get_member_lift. }
    { intros; subst; reflexivity. }
    { intros; subst; simpl in *.
      specialize (IHe1 _ _ _ _ xs xs' xs'' eq_refl).
      specialize (IHe2 _ _ _ _ xs xs' xs'' eq_refl).
      simpl in *.
      rewrite IHe1. rewrite IHe2. reflexivity. }
    { intros; subst. simpl.
      f_equal.
      pose (s := fun (t : type) (e0 : wtexpr tus tvsX t) =>
                   wtexpr_lift (d :: nil) nil e0).
      specialize (IHe _ _ _ (d :: tvs'')
                      (hlist_map s xs) (hlist_map s xs')
                      (Hcons (wtVar (MZ d tvsX))
                             (hlist_map s xs'')) eq_refl).
      simpl in *.
      repeat rewrite hlist_app_hlist_map.
      eapply IHe. }
    { intros; subst; simpl.
      f_equal. clear - H.
      induction H.
      { constructor. }
      { simpl. f_equal; eauto.
        specialize (H tvsX tvs0 tvs' tvs'' xs0 xs' xs'' eq_refl).
        simpl in *. eauto. } }
  Qed.

  Lemma subst_lift
  : forall (tus : list Tuvar) t tvsX tvs tvs' tvs''
           (e : wtexpr tus (List.app tvs'' tvs) t)
           (xs : hlist (wtexpr tus tvsX) tvs)
           (xs' : hlist (wtexpr tus tvsX) tvs')
           (xs'' : hlist (wtexpr tus tvsX) tvs''),
      subst (hlist_app xs'' (hlist_app xs' xs))
            (wtexpr_lift tvs' tvs'' e) =
      subst (hlist_app xs'' xs) e.
  Proof.
    intros.
    eapply subst_lift' with (pf:=eq_refl).
  Qed.

  Lemma find_in_hlist_ok : forall tus R tvs ts t e xs e',
      @find_in_hlist Tsymbol Tsymbol_eq_dec _ Esymbol_eq_dec
                     tus tvs ts t xs e = Some e' ->
      wtexpr_equiv R e (subst xs e').
  Proof.
    induction xs; simpl; intros; try congruence.
    destruct (type_eq_dec Tsymbol_eq_dec l t); try congruence.
    subst.
    destruct (wtexpr_eq_dec Tsymbol_eq_dec Esymbol_eq_dec e f).
    - inv_all; subst.
      simpl. reflexivity.
    - destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs e);
        try congruence.
      inv_all. subst.
      specialize (IHxs _ eq_refl).
      generalize (@subst_lift _ _ _ _ _ nil w xs (Hcons f Hnil) Hnil).
      simpl.
      intro X; change_rewrite X. eassumption.
    - destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs e); try congruence.
      inv_all. subst.
      specialize (IHxs _ eq_refl).
      generalize (@subst_lift _ _ _ _ _ nil w xs (Hcons f Hnil) Hnil).
      simpl.
      intro X; change_rewrite X. eassumption.
  Qed.

  Lemma pattern_expr_ok : forall tus R tvs t e ts xs e',
      @pattern_expr _ Tsymbol_eq_dec _ Esymbol_eq_dec
                    tus tvs t e ts xs = Some e' ->
      wtexpr_equiv R e (subst xs e').
  Proof.
    induction e; simpl in *.
    { intros.
      generalize (find_in_hlist_ok R (wtVar m) xs).
      destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs (wtVar m)); try congruence.
      intros. eapply H0 in H; clear H0.
      auto. }
    { intros.
      generalize (find_in_hlist_ok R (wtInj m) xs).
      destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs (wtInj m));
        try congruence.
      { intro. apply H0 in H; clear H0. auto. }
      { inv_all. subst. intros. reflexivity. } }
    { intros.
      generalize (find_in_hlist_ok R (wtApp e1 e2) xs).
      destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs (wtApp e1 e2));
        try congruence; eauto.
      specialize (IHe1 _ xs).
      specialize (IHe2 _ xs).
      destruct (pattern_expr Tsymbol_eq_dec Esymbol_eq_dec e1 xs); try congruence.
      specialize (IHe1 _ eq_refl).
      destruct (pattern_expr Tsymbol_eq_dec Esymbol_eq_dec e2 xs); try congruence.
      specialize (IHe2 _ eq_refl).
      inv_all. subst.
      simpl. intro.
      eapply eqApp; eauto. }
    { intros.
      generalize (find_in_hlist_ok R (wtAbs e) xs).
      destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs (wtAbs e)); eauto.
      intro X; clear X.
      match goal with
      | _ : match pattern_expr _ _ ?e ?X with _ => _ end = _ |- _ =>
        specialize (IHe _ X) ;
          destruct (pattern_expr Tsymbol_eq_dec Esymbol_eq_dec e X) ;
          try congruence
      end.
      inv_all. subst. simpl.
      specialize (IHe _ eq_refl).
      eapply eqAbs. eauto. }
    { intros.
      generalize (find_in_hlist_ok R (wtUVar u xs) xs0).
      destruct (find_in_hlist Tsymbol_eq_dec Esymbol_eq_dec xs0 (wtUVar u xs)); try congruence.
      intros. apply H1 in H0; clear H1. eauto. }
  Qed.

  Lemma wtexpr_equiv_Unifiable_eq_Inst_evolves:
    forall (tus : list (WtExpr.Tuvar Tsymbol)) (tvs : list type) (t : type)
           (s s' : Inst tus),
      Inst_evolves migrator_id s s' ->
      forall (x y : WtExpr.wtexpr Esymbol tus tvs t),
        wtexpr_equiv (Unifiable_eq s) x y ->
        wtexpr_equiv (Unifiable_eq s') x y.
  Proof.
    induction 2; try solve [ constructor; eauto ].
    { eapply eqUVar.
      clear - H0 pfs.
      induction H0; try constructor; eauto. }
    { constructor.
      destruct pf; [ left; specialize (H _ _ a b)
                   | right; specialize (H _ _ b a) ]; subst.
      repeat rewrite migrate_expr_migrator_id in H.
      eapply H. eapply H0.
      repeat rewrite migrate_expr_migrator_id in H.
      eapply H. eapply H0. }
    { eapply eqTrans; eassumption. }
  Qed.

  Lemma check_set_ok : forall tus tvs ts t unify u xs e s s',
      @check_set tus tvs ts t unify u xs e s = Some s' ->
      (forall e' s s',
          unify e' s = Some s' ->
          unify_spec s s' e' e) ->
      unify_spec s s' (wtUVar u xs) e.
  Proof.
    unfold check_set; intros.
    consider (Inst_lookup s u).
    { intros. eapply H0 in H1.
      red. destruct H1; split; auto.
      assert (wtexpr_equiv (Unifiable_eq s) (wtUVar u xs) (subst xs w)).
      { econstructor. econstructor. econstructor. eassumption. }
      eapply eqTrans with (b:=subst xs w).
      { eapply wtexpr_equiv_Unifiable_eq_Inst_evolves; eassumption. }
      { assumption. } }
    { intro Hnot_there.
      consider (pattern_expr Tsymbol_eq_dec Esymbol_eq_dec e xs);
        intros; try congruence.
      inv_all. subst.
      eapply pattern_expr_ok with (R := Unifiable_eq (Inst_set u w s)) in H.
      destruct (@Inst_set_ok _ _ _ _ _ tus tvs _ _ u w s _ eq_refl Hnot_there).
      split; auto.
      eapply eqTrans.
      2: symmetry; try eassumption.
      constructor. constructor. eapply H2. }
  Qed.

  Section unify_list.
    Context {tus : list Tuvar} {tvs : list type}.
    Variable unify : forall {t}, wtexpr tus tvs t -> wtexpr tus tvs t ->
                                 Inst tus -> option (Inst tus).

    Fixpoint unify_list {ts} (e1 e2 : hlist (wtexpr tus tvs) ts)
             (s : Inst tus) {struct e1}
    : option (Inst tus) :=
      match e1 in hlist _ ts
            return hlist (wtexpr tus tvs) ts -> option (Inst tus)
      with
      | Hnil => fun _ => Some s
      | Hcons e1 es1 => fun e2 =>
                          match unify e1 (hlist_hd e2) s with
                          | Some s' => unify_list es1 (hlist_tl e2) s'
                          | None => None
                          end
      end e2.
  End unify_list.

  Definition Unifier : Type :=
    forall {tus tvs t} (e1 e2 : wtexpr tus tvs t)
           (s : Inst tus), option (Inst tus).

  Definition UnifierOk (u : Unifier) : Prop :=
    forall tus tvs t e e' i i',
      @u tus tvs t e e' i = Some i' ->
      unify_spec i i' e e'.


  Variable unifyRec : Unifier.

  Fixpoint unify {tus tvs t} (e1 e2 : wtexpr tus tvs t) (s : Inst tus)
           {struct e1}
    : option (Inst tus).
  refine
    (match e1 in WtExpr.wtexpr _ _ _ t
           return wtexpr tus tvs t -> option (Inst tus)
     with
     | wtVar x => fun e2 =>
       match e2 in WtExpr.wtexpr _ _ _ t
             return member t tvs -> option _
       with
       | wtVar y => fun x =>
                      match member_eq_dec (T_dec:=type_eq_dec Tsymbol_eq_dec) x y with
                      | left _ => Some s
                      | right _ => None
                      end
       | wtUVar u xs => fun x =>
                          check_set (unifyRec (wtVar x))
                                    u xs (wtVar x) s
       | _ => fun _ => None
       end x
     | wtInj f => fun e2 =>
       match e2 in WtExpr.wtexpr _ _ _ t
             return Esymbol t -> option (Inst tus)
       with
       | wtInj f' => fun f => if Esymbol_eq_dec f f' then Some s else None
       | wtUVar u xs => fun f => check_set (unifyRec (wtInj f))
                                           u xs (wtInj f) s
       | _ => fun _ => None
       end f
     | @wtApp _ _ _ _ d c f x => fun e2 =>
       match e2 in WtExpr.wtexpr _ _ _ t
             return (forall tu, member (tu,t) tus ->
                                hlist (wtexpr tus tvs) tu ->
                                Inst tus -> option (Inst tus)) ->
                    (wtexpr tus tvs (TArr d t) -> Inst tus -> option (Inst tus)) ->
                    option (Inst tus)
       with
       | @wtApp _ _ _ _ d' c' f' x' =>
         match type_eq_dec Tsymbol_eq_dec d' d with
         | left pf => fun _ rec =>
           match rec match pf with
                     | eq_refl => f'
                     end s with
           | Some s' => unify _ _ _ x match pf with
                                      | eq_refl => x'
                                      end s'
           | None => None
           end
         | _ => fun _ _ => None
         end
       | wtUVar u xs => fun cs _ => cs _ u xs s
       | _ => fun _ _ => None
       end (fun z (u : member (z,c) tus) xs s =>
              check_set (unifyRec (wtApp f x)) u xs (wtApp f x) s)
           (fun x => unify _ _ _ f x)
     | @wtAbs _ _ _ _ d r e => fun e2 =>
       match e2 in WtExpr.wtexpr _ _ _ t'
             return (forall tu, member (tu,t') tus ->
                                hlist (wtexpr tus tvs) tu ->
                                Inst tus -> option (Inst tus)) ->
                    (wtexpr tus (match t' with
                                 | TArr a _ => a
                                 | _ => t'
                                 end :: tvs) match t' with
                                             | TArr _ b => b
                                             | _ => t'
                                             end -> Inst tus -> option (Inst tus)) ->
                    option (Inst tus)
       with
       | @wtAbs _ _ _ _ d' r' e' =>
         match type_eq_dec Tsymbol_eq_dec d' d with
         | left pf => fun _ rec => rec match pf with
                                       | eq_refl => e'
                                       end s
         | right _ => fun _ _ => None
         end
       | wtUVar u xs => fun cs _ => cs _ u xs s
       | _ => fun _ _ => None
       end (fun (z : list type) (u : member (z,TArr d r) tus) xs s =>
              check_set (unifyRec (wtAbs e)) u xs (wtAbs e) s)
           (fun x => @unify _ _ _ e x)
     | @wtUVar _ _ _ _ ts t u xs => fun b =>
       match b in WtExpr.wtexpr _ _ _ t
             return member (ts,t) tus ->
                    hlist (wtexpr tus tvs) ts ->
                    option (Inst tus)
       with
       | wtUVar u' xs' => fun u xs =>
         match member_check_eq u' u with
         | Some pf => unify_list (@unify _ _) xs match pf with
                                                 | eq_refl => xs'
                                                 end s
         | None =>
           (** TODO: In reality, we should heuristic the order of this
            ** unification.
            **)
           check_set (fun e' s =>
                        check_set (unifyRec e')
                                  u' xs' e' s)
                     u xs (wtUVar u' xs') s
         end
       | x => fun u xs => check_set (unifyRec x) u xs x s
       end u xs
     end e2).
  Defined.

  Section unify_ok.
    Variable tus : list Tuvar.

    Lemma Happ : forall tvs d c f g x y i i' i'',
        @unify_spec tus i i' tvs (TArr d c) f g ->
        unify_spec i' i'' x y ->
        unify_spec i i'' (wtApp f x) (wtApp g y).
    Proof.
      destruct 1; destruct 1.
      split.
      { etransitivity; eauto. }
      { constructor; eauto using wtexpr_equiv_Unifiable_eq_Inst_evolves. }
    Qed.

    Lemma member_check_eq_ok
    : forall tus ts ts' t m m' pf,
        @member_check_eq Tsymbol tus ts ts' t m m' = Some pf ->
        m = match eq_sym pf in _ = X return member (X,_) _ with
            | eq_refl => m'
            end.
    Proof using Tsymbol_eq_dec.
      clear - Tsymbol_eq_dec.
      induction m; simpl; intros.
      { destruct (member_case m').
        { destruct H0. subst.
          simpl.
          rewrite (UIP_refl x) in *; simpl in *.
          reflexivity. }
        { destruct H0; subst. inversion H. } }
      { destruct (member_case m'); destruct H0; subst.
        { inversion H. }
        { simpl in *.
          eapply IHm in H.
          simpl in *. subst. reflexivity. } }
      Unshelve.
      eapply pair_eq_dec.
      eapply list_eq_dec.
      eapply type_eq_dec; eapply Tsymbol_eq_dec.
      eapply type_eq_dec; eapply Tsymbol_eq_dec.
    Qed.

    Hypothesis unifyRec_ok : forall tvs t e e' i i',
        @unifyRec tus tvs t e e' i = Some i' ->
        unify_spec i i' e e'.

    Lemma wtexpr_TArr_case'
      : forall tus tvs d c t (e : wtexpr tus tvs t) (pf : t = TArr d c),
        (exists i, match pf with
                   | eq_refl => e
                   end = wtInj i)
        \/ (exists v, match pf with
                      | eq_refl => e
                      end = wtVar v)
        \/ (exists z f (x : wtexpr tus tvs z),
               match pf with
               | eq_refl => e
               end = wtApp f x)
        \/ (exists e', match pf with
                       | eq_refl => e
                       end = match eq_sym pf with
                             | eq_refl => wtAbs e'
                             end)
        \/ (exists ts (u : member (ts,_) tus) xs,
               match pf with
               | eq_refl => e
               end = wtUVar u xs).
    Proof using Tsymbol_eq_dec.
      clear - Tsymbol_eq_dec.
      destruct e; simpl; intros; subst; eauto.
      { right. right. left. do 3 eexists; eauto. }
      { right. right. right. left.
        generalize pf.
        inversion pf. subst. intros.
        rewrite (UIP_refl pf0). simpl. eauto. }
      { repeat right. do 3 eexists; eauto. }
      Unshelve.
      eapply type_eq_dec. eapply Tsymbol_eq_dec.
    Qed.


    Lemma unify_ok
    : forall tvs t e e' i i',
        @unify tus tvs t e e' i = Some i' ->
        unify_spec i i' e e'.
    Proof.
      induction e.
      { destruct e'; simpl; intros; try congruence.
        { destruct (member_eq_dec m m0); try congruence.
          inversion H. subst. inv_all.
          split. reflexivity.
          eapply eqVar. }
        { eapply check_set_ok in H.
          { red in H. destruct H.
            split; eauto.
            symmetry. tauto. }
          { intros. eapply unifyRec_ok in H0.
            destruct H0.
            split; eauto.
            symmetry. tauto. } } }
      { destruct e'; simpl; intros; try congruence.
        { destruct (Esymbol_eq_dec m e); try congruence; inv_all. subst.
          split. reflexivity. eapply eqInj. }
        { eapply check_set_ok in H.
          { destruct H; split; eauto.
            symmetry; tauto. }
          { intros. eapply unifyRec_ok in H0; eauto.
            destruct H0; split; eauto.
            symmetry; eauto. } } }
      { destruct e'; simpl; intros; try congruence.
        { destruct (type_eq_dec Tsymbol_eq_dec d0 d); try congruence; subst.
          specialize (IHe1 e'1 i).
          destruct (unify e1 e'1 i); try congruence.
          eapply IHe2 in H.
          specialize (IHe1 _ eq_refl).
          eapply Happ; eauto. }
        { eapply check_set_ok in H.
          { destruct H.
            split; eauto.
            symmetry; tauto. }
          { intros. eapply unifyRec_ok in H0; eauto.
            destruct H0; split; eauto.
            symmetry; eauto. } } }
      { simpl.
        intro e'.
        generalize (wtexpr_TArr_case' e' eq_refl); simpl.
        destruct 1 as [ ? | [ ? | [ ? | [ ? | ? ] ] ] ]; forward_reason;
          subst; intros; try congruence.
        { destruct (type_eq_dec Tsymbol_eq_dec d d); try congruence.
          rewrite (UIP_refl e0) in H.
          eapply IHe in H.
          clear - H.
          destruct H; split; eauto.
          econstructor. eauto. }
        { eapply check_set_ok in H.
          destruct H; split; eauto.
          symmetry. eauto.
          intros. eapply unifyRec_ok in H0; eauto.
          destruct H0; split; eauto.
          symmetry; eauto. } }
      { destruct e'; simpl; intros;
        try (eapply check_set_ok in H0;
             [ destruct H0;
               try solve [ split; eauto ]
             | do 3 intro; let Z := fresh in intro Z;
               eapply unifyRec_ok in Z; destruct Z; split;
               solve [ eauto | symmetry; eauto ] ]).
        generalize (member_check_eq_ok m u).
        destruct (member_check_eq m u); subst.
        { clear - H H0.
          intros. specialize (H1 _ eq_refl). subst. simpl in *.
          red.
          cut (Inst_evolves migrator_id i i' /\
               hlist_Forall2 (wtexpr_equiv (Unifiable_eq i') (tvs:=tvs)) xs h).
          { destruct 1; split; eauto using eqUVar. }
          clear u.
          revert H0. generalize dependent i. revert i'.
          induction H.
          { simpl; intros. inversion H0; clear H0; subst.
            split; [ reflexivity | ].
            rewrite (hlist_eta h). constructor. }
          { simpl; intros.
            specialize (H (hlist_hd h) i).
            match goal with
            | H : forall x, ?X = _ -> _ , _ : match ?Y with _ => _ end = _
              |- _ =>
              change X with Y in H; destruct Y
            end; try congruence.
            eapply IHhlist_Forall in H1.
            specialize (H _ eq_refl).
            destruct H. destruct H1.
            split.
            { etransitivity; eauto. }
            { rewrite (hlist_eta h).
              constructor; eauto using wtexpr_equiv_Unifiable_eq_Inst_evolves. } } }
        { eapply check_set_ok in H0.
          { destruct H0; split; eauto. }
          { intros. eapply check_set_ok in H1.
            destruct H1; split; eauto. symmetry; eauto.
            intros. eapply unifyRec_ok in H2. destruct H2; split; eauto.
            symmetry; eauto. } } }
      Unshelve.
      eapply type_eq_dec. eapply Tsymbol_eq_dec.
    Qed.
  End unify_ok.

End unify.

(** The Approxmation of the fixpoint.
 ** We use [positive] for fuel to avoid constructing very large natural numbers.
 **)
Section funify.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.
  Let type := type Tsymbol.
  Variable Esymbol : type -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.
  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  Let wtexpr := wtexpr Esymbol.
  Let Tuvar := Tuvar Tsymbol.

  Variable Inst : list Tuvar -> Type.
  Context {Inst_Inst : @Instantiation Tsymbol TsymbolD Esymbol Inst}.

  Let unifyX :=
    @unify Tsymbol TsymbolD Tsymbol_eq_dec Esymbol Esymbol_eq_dec
           Inst Inst_Inst.

  Require Import Coq.Numbers.BinNums.

  (** NOTE: Terms are eta-expanded to avoid partial application
   **)
  Local Fixpoint funify' (k : _ -> _) (p : positive)
           (tus : list Tuvar)
           (tvs : list type) (t : type)
           (e1 e2 : WtExpr.wtexpr Esymbol tus tvs t)
           (inst : Inst tus) {struct p}
  : option (Inst tus) :=
    match p with
    | xH => k (fun tus tvs t e1 e2 inst => None) tus tvs t e1 e2 inst
    | xO p =>
      @funify' (fun rec tus tvs t e1 e2 inst =>
                  @k (fun tus tvs t e1 e2 inst => k rec tus tvs t e1 e2 inst)
                     tus tvs t e1 e2 inst) p
               tus tvs t e1 e2 inst
    | xI p =>
      @unifyX (fun tus tvs t e1 e2 inst =>
                 @funify' (fun rec tus tvs t e1 e2 inst =>
                            @k (fun tus tvs t e1 e2 inst =>
                                  k rec tus tvs t e1 e2 inst)
                               tus tvs t e1 e2 inst)
                          p
                          tus tvs t e1 e2 inst)
              tus tvs t e1 e2 inst
    end.

  Local Lemma funify'_sound
  : forall p k,
      (forall z,
          (forall tus tvs t e e' i i',
              z tus tvs t e e' i = Some i' ->
              unify_spec i i' e e') ->
          (forall tus tvs t e e' i i',
              k z tus tvs t e e' i = Some i' ->
              unify_spec i i' e e')) ->
      forall tus tvs t e e' i i',
        @funify' k p tus tvs t e e' i = Some i' ->
        unify_spec i i' e e'.
  Proof.
    induction p; simpl; intros.
    { unfold unifyX in *.
      eapply unify_ok in H0; eauto.
      intros. eapply IHp in H1; eauto. }
    { unfold unifyX in *.
      eapply IHp in H0; eauto. }
    { eapply H in H0; eauto.
      inversion 1. }
  Qed.

  Definition funify (p : positive) : Unifier Esymbol Inst :=
    fun (tus : list Tuvar)
        (tvs : list type) (t : type)
        (e1 e2 : WtExpr.wtexpr Esymbol tus tvs t)
        (inst : Inst tus) =>
    @funify' unifyX p tus tvs t e1 e2 inst.

  Theorem funify_sound
  : forall p, UnifierOk (funify p).
  Proof.
    red.
    intros. revert H. eapply funify'_sound.
    unfold unifyX.
    intros.
    revert H0.
    eapply unify_ok; eauto.
  Qed.
End funify.