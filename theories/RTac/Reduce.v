Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.

Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Nat.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Move to Data.Prop **)
Lemma exists_iff : forall (T : Type) (P Q : T -> Prop),
                     (forall x, P x <-> Q x) ->
                     ((exists x, P x) <-> (exists x, Q x)).
Proof.
  clear. intros. setoid_rewrite H. reflexivity.
Qed.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.

  (** TODO: This isn't a very good implementation **)
  Fixpoint instantiateGoal (f : nat -> option expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | GGoal g => GGoal (instantiate f 0 g)
      | GAll t g' => GAll t (instantiateGoal f g')
      | GExs ts sub g' =>
        GExs ts (amap_instantiate f sub) (instantiateGoal f g')
      | GHyp h g' => GHyp (instantiate f 0 h) (instantiateGoal f g')
      | GConj_ a b =>
        GConj_ (instantiateGoal f a) (instantiateGoal f b)
    end.

  Definition GExs_nil_check (ts : list typ) (s : amap _)
             (g : Goal typ expr) : Goal typ expr :=
    match ts with
      | nil => g
      | _ :: _ => GExs ts s g
    end.

  Theorem GExs_nil_check_respects tus tvs ts sub
  : only_in_range (length tus) (length ts) sub ->
    WellFormed_amap sub ->
    (EqGoal (tus ++ ts) tvs ==> EqGoal tus tvs)%signature
         (@GExs typ expr ts sub) (GExs_nil_check ts sub).
  Proof.
    red. intros; subst.
    unfold EqGoal in *. simpl.
    destruct ts.
    { simpl in *.
      rewrite goalD_conv with (pfu := HList.app_nil_r_trans tus)
                              (pfv := eq_refl).
      autorewrite with eq_rw.
      destruct H1.
      split.
      { split.
        { intro. rewrite app_nil_r in H1. apply H1.
          inv_all. rewrite app_nil_r in *. assumption. }
        { rewrite app_nil_r in *.
          intros. apply H1 in H3.
          constructor; auto.
          eapply only_in_range_0_WellFormed_pre_entry; eauto.
          rewrite app_nil_r. assumption. } }
      { inversion H2; try constructor.
        eapply only_in_range_0_substD with (tus := tus++nil) (tvs:=tvs) in H; eauto.
        destruct H as [ ? [ ? ? ] ].
        change_rewrite H.
        constructor.
        do 5 red; intros; equivs.
        autorewrite with eq_rw.
        do 5 red in H5.
        rewrite H5; try reflexivity.
        rewrite <- hlist_app_nil_r.
        revert H6. clear. firstorder. } }
    { simpl in *.
      destruct H1.
      split.
      { split; intros; inv_all; constructor; tauto. }
      inversion H2; try constructor.
      match goal with
        | |- _ _ match ?X with _ => _ end
                 match ?Y with _ => _ end =>
          change Y with X ; destruct X
      end; constructor.
      clear - H5; do 5 red; intros; equivs.
      eapply exists_iff. intros.
      eapply Quant._exists_iff. intros.
      eapply and_iff. reflexivity.
      intros. eapply H5; reflexivity. }
  Qed.

  Definition GExs_do_solved (tes : tenv typ) (m : amap expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved =>
        if amap_is_full (length tes) m then
          GSolved
        else
          GExs tes m g
      | _ => GExs tes m g
    end.

  Definition GHyp_do_solved (e : expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | _ => GHyp e g
    end.

  Definition GAll_do_solved (ts : typ) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | _ => GAll ts g
    end.

  Lemma WellFormed_Goal_All_iff
  : forall tus tvs t (g : Goal typ expr),
      WellFormed_Goal tus tvs (GAll t g) <->
      WellFormed_Goal tus (tvs ++ t :: nil) g.
  Proof.
    split. intros; inv_all; subst. auto.
    intros. constructor. auto.
  Qed.

  (** DUPLICATE **)
  Lemma WellFormed_Goal_Solved_iff
  : forall tus tvs,
      WellFormed_Goal (typ:=typ) (expr:=expr) tus tvs GSolved <->
      True.
  Proof.
    split. intros; inv_all; subst. auto.
    intros. constructor.
  Qed.

  Lemma equiv_hlist_app'
  : forall {T} (F : T -> Type)
           (eqv : forall x : T, Relation_Definitions.relation (F x))
           (a b : list T) (c c' : hlist F a) (d d' : hlist F b),
      equiv_hlist eqv (hlist_app c d) (hlist_app c' d') <->
      (equiv_hlist eqv c c' /\ equiv_hlist eqv d d').
  Proof.
    intros. symmetry. eapply equiv_hlist_app.
  Qed.

  Ltac solve_equiv_hlist :=
    repeat match goal with
             | |- _ => assumption
             | |- _ => reflexivity
             | |- equiv_hlist _ (hlist_app _ _) (hlist_app _ _) =>
               eapply equiv_hlist_app'; split; auto
             | |- _ => constructor
           end.

  Theorem GAll_do_solved_respects tus tvs t
  : (EqGoal tus (tvs ++ t :: nil) ==> EqGoal tus tvs)%signature
      (GAll_do_solved t) (@GAll typ expr t).
  Proof.
    red. red. simpl. unfold GAll_do_solved. simpl.
    intros.  destruct H. split.
    { clear - H.
      destruct x;
        (try rewrite WellFormed_Goal_All_iff);
        (try rewrite H);
        (try rewrite WellFormed_Goal_All_iff);
        try reflexivity.
      rewrite <- H.
      split; constructor. }
    { destruct x; simpl in *;
      try solve [ destruct H0; constructor;
                  do 5 red; intros; eapply forall_iff; intros; eapply H0; eauto;
                  solve_equiv_hlist ].
      inversion H0. subst.
      constructor.
      do 5 red; intros. split; auto.
      intros. eapply H3. eauto.
      eapply equiv_hlist_app'. split; eauto.
      constructor. reflexivity. constructor. auto. }
  Qed.

  Lemma WellFormed_Goal_Hyp_iff
  : forall tus tvs t (g : Goal typ expr),
      WellFormed_Goal tus tvs (GHyp t g) <->
      WellFormed_Goal tus tvs g.
  Proof.
    split. intros; inv_all; subst. auto.
    intros. constructor. auto.
  Qed.

  Theorem GHyp_do_solved_respects tus tvs t tD
  : propD tus tvs t = Some tD ->
    (EqGoal tus tvs ==> EqGoal tus tvs)%signature
      (GHyp_do_solved t) (@GHyp typ expr t).
  Proof.
    red. red. simpl. unfold GHyp_do_solved. simpl.
    intros. destruct H0. split.
    { clear - H0.
      destruct x;
        (try rewrite WellFormed_Goal_Hyp_iff);
        (try rewrite H0);
        (try rewrite WellFormed_Goal_Hyp_iff);
        try reflexivity. }
    { destruct x; simpl in *; rewrite H;
      try solve
          [ destruct H1; constructor;
            do 5 red; intros;
            eapply impl_iff; intros;
            [ equivs; reflexivity |  eapply H1; eauto ] ].
      inversion H1. subst.
      constructor.
      do 5 red; intros. split; auto.
      simpl; intros. eapply H4; eauto. }
  Qed.

  Lemma WellFormed_Goal_iff_GExs_cancel
  : forall (tus tvs ts : tenv typ) m x y,
      (WellFormed_Goal (tus ++ ts) tvs x <->
       WellFormed_Goal (tus ++ ts) tvs y) ->
      (WellFormed_Goal tus tvs (GExs ts m x) <->
       WellFormed_Goal tus tvs (GExs ts m y)).
  Proof.
    clear. intros. split; intros; inv_all; subst; constructor; tauto.
  Qed.


  Lemma GoalImplies_GExs_do_solved
  : forall c (cs : ctx_subst c) ts m g,
      GoalImplies (cs, GExs ts m g)
                  (cs, GExs_do_solved ts m g).
  Proof.
    Transparent GoalImplies. simpl; intros.
    split; auto.
    split.
    { destruct g; simpl; auto.
      destruct (amap_is_full (length ts) m);
        auto. constructor. }
    { forward; inv_all; subst.
      destruct g; simpl in *; forwardy; inv_all; subst;
      Cases.rewrite_all_goal.
      * split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto.
      * split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto.
      * split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto.
      * split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto.
      * split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto.
      * match goal with
          | |- match _ _ _ (if ?X then _ else _) with _ => _ end =>
            consider X; intros; simpl
        end.
      + split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto. intros.
        clear - H H3 H6.
        eapply Quant._exists_sem.
        eapply subst_getInstantiation in H3; eauto.
        destruct H3.
        exists (hlist_map (fun t (x : exprT _ _ (typD t))=> x us0 vs0) x).
        eauto.
      + change_rewrite H3.
        split; [ reflexivity | ].
        intros. eapply Pure_pctxD; eauto. }
  Qed.

  Fixpoint toResult (ctx ctx' : Ctx typ expr)
           (g : Goal typ expr)
  : ctx_subst (Ctx_append ctx ctx') -> Result ctx :=
    match ctx' as ctx'
          return ctx_subst (Ctx_append ctx ctx') -> Result ctx
    with
      | CTop _ _ => fun cs => More_ cs g
      | CAll ctx' t => fun cs =>
        @toResult ctx ctx' (GAll t g) (fromAll cs)
      | CHyp ctx' h => fun cs =>
        @toResult ctx ctx'  (GHyp h g) (fromHyp cs)
      | CExs ctx' ts => fun cs : ctx_subst (CExs (Ctx_append ctx ctx') ts) =>
        let '(s,cs') := fromExs cs in
        @toResult ctx ctx' (GExs ts s g) cs'
    end.

  Fixpoint reduceResult (ctx ctx' : Ctx typ expr)
           (g : Goal typ expr)
  : ctx_subst (Ctx_append ctx ctx') -> Result ctx :=
    match ctx' as ctx'
          return ctx_subst (Ctx_append ctx ctx') -> Result ctx
    with
      | CTop _ _ => fun cs =>
        (** TODO: this should be More_ but to do the right reasoning,
         ** I need to find a better equivalence relation
         **)
        More cs g
      | CAll ctx' t => fun cs =>
        @reduceResult ctx ctx' (GAll_do_solved t g) (fromAll cs)
      | CHyp ctx' h => fun cs =>
        @reduceResult ctx ctx'  (GHyp_do_solved h g) (fromHyp cs)
      | CExs ctx' ts => fun cs : ctx_subst (CExs (Ctx_append ctx ctx') ts) =>
        let '(s,cs') := fromExs cs in
        @reduceResult ctx ctx' (GExs_do_solved ts s g) cs'
    end.

  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx ctx' : Ctx typ expr)
  : ctx_subst (Ctx_append ctx ctx') -> Result ctx :=
    match ctx' as ctx'
          return ctx_subst (Ctx_append ctx ctx') -> Result ctx
    with
      | CTop _ _ => fun cs => Solved cs
      | CAll ctx' t => fun cs =>
        @solveGoal ctx ctx' (fromAll cs)
      | CHyp ctx' h => fun cs =>
        @solveGoal ctx ctx' (fromHyp cs)
      | CExs ctx' ts => fun cs =>
        let '(s,cs') := fromExs cs in
        let g' := GExs_do_solved ts s GSolved in
        match g' with
          | GSolved => @solveGoal ctx ctx' cs'
          | g' => @toResult ctx ctx' g' cs'
        end
    end.

  Lemma solveGoal_toGoal
  : forall ctx ctx' (cs : ctx_subst (Ctx_append ctx ctx')),
      (EqResult)
        (@solveGoal ctx ctx' cs) (toResult ctx ctx' GSolved cs).
  Proof.
  Abort.

  Definition reduceGoal (ctx ctx' : Ctx typ expr)
             (s : ctx_subst (Ctx_append ctx ctx'))
             (g : Goal typ expr)
  : Result ctx :=
    match g with
      | GSolved => @solveGoal ctx ctx' s
      | _ => @reduceResult ctx ctx' g s
    end.

  Definition ResultImplies ctx (r1 r2 : Result ctx) : Prop :=
    match fromResult r1 , fromResult r2 with
      | _ , None => True
      | Some a , Some b => GoalImplies a b
      | None , _ => False
    end.

End parameterized.

(* TODO: Making this work requires a better set of equivalence relations
  Lemma reduceResult_toResult
  : forall ctx ctx',
      (GoalImplies (ctx:=Ctx_append ctx ctx') ==> @ResultImplies _)%signature
        (fun sg => let (cs,g) := sg in toResult ctx ctx' g cs)
        (fun sg => let (cs,g) := sg in @reduceResult ctx ctx' g cs).
  Proof.
    Opaque GoalImplies.
    induction ctx'; simpl; intro; try rewrite (ctx_subst_eta cs).
    { simpl. red. intros.
      destruct x; destruct y; simpl in *; auto. }
    { simpl. red; intros.
      destruct x; destruct y; simpl in *; eauto.
      apply (IHctx' (fromAll c, GAll t g)
                    (fromAll c0, GAll_do_solved t g0)); clear IHctx'.
      simpl. intros; inv_all; forward_reason.
      Transparent GoalImplies.
      simpl in *; intros. ; inv_all; forward_reason.

      destruct WT. forwardy.
      destruct (drop_exact_append_exact (t :: nil) (getVars (Ctx_append ctx ctx'))) as [ ? [ ? ? ] ].
      rewrite H3 in *. inv_all; subst.
      eapply IHctx'; eauto.
      eapply GAll_do_solved_respects. auto. }
    { simpl; red; intros.
      destruct x; destruct y; simpl in *; auto.
      specialize (IHctx'
                    (snd (fromExs c), GExs t (fst (fromExs c)) g)
                    (snd (fromExs c0), GExs_do_solved t (fst (fromExs c0)) g0)).
      red in IHctx'.
      consider (fromExs c); consider (fromExs c0); intros; apply IHctx'; clear IHctx'.
      simpl in *.


simpl. red; intros. inv_all.
      destruct WT. forwardy.
      destruct (drop_exact_append_exact t (getUVars (Ctx_append ctx ctx'))) as [ ? [ ? ? ] ].
      rewrite H6 in *. inv_all; subst.
      eapply IHctx'; eauto.
      eapply GExs_do_solved_respects; eauto.
      rewrite <- countUVars_getUVars.
      eapply WellFormed_entry_WellFormed_pre_entry; eauto. }
    { simpl. red; intros. inv_all.
      eapply IHctx'; eauto.
      eapply GHyp_do_solved_respects; eauto. }
  Qed.
*)


(*
  Fixpoint GExs_reduce' (tes : tenv typ) (m : amap) (g : Goal typ expr)
           (nus : nat) (acc : list (typ * option expr)) (k : list (option expr))
  : Goal typ expr * nat :=
    match tes with
      | nil =>
        let g' := instantiateGoal (adjust (List.rev k) nus) g in
        (GExs_nil_check (List.rev acc) g', nus)
      | te :: tes' =>
        match te with
          | (_,None) =>
            GExs_reduce' tes' g (pred nus) (te :: acc) (None :: k)
          | (_,Some e) =>
            (** TODO: I probably want to do my instantiation here! **)
            GExs_reduce' tes' g (pred nus) acc (Some e :: k)
        end
    end.

  Definition GExs_reduce (tes : list (typ * option expr)) (g : Goal typ expr)
             (nus : nat) : Goal typ expr * nat :=
    GExs_reduce' tes g nus nil nil.

  Eval cbv beta iota zeta delta - [ lt_rem instantiateGoal ] in
      fun t g e => GExs_reduce' ((t,None) :: (t,Some e) :: (t,Some e) :: nil) g 0 nil nil.
*)


(*
  Theorem GExs_do_solved_respects tus tvs ts m
  : forall (WF : WellFormed_pre_entry (length tus) (length ts) m)
           (WT : exists z, amap_substD (tus ++ ts) tvs m = Some z),
    (EqGoal (tus ++ ts) tvs ==> EqGoal tus tvs)%signature
      (GExs_do_solved ts m) (@GExs typ expr ts m).
  Proof.
    red. red. simpl. unfold GExs_do_solved.
    intros. destruct H. split.
    { clear H0.
      destruct x; try eapply WellFormed_Goal_iff_GExs_cancel; eauto.
      destruct (cardinal m ?[ eq ] length ts).
      { split; constructor; eauto. apply H. constructor. }
      { eapply WellFormed_Goal_iff_GExs_cancel; eauto. } }
    { destruct WT.
      destruct x; simpl in *; change_rewrite H1;
      try solve [ destruct H0; constructor;
                  do 5 red; intros;
                  eapply Quant._exists_iff; intros;
                  eapply and_iff; [ equivs; reflexivity | intro; eapply H0 ];
                  solve_equiv_hlist ].
      consider (cardinal m ?[ eq ] length ts).
      { inversion H0; subst.
        intros. simpl. constructor.
        do 5 red; intros. equivs. split; auto.
        intro X; clear X.
        eapply Quant._exists_sem.
        clear H H0 H3.
        (...) }
      { intros. simpl.
        change_rewrite H1.
        inversion H0. constructor. subst.
        do 5 red; intros.
        eapply Quant._exists_iff; intros;
        eapply and_iff; [ equivs; reflexivity | intro ].
        eapply H5. reflexivity. reflexivity. } }
  Qed.

*)

(*
  Definition GExs_consolidate (tes : list (typ * option expr))
             (g : Goal typ expr) : Goal typ expr :=
    match g with
      | GExs tes' g' => GExs (tes ++ tes') g'
      | _ => GExs_nil_check tes g
    end.

  Lemma Proper_GExs
  : forall tus tvs tes,
      Proper (EqGoal (tus ++ map fst tes) tvs ==> EqGoal tus tvs)%signature
             (GExs tes).
  Proof.
    clear; intros.
    red. red. unfold EqGoal.
    simpl. inversion 1; try constructor.
    destruct (goal_substD tus tvs (map fst tes) (map snd tes)); constructor.
    do 5 red; intros; equivs.
    eapply Quant._exists_iff. intros.
    eapply and_iff. reflexivity.
    intros. eapply H2; reflexivity.
  Qed.
*)

(*
  Theorem GExs_consolidate_respects tus tvs tes
  : forall x y,
      (EqGoal (tus ++ map fst tes) tvs)%signature x y ->
      goal_substD tus tvs (map fst tes) (map snd tes) <> None ->
      (EqGoal tus tvs)%signature
         (@GExs typ expr tes x) (GExs_consolidate tes y).
  Proof.
    intros; subst.
    destruct y;
    try solve [ simpl; eapply GExs_nil_check_respects; eauto ].
    etransitivity.
    eapply Proper_GExs. eassumption.
    inversion H; try congruence.
    { unfold EqGoal. simpl.
      forward.
      repeat rewrite map_app.
      rewrite goalD_conv with (pfu := HList.app_ass_trans tus (map fst tes) (map fst l))
                                (pfv := eq_refl).
      autorewrite with eq_rw.
      destruct (goalD ((tus ++ map fst tes) ++ map fst l) tvs y); try constructor.
      { forward. } }
    { unfold EqGoal. simpl.
      repeat rewrite map_app.
      rewrite goalD_conv with (pfu := HList.app_ass_trans tus (map fst tes) (map fst l))
                                (pfv := eq_refl).
      autorewrite with eq_rw.
      forward.
      destruct (goal_substD_app _ _ _ _ _ H0 H4) as [ ? [ ? ? ] ].
      rewrite H7. constructor.
      }
  Qed.
*)

(*
  5 (None :: Some e :: None :: nil)
  5 -> 5
  6 -> e
  7 -> 6
*)

(*
  Fixpoint adjust' (ls : list (option expr)) (d u : nat) : option expr :=
    match ls , u with
      | nil , _ => Some (UVar (d + u))
      | None :: ls' , 0 => Some (UVar d)
      | Some e :: ls' , 0 =>
        Some e (** TODO: I might need to instantiate this **)
      | None :: ls' , S u => adjust' ls' (S d) u
      | Some e :: ls' , S u => adjust' ls' d u
    end.

  Definition adjust (ls : list (option expr)) (nus u : nat) : option expr :=
    match lt_rem u nus with
      | None => None
      | Some r => adjust' ls nus r
*)