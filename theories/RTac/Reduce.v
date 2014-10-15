Require Import Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.

Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Nat.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
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

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Fixpoint instantiateGoal (f : nat -> option expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | GGoal g => GGoal (instantiate f 0 g)
      | GAll t g' => GAll t (instantiateGoal f g')
      | GExs tes g' => GExs (List.map (fun te =>
                                         match te with
                                           | (t,None) => (t,None)
                                           | (t,Some e) => (t,Some (instantiate f 0 e))
                                         end) tes)
                            (instantiateGoal f g')
      | GHyp h g' => GHyp (instantiate f 0 h) (instantiateGoal f g')
      | GConj_ a b =>
        GConj_ (instantiateGoal f a) (instantiateGoal f b)
    end.

  Definition GExs_nil_check (tes : list (typ * option expr))
             (g : Goal typ expr) : Goal typ expr :=
    match tes with
      | nil => g
      | _ :: _ => GExs tes g
    end.

  Theorem GExs_nil_check_respects tus tvs tes
  : (EqGoal (tus ++ map fst tes) tvs ==> EqGoal tus tvs)%signature
         (@GExs typ expr tes) (GExs_nil_check tes).
  Proof.
    red. intros; subst.
    unfold EqGoal in *. simpl.
    destruct tes.
    { simpl in *.
      rewrite goalD_conv with (pfu := HList.app_nil_r_trans tus)
                              (pfv := eq_refl).
      autorewrite with eq_rw.
      inversion H; constructor.
      clear - H2; do 5 red; intros; equivs.
      rewrite and_comm.
      rewrite Data.Prop.And_True_iff.
      rewrite HList.hlist_app_nil_r.
      autorewrite with eq_rw.
      eapply H2; reflexivity. }
    { simpl in *.
      inversion H; try constructor.
      match goal with
        | |- _ _ match ?X with _ => _ end
                 match ?Y with _ => _ end =>
          change Y with X ; destruct X
      end; constructor.
      clear - H2; do 5 red; intros; equivs.
      Lemma exists_iff : forall (T : Type) (P Q : T -> Prop),
                           (forall x, P x <-> Q x) ->
                           ((exists x, P x) <-> (exists x, Q x)).
      Proof.
        clear. intros. setoid_rewrite H. reflexivity.
      Qed.
      eapply exists_iff. intros.
      eapply Quant._exists_iff. intros.
      eapply and_iff. reflexivity.
      intros. eapply H2; reflexivity. }
  Qed.

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

  Lemma goal_substD_app
  : forall ts' es' tvs ts tus es s1 s2,
      goal_substD tus tvs ts es = Some s1 ->
      goal_substD (tus ++ ts) tvs ts' es' = Some s2 ->
      exists s3,
        goal_substD tus tvs (ts ++ ts') (es ++ es') = Some s3 /\
        forall us us' us'' vs,
          (s1 (hlist_app us us') vs /\
           s2 (hlist_app (hlist_app us us') us'') vs)
          <-> s3 (hlist_app us (hlist_app us' us'')) vs.
  Proof.
    induction ts; simpl; intros.
    { forward. subst. inv_all; subst. simpl in *.
      admit. }
    { forward. subst. destruct o; forward; inv_all; subst.
      { specialize (IHts (tus ++ a :: nil) l).
  Admitted.

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
      { forward. admit. } }
    { unfold EqGoal. simpl.
      repeat rewrite map_app.
      rewrite goalD_conv with (pfu := HList.app_ass_trans tus (map fst tes) (map fst l))
                                (pfv := eq_refl).
      autorewrite with eq_rw.
      forward.
      destruct (goal_substD_app _ _ _ _ _ H0 H4) as [ ? [ ? ? ] ].
      rewrite H7. constructor.
      admit. }
  Qed.

(*
  5 (None :: Some e :: None :: nil)
  5 -> 5
  6 -> e
  7 -> 6
*)

  Variable UVar : nat -> expr.
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
    end.

  Fixpoint GExs_reduce' (tes : list (typ * option expr)) (g : Goal typ expr)
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

  Fixpoint toGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst subst (Ctx_append ctx ctx')) (g : Goal typ expr)
           (su : nat)
           (un vn : nat)
  : Result subst ctx :=
    match ctx' as ctx'
          return ctx_subst subst (Ctx_append ctx ctx') -> Result subst ctx
    with
      | CTop => fun cs => More_ cs g
      | CAll ctx' t => fun cs =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            @toGoal ctx ctx' (fromAll cs) (GAll t g) 0 un vn'
        end
      | CHyp ctx' h => fun cs =>
        @toGoal ctx ctx'  (fromHyp cs) (GHyp h g) 0 un vn
      | CExs ctx' ts => fun cs =>
        let '(s,cs') := fromExs cs in
        let nes := forgets (un - length ts) ts s in
        let '(g',nus') := GExs_reduce (List.combine ts nes) g un in
        @toGoal ctx ctx' cs' g' (S su) nus' vn
    end cs.

  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst subst (Ctx_append ctx ctx'))
           (su : nat) (un vn : nat)
  : Result subst ctx :=
    match ctx' as ctx'
          return ctx_subst subst (Ctx_append ctx ctx') -> Result subst ctx
    with
      | CTop => fun cs => Solved cs
      | CAll ctx' t => fun cs =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            @solveGoal ctx ctx' (fromAll cs) 0 un vn'
        end
      | CHyp ctx' h => fun cs =>
        @solveGoal ctx ctx'  (fromHyp cs) 0 un vn
      | CExs ctx' ts => fun cs =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s,cs') := fromExs cs in
            let nes := forgets (un - length ts) ts s in
            let '(g',nus') := GExs_reduce (List.combine ts nes) GSolved un in
            match g' with
              | GSolved => @solveGoal ctx ctx' cs' (S su) un' vn
              | g' => @toGoal ctx ctx' cs' g' (S su) (S nus') vn
            end
(*            @toGoal ctx ctx' cs' (GExs (List.combine ts nes) GSolved) (S su) un' vn *)
        end
    end cs.

  Definition reduceGoal (ctx ctx' : Ctx typ expr) (s : ctx_subst _ (Ctx_append ctx ctx'))
             (g : Goal typ expr)
             (un vn : nat)
  : Result subst ctx :=
    match g with
      | GSolved => @solveGoal ctx ctx' s 0 un vn
      | _ => @toGoal ctx ctx' s g 0 un vn
    end.

End parameterized.
