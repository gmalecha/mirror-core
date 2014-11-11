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

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.

  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Variable UVar : nat -> expr.

  Fixpoint instantiateGoal (f : nat -> option expr) (g : Goal typ expr)
  : Goal typ expr :=
    match g with
      | GSolved => GSolved
      | GGoal g => GGoal (instantiate f 0 g)
      | GAll t g' => GAll t (instantiateGoal f g')
      | GExs ts sub g' =>
        GExs ts (amap_instantiate instantiate f sub) (instantiateGoal f g')
      | GHyp h g' => GHyp (instantiate f 0 h) (instantiateGoal f g')
      | GConj_ a b =>
        GConj_ (instantiateGoal f a) (instantiateGoal f b)
    end.

  (** TODO: Move to Data.Prop **)
  Lemma exists_iff : forall (T : Type) (P Q : T -> Prop),
                       (forall x, P x <-> Q x) ->
                       ((exists x, P x) <-> (exists x, Q x)).
  Proof.
    clear. intros. setoid_rewrite H. reflexivity.
  Qed.

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
        eapply only_in_range_0_substD with (tus := tus++nil) (tvs:=tvs) in H.
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

(*
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
*)

  Fixpoint toGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst (Ctx_append ctx ctx')) (g : Goal typ expr)
           (un vn : nat)
  : Result ctx :=
    match ctx' as ctx'
          return ctx_subst (Ctx_append ctx ctx') -> Result ctx
    with
      | CTop _ _ => fun cs => More_ cs g
      | CAll ctx' t => fun cs =>
        match vn with
          | 0 => (** STUCK **)
            Fail
          | S vn' =>
            @toGoal ctx ctx' (fromAll cs) (GAll t g) un vn'
        end
      | CHyp ctx' h => fun cs =>
        @toGoal ctx ctx'  (fromHyp cs) (GHyp h g) 0 un vn
      | CExs ctx' ts => fun cs =>
        match un with
          | 0 => (** STUCK **)
            Fail
          | S un' =>
            let '(s',ne) := forget un' s in
            match ne with
              | None =>
                toGoal ctx' s' (GEx l ne g) (S su) un' vn
              | Some e =>
                let g' :=
                    instantiateGoal
                      (fun u => if u ?[ eq ] un' then Some e
                                else
                                  if u ?[ gt ] un' then
                                    Some (UVar (u - 1))
                                  else
                                    None) g
                in
                toGoal ctx' s' (* (GEx l (Some e) *) g' (S su) un' vn
            end
        end
    end cs.

(*
  (** This assumes that the goal is a [GSolved] **)
  Fixpoint solveGoal (ctx ctx' : Ctx typ expr)
           (cs : ctx_subst (Ctx_append ctx ctx'))
           (su : nat) (un vn : nat)
  : Result ctx :=
    match ctx' as ctx'
          return ctx_subst (Ctx_append ctx ctx') -> Result ctx
    with
      | CTop _ _ => fun cs => Solved cs
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
*)

  Definition reduceGoal (ctx ctx' : Ctx typ expr)
             (s : ctx_subst (Ctx_append ctx ctx'))
             (g : Goal typ expr)
             (un vn : nat)
  : Result ctx :=
    @toGoal ctx ctx' s g un vn.
(*
    match g with
      | GSolved => @solveGoal ctx ctx' s 0 un vn
      | _ =>
    end.
*)

End parameterized.
