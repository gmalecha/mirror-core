Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  (** TODO: I might want some way to maintain external state **)
  Variable subst : Type.

  Inductive Result : Type :=
  | Fail
  | Solved : list typ -> list typ -> subst -> Result
  | More : list typ -> list typ -> subst -> list expr -> expr -> Result.

  Definition stac : Type :=
    list typ -> list typ -> subst -> list expr -> expr ->
    Result.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Lemma propD_conv
  : forall (tus tvs tus' tvs' : list typ) (pfu : tus' = tus) (pfv : tvs' = tvs),
      propD tus tvs =
      match pfu in _ = tu , pfv in _ = tv
            return expr -> option (HList.hlist typD tu -> HList.hlist typD tv -> Prop)
      with
        | eq_refl , eq_refl => propD tus' tvs'
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Definition stateD tus tvs (s : subst) (hs : list expr) (g : expr)
  : ResType tus tvs Prop :=
    match propD tus tvs g
        , mapT (F:=option) (T:=list) (propD tus tvs) hs
        , substD tus tvs s
    with
      | Some G , Some Hs , Some sV =>
        Some (fun us vs =>
                Forall (fun x => x us vs) Hs ->
                sV us vs /\ G us vs)
      | _ , _ , _ => None
    end.

  Lemma stateD_conv
  : forall (tus tvs tus' tvs' : list typ) (pfu : tus' = tus) (pfv : tvs' = tvs),
      stateD tus tvs =
      match pfu in _ = tu , pfv in _ = tv
            return _ -> _ -> _ ->
                   option (HList.hlist typD tu -> HList.hlist typD tv -> _)
      with
        | eq_refl , eq_refl => stateD tus' tvs'
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Definition resultD tus tvs (r : Result)
             (P : HList.hlist _ tus -> HList.hlist _ tvs -> Prop)
  : Prop :=
    match r with
      | Fail => True
      | Solved tus' tvs' s' =>
        WellFormed_subst s' /\
        match substD (tus ++ tus') (tvs ++ tvs') s' with
          | None => False
          | Some s'V =>
            (** The problem with [exists] out here is that we don't know that
             ** the values are the same before and after. This is why it makes
             ** sense to put [forall] in both places
             **)
            forall us vs,
              (exists us', forall vs',
                 let us := HList.hlist_app us us' in
                 let vs := HList.hlist_app vs vs' in
                 s'V us vs) ->
              P us vs
        end
      | More tus' tvs' s' hs' g' =>
        WellFormed_subst s' /\
        match stateD (tus ++ tus') (tvs ++ tvs') s' hs' g' with
          | Some G' =>
            forall us vs,
              (exists us', forall vs',
                 let us := HList.hlist_app us us' in
                 let vs := HList.hlist_app vs vs' in
                 G' us vs) ->
              P us vs
          | _ => False
        end
    end.

  Lemma resultD_conv
  : forall (tus tvs tus' tvs' : list typ) (pfu : tus' = tus) (pfv : tvs' = tvs),
      @resultD tus tvs =
      match pfu in _ = tu , pfv in _ = tv
            return _ ->
                   (HList.hlist typD tu -> HList.hlist typD tv -> _) -> _
      with
        | eq_refl , eq_refl => @resultD tus' tvs'
      end.
  Proof.
    destruct pfu; destruct pfv. reflexivity.
  Qed.

  Definition WellFormed_result (r : Result) : Prop :=
    match r with
      | Fail => True
      | Solved _ _ s => WellFormed_subst s
      | More _ _ s _ _ => WellFormed_subst s
    end.

  Definition stac_sound' (tac : stac) : Prop :=
    forall tus tvs s hs gs,
      WellFormed_subst s ->
      WellFormed_result (tac tus tvs s hs gs) /\
      match stateD tus tvs s hs gs with
        | None => True
        | Some P =>
          @resultD tus tvs (tac tus tvs s hs gs) P
      end.

  Definition stac_sound (tac : stac) : Prop
  := forall tus tvs s (hs : list expr) (g : expr),
       WellFormed_subst s ->
       match tac tus tvs s hs g with
         | Fail => True
         | Solved tus' tvs' s' =>
           WellFormed_subst s' /\
           match stateD tus tvs s hs g with
             | Some G =>
               match substD (tus ++ tus') (tvs ++ tvs') s' with
                 | None => False
                 | Some s'V =>
                   forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
                     (exists us', forall vs',
                        let us := HList.hlist_app us us' in
                        let vs := HList.hlist_app vs vs' in
                        s'V us vs) ->
                     G us vs
               end
             | _ => True
           end
         | More tus' tvs' s' hs' g' =>
           WellFormed_subst s' /\
           match stateD tus tvs s hs g with
             | Some G =>
               match stateD (tus ++ tus') (tvs ++ tvs') s' hs' g' with
                 | Some G' =>
                   forall us vs,
                     (exists us', forall vs',
                        let us := HList.hlist_app us us' in
                        let vs := HList.hlist_app vs vs' in
                        G' us vs) ->
                     G us vs
                 | _ => False
               end
             | _ => True
           end
       end.

  Definition stac_sound_old (tac : stac) : Prop
  := forall tus tvs s (hs : list expr) (g : expr),
       WellFormed_subst s ->
       match tac tus tvs s hs g with
         | Fail => True
         | Solved tus' tvs' s' =>
           WellFormed_subst s' /\
           match propD tus tvs g
               , mapT (F:=option) (T:=list) (propD tus tvs) hs
               , substD tus tvs s
           with
             | Some G , Some Hs , Some sV =>
               match substD (tus ++ tus') (tvs ++ tvs') s' with
                 | None => False
                 | Some s'V =>
                   forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
                     (exists us', forall vs',
                        s'V (HList.hlist_app us us') (HList.hlist_app vs vs')) ->
                     Forall (fun P => P us vs) Hs ->
                     G us vs /\ sV us vs
               end
             | _ , _ , _ => True
           end
         | More tus' tvs' s' hs' g' =>
           WellFormed_subst s' /\
           match propD tus tvs g
               , mapT (F:=option) (T:=list) (propD tus tvs) hs
               , substD tus tvs s
           with
             | Some G , Some Hs , Some sV =>
               match propD (tus ++ tus') (tvs ++ tvs') g'
                   , mapT (F:=option) (T:=list) (propD (tus ++ tus') (tvs ++ tvs')) hs'
                   , substD (tus ++ tus') (tvs ++ tvs') s'
               with
                 | Some G' , Some Hs' , Some s'V =>
                   forall us vs,
                     (exists us', forall vs',
                        let us := HList.hlist_app us us' in
                        let vs := HList.hlist_app vs vs' in
                        Forall (fun P => P us vs) Hs' ->
                           s'V us vs
                        /\ G' us vs) ->
                     Forall (fun P => P us vs) Hs ->
                     G us vs /\ sV us vs
                 | _ , _ , _ => False
               end
             | _ , _ , _ => True
           end
       end.

  Lemma And_True_iff : forall P, (P /\ True) <-> P.
  Proof. clear. intuition. Qed.
  Lemma And_And_iff : forall P, (P /\ P) <-> P.
  Proof. clear. intuition. Qed.
  Lemma And_assoc : forall P Q R, (P /\ Q /\ R) <-> ((P /\ Q) /\ R).
  Proof. clear. intuition. Qed.
  Lemma And_cancel
  : forall P Q R : Prop, (P -> (Q <-> R)) -> ((P /\ Q) <-> (P /\ R)).
  Proof. clear. intuition. Qed.
  Lemma forall_iff : forall T P Q,
                       (forall x,
                          P x <-> Q x) ->
                       ((forall x : T, P x) <-> (forall x : T, Q x)).
  Proof.
    clear. intros. setoid_rewrite H. reflexivity.
  Qed.
  Lemma exists_iff : forall T P Q,
                       (forall x,
                          P x <-> Q x) ->
                       ((exists x : T, P x) <-> (exists x : T, Q x)).
  Proof.
    clear. intros. setoid_rewrite H. reflexivity.
  Qed.

  Theorem stac_sound_stac_sound'
  : forall tac,
      stac_sound tac <-> stac_sound' tac.
  Proof.
    unfold stac_sound, stac_sound'.
    intro.
    repeat (apply forall_iff; intro).
    destruct (stateD x x0 x1 x2 x3).
    { destruct (tac x x0 x1 x2 x3); simpl.
      { intuition. }
      { rewrite And_assoc.
        rewrite And_And_iff. reflexivity. }
      { rewrite And_assoc.
        rewrite And_And_iff. reflexivity. } }
    { destruct (tac x x0 x1 x2 x3); simpl; try reflexivity.
      rewrite And_And_iff. reflexivity. }
  Qed.

  Theorem stac_sound_stac_sound_old
  : forall tac,
      stac_sound tac <-> stac_sound_old tac.
  Proof.
    unfold stac_sound, stac_sound_old.
    intros.
    repeat (apply forall_iff; intro).
    unfold stateD.
    destruct (propD x x0 x3);
      destruct (mapT (T:=list) (F:=option) (propD x x0) x2);
      destruct (substD x x0 x1);
      destruct (tac x x0 x1 x2 x3);
      try destruct (substD (x ++ l0) (x0 ++ l1) s);
      try reflexivity.
    { eapply And_cancel; intros.
      do 2 (eapply forall_iff; intro).
      setoid_rewrite (and_comm (P x5 x6) (P0 x5 x6)).
      reflexivity. }
    { eapply And_cancel; intros.
      destruct (propD (x ++ l0) (x0 ++ l1) e);
        destruct (mapT (T:=list)(F:=option) (propD (x ++ l0) (x0 ++ l1)) l2);
        try reflexivity.
      do 2 (eapply forall_iff; intro).
      setoid_rewrite (and_comm (P x5 x6) (P0 x5 x6)).
      reflexivity. }
    { apply And_cancel; intros.
      destruct (propD (x ++ l0) (x0 ++ l1) e);
        destruct (mapT (T:=list)(F:=option) (propD (x ++ l0) (x0 ++ l1)) l2);
        try reflexivity. }
  Qed.

  Lemma stateD_Some
  : forall tus tvs s hs g D,
      stateD tus tvs s hs g = Some D ->
      exists sD hD gD,
        propD tus tvs g = Some gD /\
        mapT (F:=option) (T:=list) (propD tus tvs) hs = Some hD /\
        substD tus tvs s = Some sD /\
        forall us vs,
          D us vs <-> (Forall (fun x => x us vs) hD ->
                       sD us vs /\ gD us vs).
  Proof.
    unfold stateD. intros.
    forwardy.
    do 3 eexists; repeat (split; [ eassumption | ]).
    inv_all. subst. reflexivity.
  Qed.

  Lemma More_sound
  : forall tus tvs s hs g,
      match stateD tus tvs s hs g with
        | Some G =>
          match stateD (tus ++ nil) (tvs ++ nil) s hs g with
            | Some G' =>
              forall (us : HList.hlist typD tus)
                     (vs : HList.hlist typD tvs),
                (exists us', forall vs' : HList.hlist typD nil,
                   let us := HList.hlist_app us us' in
                   let vs := HList.hlist_app vs vs' in
                   G' us vs) ->
                G us vs
            | _ => False
          end
        | _ => True
      end.
  Proof.
    intros.
    forward.
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end.
    { destruct H1.
      specialize (H1 Hnil).
      rewrite (HList.hlist_eta x) in *.
      do 2 rewrite HList.hlist_app_nil_r in H1.
      destruct (eq_sym (HList.app_nil_r_trans tus)).
      destruct (eq_sym (HList.app_nil_r_trans tvs)).
      simpl in *. rewrite H in H0. inv_all; subst; assumption. }
    { do 2 rewrite List.app_nil_r in *.
      congruence. }
  Qed.

  Lemma stac_sound_Solved (tac : stac) (Htac : stac_sound tac)
  : forall tus tvs sub hs g tus' tvs' sub',
      tac tus tvs sub hs g = Solved tus' tvs' sub' ->
      WellFormed_subst sub ->
      WellFormed_subst sub' /\
      match stateD tus tvs sub hs g with
        | Some G =>
          match substD (tus ++ tus') (tvs ++ tvs') sub' with
            | None => False
            | Some s'V =>
              forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
                (exists us', forall vs',
                   let us := HList.hlist_app us us' in
                   let vs := HList.hlist_app vs vs' in
                   s'V us vs) ->
                G us vs
          end
        | _ => True
      end.
  Proof.
    intros.
    specialize (Htac tus tvs sub hs g).
    rewrite H in Htac. eauto.
  Qed.

  Lemma stac_sound_More (tac : stac) (Htac : stac_sound tac)
  : forall tus tvs sub hs g tus' tvs' sub' hs' g',
      tac tus tvs sub hs g = More tus' tvs' sub' hs' g'->
      WellFormed_subst sub ->
      WellFormed_subst sub' /\
      match stateD tus tvs sub hs g with
        | Some G =>
          match stateD (tus ++ tus') (tvs ++ tvs') sub' hs' g' with
            | Some G' =>
              forall us vs,
                (exists us', forall vs',
                   let us := HList.hlist_app us us' in
                   let vs := HList.hlist_app vs vs' in
                   G' us vs) ->
                G us vs
            | _ => False
          end
        | _ => True
      end.
  Proof.
    intros.
    specialize (Htac tus tvs sub hs g).
    rewrite H in Htac. eauto.
  Qed.

End parameterized.

Arguments stac_sound {typ expr subst _ _ _ _ _} _.
Arguments propD {typ expr RType Expr Typ0} tus tvs e : rename.
Arguments Fail {typ expr subst}.
Arguments Solved {typ expr subst} _ _ _.
Arguments More {typ expr subst} _ _ _ _ _.

Export MirrorCore.EnvI.
Export MirrorCore.SymI.
Export MirrorCore.ExprI.
Export MirrorCore.TypesI.
Export MirrorCore.SubstI.