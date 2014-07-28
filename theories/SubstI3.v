Require Import Coq.Lists.List.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.

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
: forall A T {ed : @EqDec _ (@eq T) _} (F : T -> Type) G a b c d e f,
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
  Variable RType_type : RType typ.
  Variable expr : Type.
  Variable Expr_expr : Expr _ expr.

  Let uvar : Type := nat.

  (** TODO:
   ** Should [mentionsU] be part of [Expr]?
   **)
  Variable mentionsU : uvar -> expr -> bool.

  Class Subst :=
  { lookup : uvar -> T -> option expr
  ; domain : T -> list uvar
  }.

  Class SubstUpdate :=
  { set : uvar -> expr -> T -> option T (** TODO: Should this be typed? **)
  ; drop : uvar -> T -> option T
  ; empty : T
  }.

  Class SubstOk (S : Subst) : Type :=
  { WellFormed_subst : T -> Prop
  ; substD : forall (tus tvs : tenv typ), T -> ResType tus tvs Prop
  ; substD_weaken
    : forall tus tvs tus' tvs' s sD,
        substD tus tvs s = Some sD ->
        exists sD',
          substD (tus ++ tus') (tvs ++ tvs') s = Some sD' /\
          forall us us' vs vs',
            sD us vs <-> sD' (hlist_app us us') (hlist_app vs vs')
  ; substD_lookup
    : forall s uv e,
        WellFormed_subst s ->
        lookup uv s = Some e ->
        forall tus tvs sD,
          substD tus tvs s = Some sD ->
          exists t val,
            exists pf : Some t = nth_error tus uv,
            exprD' tus tvs e t = Some val /\
            forall us vs,
              sD us vs ->
              hlist_nth us uv = match pf in _ = t
                                      return match t with
                                               | Some x => typD nil x
                                               | None => unit
                                             end
                                with
                                  | eq_refl => val us vs
                                end
  ; WellFormed_domain : forall s ls,
      WellFormed_subst s ->
      domain s = ls ->
      (forall n, In n ls <-> lookup n s <> None)
  }.


  Class SubstUpdateOk (S : Subst) (SU : SubstUpdate) (SOk : SubstOk S) :=
  { WellFormed_empty : WellFormed_subst empty
  ; substD_empty
    : forall tus tvs,
      exists P,
        substD tus tvs empty = Some P /\
        forall us vs, P us vs
  ; set_sound
    : forall uv e s s',
        set uv e s = Some s' ->
        lookup uv s = None ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        (forall tus tvs t val sD,
           substD tus tvs s = Some sD ->
           forall pf : Some t = nth_error tus uv,
           exprD' tus tvs e t = Some val ->
           exists sD', substD tus tvs s' = Some sD' /\
           forall us vs,
             sD' us vs ->
             sD us vs /\
             hlist_nth us uv = match pf in _ = t
                                     return match t with
                                              | Some x => typD nil x
                                              | None => unit
                                            end
                               with
                                 | eq_refl => val us vs
                               end)
  ; drop_sound
    : forall s s' u,
        drop u s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        forall tus tu tvs sD,
          u = length tus ->
          substD (tus ++ tu :: nil) tvs s = Some sD ->
          exists sD',
            substD tus tvs s' = Some sD' /\
            exists e eD,
              lookup u s = Some e /\
              exprD' tus tvs e tu = Some eD /\
              forall us vs,
                sD' us vs ->
                sD (hlist_app us (Hcons (eD us vs) Hnil)) vs
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.

  (** This is the "obvious" extension of [drop] **)
  Fixpoint pull (from : uvar) (len : nat) (s : T) : option T :=
    match len with
      | 0 => Some s
      | S len' => match pull (S from) len' s with
                   | None => None
                   | Some s' => drop from s'
                  end
    end.

  Definition Subst_Extends (a b : T) : Prop :=
    forall tus tvs P Q,
      substD tus tvs b = Some P ->
      substD tus tvs a = Some Q ->
      forall us vs, P us vs -> Q us vs.

  Class NormalizedSubstOk : Type :=
  { lookup_normalized : forall s e u,
      WellFormed_subst s ->
      lookup u s = Some e ->
      forall u' e',
        lookup u' s = Some e' ->
        mentionsU u' e = false
  }.

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
                  return hlist (typD nil) (tus ++ tus') -> hlist (typD nil) t -> Prop
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
                  return hlist (typD nil) t -> hlist (typD nil) _ -> Prop
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

End subst.
