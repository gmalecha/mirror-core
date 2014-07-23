Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI3.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  (** TODO: I might want some way to maintain external state **)
  Variable subst : Type.

  Inductive Result : Type :=
  | Fail
      (** TODO: Should [Solved] not have extended environments? **)
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

  Definition goalD (tus tvs : list typ) (goal : expr) : ResType tus tvs Prop :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return ResType tus tvs Prop with
      | None => None
      | Some val =>
        Some match typ0_cast nil in _ = T return HList.hlist _ tus -> HList.hlist _ tvs -> T with
               | eq_refl => val
             end
    end.

  Definition stac_sound (tac : stac) : Prop
  := forall tus tvs s (hs : list expr) (g : expr),
       WellFormed_subst s ->
       match tac tus tvs s hs g with
         | Fail => True
         | Solved tus' tvs' s' =>
           WellFormed_subst s' /\
           match goalD tus tvs g
               , mapT (F:=option) (T:=list) (goalD tus tvs) hs
               , substD tus tvs s
           with
             | Some G , Some Hs , Some sV =>
               match substD (tus ++ tus') (tvs ++ tvs') s' with
                 | None => False
                 | Some s'V =>
                   forall (us : HList.hlist _ tus) (vs : HList.hlist _ tvs),
                     (exists us' vs',
                        s'V (HList.hlist_app us us') (HList.hlist_app vs vs')) ->
                     Forall (fun P => P us vs) Hs ->
                     G us vs /\ sV us vs
               end
             | _ , _ , _ => True
           end
         | More tus' tvs' s' hs' g' =>
           WellFormed_subst s' /\
           match goalD tus tvs g
               , mapT (F:=option) (T:=list) (goalD tus tvs) hs
               , substD tus tvs s
           with
             | Some G , Some Hs , Some sV =>
               match goalD (tus ++ tus') (tvs ++ tvs') g'
                   , mapT (F:=option) (T:=list) (goalD (tus ++ tus') (tvs ++ tvs')) hs'
                   , substD (tus ++ tus') (tvs ++ tvs') s'
               with
                 | Some G' , Some Hs' , Some s'V =>
                   forall us vs,
                     (exists us' vs',
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

  Lemma More_sound
  : forall tus tvs s hs g,
      match goalD tus tvs g
          , mapT (F:=option) (T:=list) (goalD tus tvs) hs
          , substD tus tvs s
      with
        | Some G , Some Hs , Some sV =>
          match goalD (tus ++ nil) (tvs ++ nil) g
              , mapT (F:=option) (T:=list) (goalD (tus ++ nil) (tvs ++ nil)) hs
              , substD (tus ++ nil)%list (tvs ++ nil)%list s
          with
            | Some G' , Some Hs' , Some s'V =>
              forall (us : HList.hlist (typD nil) tus)
                     (vs : HList.hlist (typD nil) tvs),
                (exists us' vs' : HList.hlist (typD nil) nil,
                   let us := HList.hlist_app us us' in
                   let vs := HList.hlist_app vs vs' in
                   Forall (fun P => P us vs) Hs' ->
                   s'V us vs /\ G' us vs) ->
                Forall (fun P => P us vs) Hs ->
                G us vs /\ sV us vs
            | _ , _ , _ => False
          end
        | _ , _ , _ => True
      end.
  Proof.
    intros.
    forward.
    repeat match goal with
             | |- match ?X with _ => _ end =>
               consider X; intros
           end.
    { destruct H5 as [ ? [ ? ? ] ].
      rewrite (HList.hlist_eta x) in *.
      rewrite (HList.hlist_eta x0) in *.
      do 2 rewrite HList.hlist_app_nil_r in H5.
      destruct (eq_sym (HList.app_nil_r_trans tus)).
      destruct (eq_sym (HList.app_nil_r_trans tvs)).
      rewrite H0 in *. rewrite H1 in *. rewrite H in *.
      inv_all; subst.
      simpl in H5. eapply H5 in H6.
      tauto. }
    { do 2 rewrite List.app_nil_r in *.
      congruence. }
    { do 2 rewrite List.app_nil_r in *.
      congruence. }
    { do 2 rewrite List.app_nil_r in *.
      congruence. }
  Qed.

End parameterized.

Arguments stac_sound {typ expr subst _ _ _ _ _} _.

Export MirrorCore.EnvI.
Export MirrorCore.SymI.
Export MirrorCore.ExprI.
Export MirrorCore.TypesI.
Export MirrorCore.SubstI3.