Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
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
  | Solved : list typ -> list typ -> subst -> Result
  | More : list typ -> list typ -> subst -> expr -> Result.

  Definition stac : Type :=
    (** TODO: Part of the state is hypotheses **)
    list typ -> list typ -> subst -> expr ->
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
  := forall tus tvs s (g : expr),
       WellFormed_subst s ->
       match tac tus tvs s g with
         | Fail => True
         | Solved tus' tvs' s' =>
           WellFormed_subst s' /\
           match goalD tus tvs g
               , substD tus tvs s
           with
             | Some G , Some sV =>
               match substD (tus ++ tus') (tvs ++ tvs') s' with
                 | None => False
                 | Some s'V =>
                   forall us vs,
                     (exists us' vs',
                        s'V (HList.hlist_app us us') (HList.hlist_app vs vs')) ->
                     G us vs /\ sV us vs
               end
             | _ , _ => True
           end
         | More tus' tvs' s' g' =>
           WellFormed_subst s' /\
           match goalD tus tvs g
               , substD tus tvs s
           with
             | Some G , Some sV =>
               match goalD (tus ++ tus') (tvs ++ tvs') g'
                   , substD (tus ++ tus') (tvs ++ tvs') s'
               with
                 | Some G' , Some s'V =>
                   forall us vs,
                     (exists us' vs',
                           s'V (HList.hlist_app us us') (HList.hlist_app vs vs')
                        /\ G' (HList.hlist_app us us') (HList.hlist_app vs vs')) ->
                     G us vs /\ sV us vs
                 | _ , _ => False
               end
             | _ , _ => True
           end
       end.

  Lemma More_sound
  : forall tus tvs s g,
      match goalD tus tvs g with
        | Some G =>
          match substD tus tvs s with
            | Some sV =>
              match goalD (tus ++ nil) (tvs ++ nil) g with
                | Some G' =>
                  match substD (tus ++ nil)%list (tvs ++ nil)%list s with
                    | Some s'V =>
                      forall (us : HList.hlist (typD nil) tus)
                             (vs : HList.hlist (typD nil) tvs),
                        (exists us' vs' : HList.hlist (typD nil) nil,
                           s'V (HList.hlist_app us us') (HList.hlist_app vs vs') /\
                           G' (HList.hlist_app us us') (HList.hlist_app vs vs')) ->
                        G us vs /\ sV us vs
                    | None => False
                  end
                | None => False
              end
            | None => True
          end
        | None => True
      end.
  Proof.
    intros.
    forward.
    repeat match goal with
             | |- match ?X with _ => _ end =>
               consider X; intros
           end.
    { destruct H3 as [ ? [ ? ? ] ].
      rewrite (HList.hlist_eta x) in *.
      rewrite (HList.hlist_eta x0) in *.
      do 2 rewrite HList.hlist_app_nil_r in H3.
      destruct (eq_sym (HList.app_nil_r_trans tus)).
      destruct (eq_sym (HList.app_nil_r_trans tvs)).
      rewrite H0 in *.
      rewrite H1 in *. inv_all; subst.
      tauto. }
    { do 2 rewrite List.app_nil_r in H2.
      congruence. }
    { do 2 rewrite List.app_nil_r in H1.
      congruence. }
  Qed.

End parameterized.

Arguments stac_sound {typ expr subst _ _ _ _ _} _.

Export MirrorCore.EnvI.
Export MirrorCore.SymI.
Export MirrorCore.ExprI.
Export MirrorCore.TypesI.
Export MirrorCore.SubstI3.