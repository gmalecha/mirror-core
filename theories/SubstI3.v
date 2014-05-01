Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
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

Section subst.
  Variable T : Type.
  (** the [expr] type requires a notion of unification variable **)
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable expr : Type.
  Variable Expr_expr : Expr typD expr.

  Let uvar : Type := nat.

  Class Subst :=
  { lookup : uvar -> T -> option expr
  ; domain : T -> list uvar
  }.

  Class SubstUpdate :=
  { set : uvar -> expr -> T -> option T (** TODO: Should this be typed? **)
  ; pull : uvar -> nat -> T -> option T
  ; empty : T
  }.

  Class SubstOk (S : Subst) : Type :=
  { WellFormed_subst : T -> Prop
  ; substD : forall (tus tvs : tenv typ), T -> ResType typD tus tvs Prop
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
  ; substD_empty : forall tus tvs,
                   exists P,
                     substD tus tvs empty = Some P /\
                     forall us vs, P us vs
  ; set_sound
    : forall uv e s s',
        set uv e s = Some s' ->
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
  ; pull_sound
    : forall s s' u n,
        pull u n s = Some s' ->
        WellFormed_subst s ->
        WellFormed_subst s' /\
        forall tus tus' tvs sD,
          u = length tus ->
          n = length tus' ->
          substD (tus ++ tus') tvs s = Some sD ->
          exists sD',
            substD tus tvs s' = Some sD' /\
            exists eus' : list expr,
              exists us' : hlist (fun t => hlist (typD nil) tus -> hlist (typD nil) tvs -> typD nil t) tus',
                @hlist_build _ _ _ (fun t e => exprD' tus tvs e t) tus' eus' = Some us' /\
                forall us vs,
                  let us' := hlist_map (fun t (x : hlist (typD nil) tus -> hlist (typD nil) tvs -> typD nil t) => x us vs) us' in
                  sD' us vs ->
                  sD (hlist_app us us') vs
  }.

  Variable Subst_subst : Subst.
  Variable SubstOk_subst : SubstOk Subst_subst.

  Definition Subst_Extends (a b : T) : Prop :=
    forall tus tvs P Q,
      substD tus tvs b = Some P ->
      substD tus tvs a = Some Q ->
      forall us vs, P us vs -> Q us vs.

  (** TODO:
   ** Should [mentionsU] be part of [Expr]?
   **)
  Variable mentionsU : uvar -> expr -> bool.

  Class NormalizedSubstOk : Type :=
  { lookup_normalized : forall s e u,
      WellFormed_subst s ->
      lookup u s = Some e ->
      forall u' e',
        lookup u' s = Some e' ->
        mentionsU u' e = false
  }.

End subst.
