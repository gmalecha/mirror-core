Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Can I do alternation if I can do strengthening of both
 ** unification variables and regular variables?
 ** 1) This means that substD needs strengthening
 ** 2) It also means that hypotheses need to be eliminatable
 **
 **    goal :=
 **      Alls : list typ -> goal -> goal
 **    | Exs : list typ -> goal -> goal
 **    | Hyps : list expr -> goal -> goal
 **    | Goal : expr -> goal.
 **
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  (** TODO: I might want some way to maintain external state **)
  Variable subst : Type.

  (** This is a way to put everything inside there,
   ** an alternative representation is to use a simpler type, i.e.
   **     [list (All | Ex | Hyp)]
   ** to interpret the flattened environments
   **)
  (** NOTE: It seems very important that this is inverted, otherwise
   ** every operation is going to be very expensive.
   **)
  Inductive Goal :=
  | GAlls : list typ -> Goal -> Goal
  | GExs  : list typ -> Goal -> Goal
  | GHyps : list expr -> Goal -> Goal
  | GGoal : subst -> option expr -> Goal.

  (** GoalD **)

  Definition Result := option Goal.
(*
  Inductive Result : Type :=
  | Fail
  | More : Goal -> Result.
*)

  Definition stac : Type :=
    Goal -> Result.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition propD (tus tvs : list typ) (goal : expr) : ResType tus tvs Prop :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return ResType tus tvs Prop with
      | None => None
      | Some val =>
        Some match typ0_cast nil in _ = T return HList.hlist _ tus -> HList.hlist _ tvs -> T with
               | eq_refl => val
             end
    end.

  Fixpoint _foralls (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD nil l,
                              _foralls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD nil l,
                              _exists (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> _impls ls P
    end.

  Fixpoint goalD (tus tvs : list typ) (goal : Goal)
  : ResType tus tvs Prop :=
    match goal with
      | GAlls tvs' goal' =>
        match goalD tus (tvs ++ tvs') goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_foralls tvs' (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tus' goal' =>
        match goalD (tus ++ tus') tvs goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_exists tus' (fun us' => D (HList.hlist_app us us') vs))
        end
      | GHyps hyps' goal' =>
        match mapT (T:=list) (F:=option) (propD tus tvs) hyps' with
          | None => None
          | Some hs =>
            match goalD tus tvs goal' with
              | None => None
              | Some D =>
                Some (fun us vs => _impls (map (fun x => x us vs) hs) (D us vs))
            end
        end
      | GGoal sub' None =>
        match substD tus tvs sub' with
          | Some sD => Some (fun us vs => sD us vs)
          | _ => None
        end
      | GGoal sub' (Some goal') =>
        match substD tus tvs sub'
            , propD tus tvs goal'
        with
          | Some sD , Some gD =>
            Some (fun (us : HList.hlist (typD nil) tus)
                      (vs : HList.hlist (typD nil) tvs)  => sD us vs /\ gD us vs)
          | _ , _ => None
        end
    end.

  Section at_bottom.
    Variable T : Type.
    Variable gt : list typ -> list typ -> Goal -> Goal * T.

    Let under (gt : Goal -> Goal) (x : Goal * T) : Goal * T :=
      let (x,y) := x in
      (gt x, y).

    Fixpoint at_bottom tus tvs (g : Goal) : Goal * T :=
      match g with
        | GAlls x g' => under (GAlls x) (at_bottom tus (tvs ++ x) g')
        | GExs  x g' => under (GExs  x) (at_bottom (tus ++ x) tvs g')
        | GHyps x g' => under (GHyps x) (at_bottom tus tvs g')
        | _ => gt tus tvs g
      end.
  End at_bottom.

  (** On [Proved], I need to check, that means that I probably need to do
   ** deltas so that I know where I need to pull to...
   **)
  Definition with_new_uvar (t : typ) (k : nat -> stac)
  : stac :=
    fun g =>
      let (g',uv) :=
          at_bottom (fun tus _ g => (GExs (t :: nil) g, length tus)) nil nil g
      in
      k uv g'.

  Axiom ty : typ.
  Axiom s : subst.

  Eval compute in fun (f : nat -> stac) => with_new_uvar ty f (GGoal s None).

  Definition with_new_var (t : typ) (k : nat -> stac)
  : stac :=
    fun g =>
      let (g',uv) :=
          at_bottom (fun _ tvs g => (GAlls (t :: nil) g, length tvs)) nil nil g
      in
      k uv g'.
    