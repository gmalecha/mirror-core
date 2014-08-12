Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition stac_cont : Type :=
    (* tus : *) list typ ->
    (* tvs : *) list typ ->
                subst ->
    (* hyps : *) list expr ->
    (* goals : *) list expr ->
    Result typ expr subst.

  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.

  Definition stac_cont_sound (tacC : stac_cont) : Prop :=
    forall tus tvs sub hyps gs,
      WellFormed_subst sub ->
      match tacC tus tvs sub hyps gs with
        | Fail => True
        | Solved tus' tvs' sub' =>
          WellFormed_subst sub' /\
          match mapT (T:=list) (F:=option) (propD (Expr:=Expr_expr) tus tvs) hyps
              , mapT (T:=list) (F:=option) (propD tus tvs) gs
              , substD tus tvs sub
          with
            | Some hD , Some gD , Some sD =>
              match substD (tus ++ tus') (tvs ++ tvs') sub' with
                | Some sD' =>
                  forall (us : hlist (typD nil) tus)
                         (vs : hlist (typD nil) tvs),
                    (exists (us' : hlist (typD nil) tus')
                            (vs' : hlist (typD nil) tvs'),
                       sD' (hlist_app us us') (hlist_app vs vs')) ->
                    Forall
                      (fun P : hlist (typD nil) tus ->
                               hlist (typD nil) tvs -> Prop =>
                         P us vs) hD ->
                    Forall (fun P => P us vs) gD /\ sD us vs
                | _ => False
              end
            | _ , _ , _ => True
          end
        | More tus' tvs' sub' hyps' g' =>
          WellFormed_subst sub' /\
          match mapT (T:=list) (F:=option) (propD (Expr:=Expr_expr) tus tvs) hyps
              , mapT (T:=list) (F:=option) (propD tus tvs) gs
              , substD tus tvs sub
          with
            | Some hD , Some gD , Some sD =>
              match mapT (T:=list) (F:=option) (propD (tus ++ tus') (tvs ++ tvs')) hyps'
                  , propD (tus ++ tus') (tvs ++ tvs') g'
                  , substD (tus ++ tus') (tvs ++ tvs') sub'
              with
                | Some hD' , Some gD' , Some sD' =>
                  forall (us : hlist (typD nil) tus)
                         (vs : hlist (typD nil) tvs),
                    (exists (us' : hlist (typD nil) tus')
                            (vs' : hlist (typD nil) tvs'),
                       let us := hlist_app us us' in
                       let vs := hlist_app vs vs' in
                       Forall
                         (fun P : hlist (typD nil) (tus ++ tus') ->
                                  hlist (typD nil) (tvs ++ tvs') -> Prop =>
                            P us vs) hD' ->
                          sD' us vs
                       /\ gD' us vs) ->
                    Forall
                      (fun P : hlist (typD nil) tus ->
                               hlist (typD nil) tvs -> Prop =>
                         P us vs) hD ->
                    Forall (fun P => P us vs) gD /\ sD us vs
                | _ , _ , _ => False
              end
            | _ , _ , _ => True
          end
      end.

End parameterized.

Arguments stac_cont_sound {typ expr subst RType Typ0 Expr Subst _} _ : rename.