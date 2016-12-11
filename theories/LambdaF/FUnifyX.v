Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Structures.Monads.
Require Import MirrorCore.LambdaF.FExpr.

Set Primitive Projections.
Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.


Section unify.
  Variable Tsymbol : forall u, kind u -> Type@{Urefl}.
  Variable TsymbolD : forall u (k : kind u), Tsymbol k -> TSigT k.

  Variable Esymbol : forall u (t : type Tsymbol nil nil (Kstar u)), Type@{Urefl}.
  Variable EsymbolD : forall u (t : type Tsymbol nil nil (Kstar u)),
      @Esymbol u t -> tsigT_star _ (typeD TsymbolD t Hnil Hnil).

(*


  Inductive 
*)


(*
  Inductive TStrengthenU {tus tus'} {tvs}
  : forall {u : univ} {k : kind u}, @type Tsymbol tus tvs u k -> @type Tsymbol tus' tvs u k -> Prop :=
  | TUnif_TArr : forall u a b a' b',
      TUnifiable inst a a' -> TUnifiable inst b b' -> @TUnifiable tus inst tvs u _ (TArr a b) (TArr a' b')
  | TUnif_TApp : forall k1 k2 (a a' : type Tsymbol tus tvs (Karr k1 k2))  b b',
      TUnifiable inst a a' -> TUnifiable inst b b' -> TUnifiable inst (TApp a b) (TApp a' b')
  | TUnif_TPi : forall k (u : univ) (t t' : type Tsymbol tus (k :: tvs) _),
      @TUnifiable _ inst _ u _ t t' -> @TUnifiable tus inst tvs _ _ (TPi t) (TPi t')
  | TUnif_TVar : forall (k : kind U0) (m : member k tvs), TUnifiable inst (TVar _ _ m) (TVar _ _ m)
  | TUnif_TInj : forall u (k : kind u) (s : Tsymbol k), TUnifiable inst (TInj _ _ _ _ s) (TInj _ _ _ _ s)
  | TUnif_TUVarL : forall kv (u : member kv tus) (vs : hlist (@type Tsymbol _ _ _) (Tuctx kv)) t,
      TUnifiable inst (type_subst (Umigrator_id _ _) vs (hlist_get u inst)) t ->
      TUnifiable inst (TUVar u vs) t.
  | TUnif_TUVarL : forall kv (u : member kv tus) (vs : hlist (@type Tsymbol _ _ _) (Tuctx kv)) t,
      TUnifiable inst (type_subst (Umigrator_id _ _) vs (hlist_get u inst)) t ->
      TUnifiable inst (TUVar u vs) t.
*)

  SearchAbout hlist.


  Inductive TUnifiable {tus : list Kuvar} (inst : Umigrator Tsymbol tus tus) {tvs : list (kind U0)}
  : forall {u : univ} {k : kind u}, @type Tsymbol tus tvs u k -> @type Tsymbol tus tvs u k -> Prop :=
  | TUnif_TArr : forall u a b a' b',
      TUnifiable inst a a' -> TUnifiable inst b b' -> @TUnifiable tus inst tvs u _ (TArr a b) (TArr a' b')
  | TUnif_TApp : forall k1 k2 (a a' : type Tsymbol tus tvs (Karr k1 k2))  b b',
      TUnifiable inst a a' -> TUnifiable inst b b' -> TUnifiable inst (TApp a b) (TApp a' b')
  | TUnif_TPi : forall k (u : univ) (t t' : type Tsymbol tus (k :: tvs) _),
      @TUnifiable _ inst _ u _ t t' -> @TUnifiable tus inst tvs _ _ (TPi t) (TPi t')
  | TUnif_TVar : forall (k : kind U0) (m : member k tvs), TUnifiable inst (TVar _ _ m) (TVar _ _ m)
  | TUnif_TInj : forall u (k : kind u) (s : Tsymbol k), TUnifiable inst (TInj _ _ _ _ s) (TInj _ _ _ _ s)
  | TUnif_TUVar : forall kv (u : member kv tus) (vs vs' : hlist (@type Tsymbol _ _ _) (Tuctx kv)),
      DepUtil.hlist_Forall2 (@TUnifiable tus inst tvs _) vs vs' ->
      TUnifiable inst (TUVar u vs) (TUVar u vs')
  | TUnif_TUVarL : forall kv (u : member kv tus) (vs : hlist (@type Tsymbol _ _ _) (Tuctx kv)) t,
      TUnifiable inst (type_subst (Umigrator_id _ _) vs (hlist_get u inst)) t ->
      TUnifiable inst (TUVar u vs) t
  | TUnif_TUVarR : forall kv (u : member kv tus) (vs : hlist (@type Tsymbol _ _ _) (Tuctx kv)) t,
      TUnifiable inst t (type_subst (Umigrator_id _ _) vs (hlist_get u inst)) ->
      TUnifiable inst t (TUVar u vs).

  Definition refl_TUnifiable {tus} inst {tvs} {u} {k} t : @TUnifiable tus inst tvs u k t t.
    induction t using type_rect; simpl.
    { constructor; eauto. }
    { constructor; eauto. }
    { constructor; eauto. }
    { constructor; eauto. }
    { constructor; eauto. }
    { eapply TUnif_TUVar.
      induction X; constructor; auto. }
  Defined.

  Definition sym_TUnifiable {tus} inst {tvs} {u} {k} t t'
  : @TUnifiable tus inst tvs u k t t' ->
    @TUnifiable tus inst tvs u k t' t.
  Proof.
    induction 1; constructor; eauto.
    admit.
  Admitted.
    
    


(*
  Variable Tsymbol_eq_dec : forall u (k : kind u) (t1 t2 : Tsymbol k), {t1 = t2} + {t1 <> t2}.
  Variable Esymbol_eq_dec : forall u t (e1 e2 : @Esymbol u t), {e1 = e2} + {e1 <> e2}.
*)
