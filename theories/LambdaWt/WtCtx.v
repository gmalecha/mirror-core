Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.SubstWt.
Require Import MirrorCore.LambdaWt.WtMigrator.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.

  Section with_existentials.
    (** This is the universe with operators for [forall] and [impl] *)
    Variable tyProp : type Tsymbol.
    Context {LogicOps_tyProp : ILogicOps (typeD TsymbolD tyProp)}.
    Context {Logic_tyProp : ILogic (typeD TsymbolD tyProp)}.

    (** Goals **)
    Inductive wtgoal tus tvs : Type :=
    | wtSolved : wtgoal tus tvs
    | wtGoal   : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs
    | wtConj   : wtgoal tus tvs -> wtgoal tus tvs -> wtgoal tus tvs
    | wtHyp    : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs -> wtgoal tus tvs
    | wtAll    : forall t, wtgoal tus (t :: tvs) -> wtgoal tus tvs.
    Arguments wtSolved {_ _}.
    Arguments wtGoal {_ _} _.
    Arguments wtConj {_ _} _ _.
    Arguments wtHyp {_ _} _ _.
    Arguments wtAll {_ _} _ _.

    Section wtgoal_subst.
      Context {tus tus' : list (Tuvar Tsymbol)}.
      Variable mig : migrator Esymbol tus tus'.

      Fixpoint wtgoal_subst {tvs tvs'}
               (sVar : hlist (wtexpr Esymbol tus' tvs') tvs)
               (gl : wtgoal tus tvs)
      : wtgoal tus' tvs'.
      refine
        match gl with
        | wtSolved => wtSolved
        | wtGoal gl => wtGoal (subst sVar (migrate_expr mig gl))
        | wtConj l r =>
          wtConj (wtgoal_subst _ _ sVar l) (wtgoal_subst _ _ sVar r)
        | wtHyp p g =>
          wtHyp (subst sVar (migrate_expr mig p)) (wtgoal_subst _ _ sVar g)
        | wtAll t g =>
          wtAll t (wtgoal_subst _ _
                                (Hcons (wtVar (Member.MZ _ _)) _) g)
        end.
      eapply hlist_map.
      2: eapply sVar.
      intros.
      eapply (@wtexpr_lift _ _ tus' _ _ (_::nil) nil X).
      Defined.
    End wtgoal_subst.

    Fixpoint wtgoalD {tus tvs} (g : wtgoal tus tvs) {struct g}
    : exprT TsymbolD tus tvs (typeD TsymbolD tyProp) :=
      match g with
      | wtSolved => pure ltrue
      | wtGoal g => wtexprD EsymbolD g
      | wtConj l r =>
        ap (ap (pure land) (wtgoalD l)) (wtgoalD r)
      | wtHyp h g => ap (ap (pure limpl) (wtexprD EsymbolD h)) (wtgoalD g)
      | @wtAll _ _ t g =>
        let gD := wtgoalD g in
        ap (T:=exprT TsymbolD tus tvs) (pure (@lforall _ _ (typeD TsymbolD t)))
           (fun us vs v => gD us (Hcons v vs))
      end.


    Inductive wtctx (tus : list (Tuvar Tsymbol)) : list (type Tsymbol) -> Type :=
    | ctx_Top : wtctx tus nil
    | ctx_All : forall t {ts}, wtctx tus ts -> wtctx tus (t :: ts)
    | ctx_Hyp : forall {ts}, wtexpr Esymbol tus ts tyProp ->
                             wtctx tus ts -> wtctx tus ts
(*
    | ctx_Left : forall {ts}, wtgoal tus ts -> wtctx tus ts -> wtctx tus ts
    | ctx_Right : forall {ts}, wtgoal tus ts -> wtctx tus ts -> wtctx tus ts
*)
(*
    | ctx_MDelay : forall {tus' tvs},
        migrator Esymbol tus' tus ->
        wtctx tus' tvs -> wtctx tus tvs
*)
    .
    Arguments ctx_Top {_}.
    Arguments ctx_All {_} _ {_} _.
    Arguments ctx_Hyp {_ _} _ _.
(*
    Arguments ctx_Left {_ _} _ _.
    Arguments ctx_Right {_ _} _ _.
*)
(*
    Arguments ctx_MDelay {_ _ _} _ _.
*)

    Arguments WtMigrator.vars_id {_ _ _ tvs} : rename.

    Fixpoint force_ctx {tus tus' tvs} (mig : migrator Esymbol tus tus')
             (ctx : wtctx tus tvs) : wtctx tus' tvs :=
      match ctx in wtctx _ tvs return wtctx tus' tvs with
      | ctx_Top => ctx_Top
      | ctx_All t c => ctx_All t (force_ctx mig c)
      | ctx_Hyp p c => ctx_Hyp (migrate_expr mig p) (force_ctx mig c)
(*
      | ctx_Left g c =>
        ctx_Left (wtgoal_subst mig WtMigrator.vars_id g) (force_ctx mig c)
      | ctx_Right g c =>
        ctx_Right (wtgoal_subst mig WtMigrator.vars_id g) (force_ctx mig c)
*)
(*
      | ctx_MDelay m c => force_ctx (migrator_compose m mig) c
*)
      end.

    Fixpoint wtctxD {tus} {ts : list (type Tsymbol)} (ctx : wtctx tus ts)
    : exprT TsymbolD tus ts (typeD TsymbolD tyProp) ->
      exprT TsymbolD tus nil (typeD TsymbolD tyProp) :=
      match ctx in wtctx _ ts
            return exprT TsymbolD tus ts (typeD TsymbolD tyProp) ->
                   exprT TsymbolD tus nil (typeD TsymbolD tyProp)
      with
      | ctx_Top => fun K => K
      | ctx_All t ctx' => fun K =>
        wtctxD ctx'
               (fun us vs => lforall (fun v => K us (HList.Hcons v vs)))
      | ctx_Hyp t ctx' => fun K =>
        wtctxD ctx'
               (fun us vs => wtexprD EsymbolD t us vs -->> K us vs)
(*
      | ctx_Left g ctx' => fun K =>
        wtctxD ctx'
               (fun us vs => wtgoalD g us vs //\\ K us vs)
      | ctx_Right g ctx' => fun K =>
        wtctxD ctx'
               (fun us vs => K us vs //\\ wtgoalD g us vs)
*)
(*
      | ctx_MDelay mig ctx' => fun K us vs =>
        wtctxD _ _ ctx' _ _ vs
*)
      end.

  End with_existentials.

End simple_dep_types.

Arguments wtgoal {_} Esymbol _ _ _.
Arguments wtAll {_ _ _ _ _} _ _.
Arguments wtSolved {_ _ _ _ _}.
Arguments wtGoal {_ _ _ _ _} _.
Arguments wtHyp {_ _ _ _ _} _ _.
Arguments wtConj {_ _ _ _ _} _ _.
Arguments ctx_Top {_ _ _ _}.
Arguments ctx_All {_ _ _ _} _ {_} _.
Arguments ctx_Hyp {_ _ _ _ _} _ _.
(*
Arguments ctx_Left {_ _ _ _ _} _ _.
Arguments ctx_Right {_ _ _ _ _} _ _.
*)
Arguments wtgoalD {_ _ _} EsymbolD [tyProp] {_} [_ _] _ _ _.