Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.SubstWt.

Set Implicit Arguments.
Set Strict Implicit.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.

  Section logicT.
    Variable tyProp : type Tsymbol.
    Variable forall_prop : forall (T : Type),
        (T -> typeD TsymbolD tyProp) ->
        typeD TsymbolD tyProp.


    Fixpoint foralls_prop (ts : list (type Tsymbol))
    : (hlist (typeD TsymbolD) ts -> typeD TsymbolD tyProp) ->
      typeD TsymbolD tyProp :=
      match ts with
      | nil => fun k => k Hnil
      | t :: ts => fun k =>
        foralls_prop (fun vs =>
                        forall_prop (fun v => k (Hcons v vs)))
      end.

    Fixpoint foralls_uvar_prop (ts : list (Tuvar Tsymbol))
    : (hlist (fun tst => hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst)) ts -> Prop) ->
      Prop :=
      match ts with
      | nil => fun k => k Hnil
      | t :: ts => fun k =>
        foralls_uvar_prop (fun vs => forall v, k (Hcons v vs))
      end.

    Variable impl_prop :
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp.

    Require Import ExtLib.Structures.Applicative.

    Section impls.
      Context {tus : list (Tuvar Tsymbol)} {tvs : list (type Tsymbol)}.
      Fixpoint impls_prop (ts : list (typeD TsymbolD tyProp))
               (post : typeD TsymbolD tyProp)
      : typeD TsymbolD tyProp :=
        match ts with
        | nil => post
        | t :: ts =>
          impl_prop t (impls_prop ts post)
        end.
    End impls.

    Variable m : Type -> Type.

    Inductive wtgoal tus tvs : Type :=
    | wtSolved : wtgoal tus tvs
    | wtGoal   : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs
    | wtConj   : wtgoal tus tvs -> wtgoal tus tvs -> wtgoal tus tvs
    | wtHyp    : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs -> wtgoal tus tvs
    | wtAll    : forall t, wtgoal tus (t :: tvs) -> wtgoal tus tvs.

    Variables Pre Post : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.

    (** NOTE: [logicT] does not form a monad due to the generalization
     **       over the indices.

     **)
    Definition logicT : Type :=
      forall tus tvs
        (prems : list (wtexpr Esymbol tus tvs tyProp))
        (inst  : Inst Esymbol tus)
        (goal  : Pre tus tvs),
        m { tus' : _
          & Post tus' tvs
          * Inst Esymbol tus'
          * migrator Esymbol tus tus' }%type.

    Variable PreD : forall {tus tvs}, Pre tus tvs ->
                                      exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable PostD : forall {tus tvs}, Post tus tvs ->
                                       exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable mD : forall T (TD : T -> Prop), m T -> Prop.

    Variable tyProp_to_Prop : typeD TsymbolD tyProp -> Prop.
    Variable Prop_to_tyProp : Prop -> typeD TsymbolD tyProp.

    Definition logicT_spec (l : logicT) : Prop :=
      forall tus tvs prems goal inst result,
        l tus tvs prems inst goal = result ->
        mD (fun t =>
                let '(existT _ tus' (post, inst', trans)) := t in
                @foralls_uvar_prop tus' (fun us' =>
                  let us := migrate_env EsymbolD trans us' in
                  InstD EsymbolD inst' us' ->
                  tyProp_to_Prop
                    (@foralls_prop tvs (fun vs =>
                       impls_prop (map (fun p => wtexprD EsymbolD p us vs) prems)
                                  (impl_prop (@PostD _ _ post us' vs)
                                             (@PreD  _ _ goal us  vs))))))
           result.
  End logicT.
End simple_dep_types.





(*
    Definition logicT_cps (Pre Post : _ -> _ -> Type) : Type :=
      forall tus tvs
        (prems : list (wtexpr Esymbol tus tvs tyProp))
        (goal  : Pre tus tvs)
        (inst  : Inst Esymbol tus)
        (T : Type)
        (success : forall tus' : _ ,
            list (wtexpr Esymbol tus tvs tyProp) ->
            Post tus' tvs ->
            Inst Esymbol tus' ->
            migrator tus tus' ->
            m T)
        (fail : unit -> m T),
        m T.



    Definition with_uvars tus (T : list (Tuvar Tsymbol) -> Type) : Type :=
      Inst Esymbol tus ->
      m { tus' : _ & T tus' * Inst Esymbol tus' *
                     forall ts t, Member.member (ts,t) tus -> wtexpr Esymbol tus' ts t }%type.

    Definition in_context tvs (T : Type) : Type :=
        wtctxD
*)