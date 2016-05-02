Require Import Coq.Lists.List.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.SubstWt.

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
    : (HList.hlist (typeD TsymbolD) ts -> typeD TsymbolD tyProp) ->
      typeD TsymbolD tyProp :=
      match ts with
      | nil => fun k => k HList.Hnil
      | t :: ts => fun k =>
        foralls_prop ts (fun vs =>
                           forall_prop _ (fun v => k (HList.Hcons v vs)))
      end.

    Fixpoint foralls_uvar_prop (ts : list (Tuvar Tsymbol))
    : (HList.hlist (fun tst => HList.hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst)) ts -> Prop) ->
      Prop :=
      match ts with
      | nil => fun k => k HList.Hnil
      | t :: ts => fun k =>
        foralls_uvar_prop ts (fun vs => forall v, k (HList.Hcons v vs))
      end.

    Variable impl_prop :
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp.

    Require Import ExtLib.Structures.Applicative.

    Section impls.
      Context {tus : list (Tuvar Tsymbol)} {tvs : list (type Tsymbol)}.
      Fixpoint impls_prop (ts : list (exprT TsymbolD tus tvs (typeD TsymbolD tyProp)))
               (post : exprT TsymbolD tus tvs (typeD TsymbolD tyProp))
      : exprT TsymbolD tus tvs (typeD TsymbolD tyProp) :=
        match ts with
        | nil => post
        | t :: ts =>
          ap (ap (pure impl_prop) t) (impls_prop ts post)
        end.
    End impls.

    Variable m : Type -> Type.

    Inductive wtgoal tus tvs : Type :=
    | wtSolved : wtgoal tus tvs
    | wtGoal   : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs
    | wtConj   : wtgoal tus tvs -> wtgoal tus tvs -> wtgoal tus tvs
    | wtHyp    : wtexpr Esymbol tus tvs tyProp -> wtgoal tus tvs -> wtgoal tus tvs
    | wtAll    : forall t, wtgoal tus (t :: tvs) -> wtgoal tus tvs.

    Definition migrator tus tus' : Type :=
      forall ts t, Member.member (ts,t) tus' -> wtexpr Esymbol tus ts t.

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
          * migrator tus' tus }%type.



    Variable PreD : forall {tus tvs}, Pre tus tvs ->
                                      exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable PostD : forall {tus tvs}, Post tus tvs ->
                                       exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable mD : forall T (TD : T -> Prop), m T -> Prop.

    Variable tyProp_to_Prop : typeD TsymbolD tyProp -> Prop.
    Variable Prop_to_tyProp : Prop -> typeD TsymbolD tyProp.

    Definition migrator_tl {a b c} (mig : migrator a (b :: c))
    : migrator a c :=
      fun ts t X => mig ts t (Member.MN b X).


    Section migrate.
      Variable tus : list (Tuvar Tsymbol).
      Variable pre : HList.hlist (fun tst : list (type Tsymbol) * type Tsymbol =>
                       HList.hlist (typeD TsymbolD) (fst tst) ->
                       typeD TsymbolD (snd tst)) tus.

      Fixpoint migrate_env {tus'} {struct tus'}
      : migrator tus tus' ->
        HList.hlist (fun tst : list (type Tsymbol) * type Tsymbol =>
                       HList.hlist (typeD TsymbolD) (fst tst) ->
                       typeD TsymbolD (snd tst)) tus' :=
        match tus' as tus'
              return migrator tus tus' ->
                     HList.hlist (fun tst : list (type Tsymbol) * type Tsymbol =>
                                    HList.hlist (typeD TsymbolD) (fst tst) ->
                                    typeD TsymbolD (snd tst)) tus'
        with
        | nil => fun _ => HList.Hnil
        | (ts,t) :: tus' => fun mig =>
          @HList.Hcons _ (fun tst : list (type Tsymbol) * type Tsymbol =>
                            HList.hlist (typeD TsymbolD) (fst tst) ->
                            typeD TsymbolD (snd tst))
                       (ts,t) _
                       (wtexprD EsymbolD (mig _ _ (Member.MZ _ _)) pre)
                       (@migrate_env _ (migrator_tl mig))
        end.

    End migrate.

    Definition logicT_spec (l : logicT) : Prop :=
      forall tus tvs prems goal inst result,
        l tus tvs prems inst goal = result ->
        mD _ (fun t =>
                let '(existT _ tus' (post, inst', trans)) := t in
                foralls_uvar_prop tus' (fun us' =>
                  InstD EsymbolD inst' us' ->
                  tyProp_to_Prop
                    (foralls_prop tvs (fun vs =>
                       impls_prop (List.map (fun p us' vs => wtexprD EsymbolD p (migrate_env _ us' trans) vs) prems)
                                  (fun us' vs =>
                                     impl_prop (@PostD _ _ post us' vs)
                                               (@PreD  _ _ goal  (migrate_env _ us' trans)  vs)) us' vs))))
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