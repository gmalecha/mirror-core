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
  Variable Esymbol_eq_dec : forall t (a b : Esymbol t), {a = b} + {a <> b}.

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
          * list (wtexpr Esymbol tus' tvs tyProp)
          * Inst Esymbol tus'
          * migrator Esymbol tus tus' }%type.

    Variable PreD
    : forall {tus tvs}, Pre tus tvs ->
                        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable PostD
    : forall {tus tvs}, Post tus tvs ->
                        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable mD : forall T (TD : T -> Prop), m T -> Prop.

    Variable tyProp_to_Prop : typeD TsymbolD tyProp -> Prop.
    Variable Prop_to_tyProp : Prop -> typeD TsymbolD tyProp.

    Definition logicT_spec (l : logicT) : Prop :=
      forall tus tvs prems goal inst result,
        l tus tvs prems inst goal = result ->
        mD (fun t =>
                let '(existT _ tus' (post, prems', inst', trans)) := t in
                Inst_evolves trans inst' inst /\
                @foralls_uvar_prop tus' (fun us' =>
                  let us := migrate_env EsymbolD trans us' in
                  InstD EsymbolD inst' us' ->
                  tyProp_to_Prop
                    (@foralls_prop tvs (fun vs =>
                       impl_prop (impls_prop (map (fun p => wtexprD EsymbolD p us' vs) prems')
                                             (@PostD _ _ post us' vs))
                                 (impls_prop (map (fun p => wtexprD EsymbolD p us vs) prems)
                                             (@PreD  _ _ goal us  vs))))))
           result.
  End logicT.

  Require Import MirrorCore.LambdaWt.Unify.

  Section assumption_tactic.
    Variable tyProp : type Tsymbol.
    Variable m : Type -> Type.
    Require Import ExtLib.Structures.Monads.
    Require Import ExtLib.Structures.Functor.
    Context {Monad_m : Monad m}.
    Context {MonadPlus_m : MonadPlus m}.
    Context {MonadZero_m : MonadZero m}.
    Context {Functor_m : Functor m}.

    Variable unify : Unifier Esymbol (Inst Esymbol).
    Variable unifyOk : UnifierOk (@Inst_lookup _ Esymbol) unify.

    Variable mD : forall T (TD : T -> Prop), m T -> Prop.
    Variable forall_prop : forall (T : Type),
        (T -> typeD TsymbolD tyProp) ->
        typeD TsymbolD tyProp.
    Variable impl_prop :
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp ->
        typeD TsymbolD tyProp.

    Variable tyProp_to_Prop : typeD TsymbolD tyProp -> Prop.
    Variable Prop_to_tyProp : Prop -> typeD TsymbolD tyProp.

    Hypothesis mD_mzero : forall T (P : T -> _), mD P mzero.
    Hypothesis mD_fmap : forall T U (f : T -> U) (P Q : _ -> Prop) x,
        (forall x, Q x -> P (f x)) ->
        mD Q x ->
        mD P (fmap f x).
    Hypothesis mD_mplus : forall T U (P : T -> Prop) (Q : U -> Prop)
                                 (x : m T) (y : m U),
        mD P x ->
        mD Q y ->
        mD (fun x => match x with
                     | inl x => P x
                     | inr x => Q x
                     end) (mplus x y).
    Hypothesis mD_bind : forall T U (P : T -> Prop) (Q : U -> Prop) c k,
        mD P c ->
        (forall x, P x -> mD Q (k x)) ->
        mD Q (bind c k).
    Hypothesis mD_ret : forall T (P : T -> Prop) x,
        P x -> mD P (ret x).

    Hypothesis mD_conseq : forall T (P Q : T -> Prop) x,
        mD Q x ->
        (forall x, Q x -> P x) ->
        mD P x.

    Theorem mD_mjoin : forall T (P : T -> Prop) x y,
        mD P x ->
        mD P y ->
        mD P (mjoin x y).
    Proof.
      unfold mjoin.
      intros. eapply mD_bind. eapply mD_mplus.
      eassumption. eassumption.
      simpl. destruct x0; eauto using mD_ret.
    Qed.

    Section find_premise.
      Context {tus : list (Tuvar Tsymbol)}.
      Context {tvs : list (type Tsymbol)}.
      Variables (gl : wtexpr Esymbol tus tvs tyProp)
                (s : Inst Esymbol tus).

      Fixpoint find_premise
               (prems : list (wtexpr Esymbol tus tvs tyProp))
      : m (Inst Esymbol tus) :=
        match prems with
        | nil => mzero
        | p :: ps =>
          match @unify _ _ _ gl p s
          with
          | None => find_premise ps
          | Some s' => mjoin (ret s') (find_premise ps)
          end
        end.

      Local Lemma find_premise_sound
      : forall prems,
          mD (fun inst' : Inst Esymbol tus =>
                let trans := migrator_id Esymbol tus in
                SubstWt.Inst_evolves trans inst' s /\
                foralls_uvar_prop
                  (fun
                      us : hlist
                             (fun tst : list (type Tsymbol) * type Tsymbol =>
                                hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                             tus =>
                      InstD EsymbolD inst' us ->
                      tyProp_to_Prop
                        (foralls_prop tyProp forall_prop
                                      (fun vs : hlist (typeD TsymbolD) tvs =>
                                         impls_prop tyProp impl_prop
                                                    (map
                                                       (fun p : wtexpr Esymbol tus tvs tyProp =>
                                                          wtexprD EsymbolD p us vs) prems)
                                                    (wtexprD EsymbolD gl us vs)))))
             (find_premise prems).
      Proof.
        induction prems.
        { eapply mD_mzero. }
        { simpl.
          lazymatch goal with
          | |- mD ?X _ =>
            assert (mD X (find_premise prems))
          end.
          { clear - IHprems. admit. }
          clear IHprems.
          destruct (unify gl a s) eqn:?; eauto.
          eapply mD_mjoin; eauto.
          { eapply mD_ret. simpl.
            admit. } }
      Admitted.

    End find_premise.

    Definition Assumption
    : logicT tyProp m
             (fun tus tvs => wtexpr Esymbol tus tvs tyProp)
             (fun _ _ => unit) :=
      fun tus tvs prems sub goal =>
        fmap (F:=m)
             (fun sub' => @existT _ _ tus (tt,prems,sub',migrator_id _ _))
             (find_premise goal sub prems).

    Theorem Assumption_sound
    : logicT_spec forall_prop impl_prop
                  (fun tus tvs e => wtexprD EsymbolD e)
                  (fun _ _ _ => Pure_exprT (Prop_to_tyProp True))
                  mD tyProp_to_Prop Assumption.
    Proof.
      red. unfold Assumption. intros.
      subst.
      eapply mD_fmap
      with (Q:=fun inst' =>
                 let trans := migrator_id _ _ in
                 SubstWt.Inst_evolves trans inst' inst /\
                 foralls_uvar_prop
                   (fun
                       us : hlist
                              (fun tst : list (type Tsymbol) * type Tsymbol =>
                                 hlist (typeD TsymbolD) (fst tst) ->
                                 typeD TsymbolD (snd tst)) tus =>
                       InstD EsymbolD inst' us ->
                       tyProp_to_Prop
                         (foralls_prop tyProp forall_prop
                                       (fun vs : hlist (typeD TsymbolD) tvs =>
                                          impls_prop tyProp impl_prop
                                                     (map
                                                        (fun p : wtexpr Esymbol tus tvs tyProp =>
                                                           wtexprD EsymbolD p us vs) prems)
                                                     (wtexprD EsymbolD goal us vs))))).
      { destruct 1.
        split; [ assumption | ].
        admit. }
      eapply find_premise_sound.
    Admitted.
  End assumption_tactic.

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