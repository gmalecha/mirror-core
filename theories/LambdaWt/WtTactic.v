Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Tactics.Tactics.
Require Import MirrorCore.LambdaWt.MLogic.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.SubstWt.
Require Import MirrorCore.LambdaWt.WtMigrator.
Require Import MirrorCore.LambdaWt.Unify.

Set Implicit Arguments.
Set Strict Implicit.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.
  Variable Esymbol_eq_dec : forall t (a b : Esymbol t), {a = b} + {a <> b}.

  (** TODO(gmalecha): Move **)
  Definition exprR tus tvs (T : Type) (R : T -> T -> Prop)
  : exprT TsymbolD tus tvs T -> exprT TsymbolD tus tvs T -> Prop :=
    fun v1 v2 =>
      forall us vs, R (v1 us vs) (v2 us vs).

  Definition wtRespectful {t u}
             (P : typeD TsymbolD t -> typeD TsymbolD t -> Prop)
             (Q : typeD TsymbolD u -> typeD TsymbolD u -> Prop)
  : typeD TsymbolD (TArr t u) -> typeD TsymbolD (TArr t u) -> Prop :=
    fun f g => forall x y, P x y -> Q (f x) (g y).

  Lemma exprR_Ap_exprT
  : forall tus tvs (T U : type Tsymbol) P Q
           (f g : exprT TsymbolD tus tvs (typeD TsymbolD (TArr T U)))
           (x y : exprT TsymbolD tus tvs (typeD TsymbolD T)),
      exprR (wtRespectful P Q) f g ->
      exprR P x y ->
      exprR Q (Ap_exprT f x) (Ap_exprT g y).
  Proof using.
    clear.
    unfold wtRespectful, Ap_exprT, exprR.
    intros; eauto.
  Defined.


  Context (Inst : list _ -> Type)
          {Inst_Inst : Instantiation TsymbolD Esymbol Inst}.

  Variable tyProp : type Tsymbol.
  Context {tyPropL : ILogicOps (typeD TsymbolD tyProp)}.
  Context {tyPropLo : ILogic (typeD TsymbolD tyProp)}.

  Section logicM.

    Fixpoint foralls_prop (ts : list (type Tsymbol))
    : (hlist (typeD TsymbolD) ts -> typeD TsymbolD tyProp) ->
      typeD TsymbolD tyProp :=
      match ts with
      | nil => fun k => k Hnil
      | t :: ts => fun k =>
        foralls_prop (fun vs =>
                        lforall (fun v => k (Hcons v vs)))
      end.

    Fixpoint foralls_uvar_prop (ts : list (Tuvar Tsymbol))
    : (hlist (fun tst => hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst)) ts -> Prop) ->
      Prop :=
      match ts with
      | nil => fun k => k Hnil
      | t :: ts => fun k =>
        foralls_uvar_prop (fun vs => forall v, k (Hcons v vs))
      end.

    Section impls.
      Context {tus : list (Tuvar Tsymbol)} {tvs : list (type Tsymbol)}.
      Fixpoint impls_prop (ts : list (typeD TsymbolD tyProp))
               (post : typeD TsymbolD tyProp)
      : typeD TsymbolD tyProp :=
        match ts with
        | nil => post
        | t :: ts =>
          limpl t (impls_prop ts post)
        end.
    End impls.

    Variable m : Type -> Type.

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

    Variables Pre Post : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.

    Record resultA tus resultUs tvs : Type := mkResultA
    { result         : Post resultUs tvs
    ; resultPrems    : list (wtexpr Esymbol resultUs tvs tyProp)
    ; resultSubst    : Inst resultUs
    ; resultMigrator : migrator Esymbol tus resultUs }.
    Arguments mkResultA {_ _ _} _ _ _ _ : clear implicits.

    Record resultC tus tvs : Type := mkResultC
    { resultUs       : _
    ; the_result     : resultA tus resultUs tvs }.
    Arguments mkResultC {_ _ _} _ : clear implicits.

    (** Statically known pre- and post-context
     **)
    Definition logicA tus tus' tvs : Type :=
      forall
        (prems : list (wtexpr Esymbol tus tvs tyProp))
        (inst  : Inst tus)
        (goal  : Pre tus tvs),
        m (resultA tus tus' tvs).

    (** Statically known pre- context
     **)
    Definition logicC tus tvs : Type :=
      forall
        (prems : list (wtexpr Esymbol tus tvs tyProp))
        (inst  : Inst tus)
        (goal  : Pre tus tvs),
        m (resultC tus tvs).

    (** NOTE: [logicT] does not form a monad due to the generalization
     **       over the indices.
     **)
    Definition logicM : Type :=
      forall tus tvs, logicC tus tvs.

    Variable PreD
    : forall {tus tvs}, Pre tus tvs ->
                        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
    Variable PostD
    : forall {tus tvs}, Post tus tvs ->
                        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

    Context {Functor_m : Functor m}.
    Context {FLogic_m : FLogic m}.

    Definition logicA_spec {tus tus' tvs} (c : logicA tus tus' tvs) : Prop :=
      forall prems goal inst result,
        c prems inst goal = result ->
        fmodels (fun t =>
              match t with
              | mkResultA post prems' inst' trans =>
                Inst_evolves trans inst inst' /\
                @foralls_uvar_prop tus' (fun us' =>
                  let us := migrate_env EsymbolD trans us' in
                  InstD inst' us' ->
                  lentails ltrue
                    (@foralls_prop tvs (fun vs =>
                       limpl (impls_prop
                                (map (fun p => wtexprD EsymbolD p us' vs) prems')
                                (@PostD _ _ post us' vs))
                             (impls_prop
                                (map (fun p => wtexprD EsymbolD p us vs) prems)
                                (@PreD  _ _ goal us  vs)))))
              end)
           result.

    Definition logicC_spec {tus tvs} (c : logicC tus tvs) : Prop :=
      forall prems goal inst result,
        c prems inst goal = result ->
        fmodels (fun t =>
              match t with
              | @mkResultC _ _ tus' (mkResultA post prems' inst' trans) =>
                Inst_evolves trans inst inst' /\
                @foralls_uvar_prop tus' (fun us' =>
                  let us := migrate_env EsymbolD trans us' in
                  InstD inst' us' ->
                  lentails ltrue
                    (@foralls_prop tvs (fun vs =>
                       limpl (impls_prop
                                (map (fun p => wtexprD EsymbolD p us' vs) prems')
                                (@PostD _ _ post us' vs))
                             (impls_prop
                                (map (fun p => wtexprD EsymbolD p us vs) prems)
                                (@PreD  _ _ goal us  vs)))))
              end)
           result.

    Definition logicM_spec (l : logicM) : Prop :=
      forall tus tvs,
        logicC_spec (l tus tvs).
  End logicM.


  Lemma foralls_uvar_prop_impl
    : forall ts (P Q : _ -> Prop),
      (forall xs, P xs -> Q xs) ->
      (@foralls_uvar_prop ts P -> @foralls_uvar_prop ts Q).
  Proof.
    clear.
    induction ts; simpl; intros; auto.
    eapply IHts; [| eassumption ].
    simpl. eauto.
  Qed.

  Lemma foralls_prop_impl : forall ts P Q,
      (forall xs, P xs |-- Q xs) ->
      @foralls_prop ts P |-- @foralls_prop ts Q.
  Proof.
    clear - tyPropLo.
    induction ts; simpl; eauto.
    intros.
    eapply IHts. intros.
    eapply lforallR. intros. eapply lforallL. eapply H.
  Qed.

  Lemma foralls_uvar_prop_sem
    : forall ts (P : _ -> Prop),
      (forall xs, P xs) ->
      (@foralls_uvar_prop ts P).
  Proof.
    clear.
    induction ts; simpl; intros; auto.
  Qed.

  Lemma foralls_prop_sem : forall ts Q,
      (forall xs, |-- Q xs) ->
      |-- @foralls_prop ts Q.
  Proof.
    clear - tyPropLo.
    induction ts; simpl; eauto.
    intros.
    eapply IHts. intros.
    eapply lforallR. intros. eauto.
  Qed.

  Lemma impls_prop_pure : forall A B,
      A |-- B ->
      forall Cs,
        A |-- impls_prop Cs B.
  Proof.
    induction Cs; simpl; intros; eauto.
    apply limplAdj.
    etransitivity; [ | eapply IHCs ].
    eapply landL1. reflexivity.
  Qed.

  Lemma wtexpr_equiv_Unifiable_eq
  : forall tus tvs t (e1 e2 : wtexpr Esymbol tus tvs t)
           (i : Inst tus),
      wtexpr_equiv (Unifiable_eq i) e1 e2 ->
      forall (xs : Uenv TsymbolD tus)
             (vs : Venv TsymbolD tvs),
        InstD i xs ->
        wtexprD EsymbolD e1 xs vs = wtexprD EsymbolD e2 xs vs.
  Proof.
    induction 1; intros; try solve [ eauto | eapply H; eapply H0 ].
    { simpl.
      unfold Ap_exprT.
      rewrite IHwtexpr_equiv1; eauto.
      rewrite IHwtexpr_equiv2; eauto. }
    { simpl. unfold Abs_exprT.
      eapply FunctionalExtensionality.functional_extensionality; eauto. }
    { simpl. unfold UVar_exprT.
      repeat rewrite hlist_map_hlist_map.
      f_equal.
      clear - H0 H.
      induction H; simpl; auto.
      f_equal; eauto. }
    { destruct pf.
      { inversion H0; clear H0; subst.
        (** TODO(gmalecha): This should be provable *)
        admit. }
      { inversion H0; clear H0; subst.
        (** TODO(gmalecha): This should be provable *)
        admit. } }
    { etransitivity;
      [ eapply IHwtexpr_equiv1 | eapply IHwtexpr_equiv2 ]; eauto. }
  Admitted.

  Section evar_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.

    Variable unify : Unifier Esymbol Inst.
    Variable unifyOk : UnifierOk unify.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.


    Definition migrator_fresh t tus
    : migrator Esymbol tus (tus ++ t :: nil).
      eapply WtMigrator.migrator_id'. simpl.
      intros. eapply wtUVar.
      eapply DepUtil.member_lift with (ls'':=tus) (ls:=nil) (ls':=t::nil).
      rewrite (app_nil_r_trans tus). eassumption.
      eapply WtMigrator.vars_id.
    Defined.

    Definition Inst_fresh t {tus} (i : Inst tus)
    : Inst (tus ++ t :: nil).
    Admitted.

    Variables Pre Post : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.
    Variable Pre_Post_migrate
      : forall tus t tvs, Pre tus tvs -> Post (tus ++ t :: nil) tvs.

    Definition Evar {tus tvs} t
    : logicA m Pre Post tus (tus ++ t :: nil) tvs :=
      fun prems sub goal =>
        let mig := migrator_fresh t tus in
        ret {| result := Pre_Post_migrate t goal
             ; resultPrems := map (migrate_expr mig) prems
             ; resultSubst := Inst_fresh t sub
             ; resultMigrator := mig |}.
  End evar_tactic.

  Section under_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.
    Context {MonadZero_m : MonadZero m}.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.
    Context {MLogicZero_m : MLogicZero m}.

    Context {Post : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type}.
    Definition Under_All {tus tvs}
               (tac : forall t, logicC m wtgoal Post tus (t :: tvs))
    : logicC m wtgoal Post tus tvs.
    refine (
        fun prems sub goal =>
          match goal with
          | @wtAll _ _ t goal' =>
            (** TODO(gmalecha): This is going to be too expensive.
             ** 1/ Combine prems and quantifiers into a context.
             ** 2/ Might not want to eagerly instantiate premises
             **)
            fmap _ (tac t _ sub goal')
          | _ => mzero
          end).
    admit. admit.
    Admitted.
  End under_tactic.


  Section assumption_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MonadPlus_m : MonadPlus m}.
    Context {MonadZero_m : MonadZero m}.
    Context {Functor_m : Functor m}.

    Variable unify : Unifier Esymbol Inst.
    Variable unifyOk : UnifierOk unify.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.
    Context {MLogicPlus_m : MLogicPlus m}.
    Context {MLogicZero_m : MLogicZero m}.

    Section find_premise.
      Context {tus : list (Tuvar Tsymbol)}.
      Context {tvs : list (type Tsymbol)}.
      Variables (gl : wtexpr Esymbol tus tvs tyProp)
                (s : Inst tus).

      Fixpoint find_premise
               (prems : list (wtexpr Esymbol tus tvs tyProp))
      : m (Inst tus) :=
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
          fmodels (fun inst' : Inst tus =>
                let trans := migrator_id in
                SubstWt.Inst_evolves trans s inst' /\
                foralls_uvar_prop
                  (fun
                      us : hlist
                             (fun tst : list (type Tsymbol) * type Tsymbol =>
                                hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                             tus =>
                      InstD inst' us ->
                      lentails ltrue
                        (foralls_prop
                                      (fun vs : hlist (typeD TsymbolD) tvs =>
                                         impls_prop
                                                    (map
                                                       (fun p : wtexpr Esymbol tus tvs tyProp =>
                                                          wtexprD EsymbolD p us vs) prems)
                                                    (wtexprD EsymbolD gl us vs)))))
             (find_premise prems).
      Proof.
        induction prems.
        { eapply fmodels_mzero. }
        { simpl.
          lazymatch goal with
          | |- fmodels ?X _ =>
            assert (fmodels X (find_premise prems))
          end.
          { eapply fmodels_conseq; [ eassumption | ].
            simpl. destruct 1; split; auto.
            revert H0.
            eapply foralls_uvar_prop_impl.
            intros.
            etransitivity; [ eapply H0; eassumption | ].
            eapply foralls_prop_impl; intros.
            eapply limplAdj. eapply landL1. reflexivity. }
          clear IHprems.
          destruct (unify gl a s) eqn:?; eauto.
          eapply fmodels_mjoin; [ | solve [ eauto ] ].
          clear H.
          eapply fmodels_ret.
          eapply unifyOk in Heqo.
          destruct Heqo; split; [ eassumption | ].
          eapply foralls_uvar_prop_sem. intros.
          eapply foralls_prop_sem; intros.
          eapply limplAdj.
          eapply impls_prop_pure.
          eapply landL2.
          erewrite <- wtexpr_equiv_Unifiable_eq; eauto.
          { reflexivity. } }
      Qed.

    End find_premise.


    Lemma impls_prop_ap
      : forall P Q prems G,
        G |-- impls_prop prems (P -->> Q) ->
        G |-- impls_prop prems P -->> impls_prop prems Q.
    Proof.
      induction prems; simpl; auto.
      intros.
      charge_intros.
      charge_eapply (IHprems (G //\\ a)).
      charge_split.
      { charge_tauto. }
      { charge_tauto. }
      Unshelve.
      charge_tauto.
    Qed.


    Definition Assumption
    : logicM m
             (fun tus tvs => wtexpr Esymbol tus tvs tyProp)
             (fun _ _ => unit) :=
      fun tus tvs prems sub goal =>
        fmap (F:=m)
             (fun sub' => mkResultC (mkResultA (fun _ _ => unit) tt prems sub' migrator_id))
             (find_premise goal sub prems).

    Theorem Assumption_sound
    : logicM_spec (fun tus tvs e => wtexprD EsymbolD e)
                  (fun _ _ _ => Pure_exprT ltrue)
                  Assumption.
    Proof.
      red. red. unfold Assumption. intros.
      subst.
      eapply fmodels_fmap; [ | eapply find_premise_sound ].
      { destruct 1.
        split; [ assumption | ].
        revert H0.
        eapply foralls_uvar_prop_impl; intros.
        rewrite H0; eauto; clear H0.
        eapply foralls_prop_impl; intros.
        rewrite migrate_env_migrator_id.
        eapply impls_prop_ap.
        charge_revert.
        eapply impls_prop_ap.
        eapply impls_prop_pure.
        charge_tauto. }
    Qed.
  End assumption_tactic.

  Section apply_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {MonadZero_m : MonadZero m}.
    Context {Functor_m : Functor m}.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.
    Context {MLogicZero_m : MLogicZero m}.

    Variable unify : Unifier Esymbol Inst.
    Variable unifyOk : UnifierOk unify.

    Section lemma.
      Variable C : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.
      Variable CD : forall {tus tvs},
          C tus tvs -> exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

      Record lemma tus tvs : Type :=
      { vars  : list (type Tsymbol)
      ; prems : list (wtexpr Esymbol tus (vars ++ tvs) tyProp)
      ; concl : C tus (vars ++ tvs)
      }.

      Definition lemmaD {tus tvs} (l : lemma tus tvs)
      : exprT TsymbolD tus tvs (typeD TsymbolD tyProp) :=
        fun us vs =>
          foralls_prop
            (fun vs' : Venv TsymbolD l.(vars) =>
               impls_prop
                 (map (fun e => wtexprD EsymbolD e us (hlist_app vs' vs))
                      l.(prems))
                 (CD l.(concl) us (hlist_app vs' vs))).
    End lemma.
(*
    Definition EApply {tus tvs}
               (lem : lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp) tus tvs)
    : logicC m
             (fun tus tvs => wtexpr Esymbol tus tvs tyProp)
             (fun tus tvs => wtgoal tus tvs)%type
             tus tvs.
    refine (
      fun prems sub goal =>
        match unify goal lem.(concl) sub with
        | None => mzero
        | Some sub' => _
        end).
*)

  End apply_tactic.

  Section cut_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.

    Definition Cut {tus tvs} (t : wtexpr Esymbol tus tvs tyProp)
    : logicC m
             (fun tus tvs => wtexpr Esymbol tus tvs tyProp)
             (fun tus tvs => wtgoal tus tvs)%type
             tus tvs :=
      fun prems sub goal =>
        ret (m:=m) (mkResultC
                      (mkResultA wtgoal
                                 (wtConj (wtGoal t) (wtHyp t (wtGoal goal)))
                                 prems
                                 sub
                                 migrator_id)).

    Existing Instance Reflexive_Inst_evolves.

    Theorem Cut_sound
    : forall tus tvs t,
        logicC_spec (fun tus tvs e => wtexprD EsymbolD e)
                    (fun _ _ e => @wtgoalD _ _ e)
                    (@Cut tus tvs t).
    Proof.
      unfold Cut. red. simpl; intros. subst.
      eapply fmodels_ret.
      split; [ reflexivity | ].
      { simpl.
        eapply foralls_uvar_prop_sem; intros.
        eapply foralls_prop_sem; intros.
        rewrite migrate_env_migrator_id.
        eapply impls_prop_ap.
        eapply impls_prop_pure.
        charge_tauto. }
    Qed.

  End cut_tactic.

End simple_dep_types.





(*
    Definition logicM_cps (Pre Post : _ -> _ -> Type) : Type :=
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