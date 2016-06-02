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
Require Import MirrorCore.LambdaWt.WtCtx.

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

  Section hlist_maps.
    Context {T U : Type} (f : T -> U) (F : U -> Type).

    Fixpoint hlist_to_hlist_map ls (hs : hlist (fun x => F (f x)) ls)
    : hlist F (map f ls) :=
      match hs in hlist _ ls
            return hlist F (map f ls)
      with
      | Hnil => Hnil
      | @Hcons _ _ x xs h hs =>
        @Hcons _ _ (f x) (map f xs) h (@hlist_to_hlist_map _ hs)
      end.
  End hlist_maps.

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

    Arguments wtctx [_] _ _ _ _.

    (** TODO(gmalecha):
     **  I need to figure out how contexts should play into this.
     **  - Should [tus] and [tvs] be computed from the context, or should
     **    the type of contexts be dependent on them?
     **)
    Record resultA tus resultUs T : Type := mkResultA
    { result         : T (*
      (** The only reason to return this is to avoid duplicate work
       ** when doing migration.
       **)
    ; resultPrems    : wtctx Esymbol tyProp resultUs tvs *)
    ; resultSubst    : Inst resultUs
    ; resultMigrator : migrator Esymbol tus resultUs }.
    Arguments mkResultA {_ _ _} _ _ _ : clear implicits.

    Record resultC tus T : Type := mkResultC
    { resultUs       : _
    ; the_result     : resultA tus resultUs T }.
    Arguments mkResultC {_ _} _ _ : clear implicits.

    (** Statically known pre- and post-context
     **)
    Definition InCtxA tus tus' tvs (T : Type) : Type :=
      forall (sub : Inst tus) (ctx : wtctx Esymbol tyProp tus tvs),
        m (resultA tus tus' T).

    (** Statically known pre- context
     **)
    Definition InCtxC tus tvs (T : Type) : Type :=
      forall (sub : Inst tus) (ctx : wtctx Esymbol tyProp tus tvs),
        m (resultC tus T).

    (* (** NOTE: [logicT] does not form a monad due to the generalization *)
    (*  **       over the indices. *)
    (*  **) *)
    (* Definition logicM : Type := *)
    (*   forall tus tvs, logicC tus tvs. *)

    (* Variable PreD *)
    (* : forall {tus tvs}, Pre tus tvs -> *)
    (*                     exprT TsymbolD tus tvs (typeD TsymbolD tyProp). *)
    (* Variable PostD *)
    (* : forall {tus tvs}, Post tus tvs -> *)
    (*                     exprT TsymbolD tus tvs (typeD TsymbolD tyProp). *)

    Context {Functor_m : Functor m}.
    Context {FLogic_m : FLogic m}.

    Arguments wtctxD [_ _ _] _ _ {_} [_ _] _ _ _ _.

    Global Instance ILogicOps_exprT T (ILo : ILogicOps T) tus tvs
    : ILogicOps (exprT TsymbolD tus tvs T) :=
    { lentails := fun P Q => forall us vs, P us vs |-- Q us vs
    ; ltrue    := fun _ _ => ltrue
    ; lfalse   := fun _ _ => lfalse
    ; land     := fun P Q us vs => P us vs //\\ Q us vs
    ; lor      := fun P Q us vs => P us vs \\// Q us vs
    ; limpl    := fun P Q us vs => P us vs -->> Q us vs
    ; lforall  := fun T P us vs => lforall (fun x => P x us vs)
    ; lexists  := fun T P us vs => lexists (fun x => P x us vs)
    }.
    Global Instance ILogic_exprT T (ILo : ILogicOps T) (IL : ILogic T) tus tvs
    : ILogic (exprT TsymbolD tus tvs T).
    Proof using.
      clear - IL.
      constructor; try red; simpl; intros.
      { constructor.
        { red. reflexivity. }
        { red. intros. etransitivity; [ eapply H | eapply H0 ]. } }
      { eapply ltrueR. }
      { eapply lfalseL. }
      { eapply lforallL; eapply H. }
      { eapply lforallR. intros. eapply H. }
      { eapply lexistsL. eauto. }
      { eapply lexistsR. eapply H. }
      { eapply landL1; eapply H. }
      { eapply landL2; eapply H. }
      { eapply lorR1; eapply H. }
      { eapply lorR2; eapply H. }
      { eapply landR; [ eapply H | eapply H0 ]. }
      { eapply lorL; [ eapply H | eapply H0 ]. }
      { eapply landAdj. apply H. }
      { eapply limplAdj. apply H. }
    Defined.

    Require Import ChargeCore.Logics.ILEmbed.
    Global Instance EmbedOp_Prop_tyProp : EmbedOp Prop (typeD TsymbolD tyProp).
    Admitted.
    Global Instance Embed_Prop_tyProp : Embed Prop (typeD TsymbolD tyProp).
    Admitted.
    Global Instance EmbedOp_UProp_tyProp {tus tvs}
    : EmbedOp (Uenv TsymbolD tus -> Prop)
              (exprT TsymbolD tus tvs (typeD TsymbolD tyProp)) :=
    { embed := fun P us _ => embed (P us) }.
(*
    Global Instance Embed_UProp_tyProp {tus tvs}
    : Embed (Uenv TsymbolD tus -> Prop)
            (exprT TsymbolD tus tvs (typeD TsymbolD tyProp)).
    { embed := fun P us _ => embed (P us) }.
*)

    (** This basically says that the second is equal to the migration of the
     ** first. It is only important if I have delayed migration of contexts.
     **)
    Axiom wtctx_migrates : forall {tus tus' tvs}, migrator Esymbol tus tus' ->
        wtctx Esymbol tyProp tus tvs -> wtctx Esymbol tyProp tus' tvs -> Prop.

    Arguments WtMigrator.vars_id {_ _ _ _}.
    Arguments wtgoal_subst {_ _ _ _ _} _ [_ _] _ _.

    (** This is an eager migration function **)
    Fixpoint migrate_wtctx {tus tus' tvs} (mig : migrator Esymbol tus tus')
             (ctx : wtctx Esymbol tyProp tus tvs)
    : wtctx Esymbol tyProp tus' tvs :=
      match ctx in wtctx _ _ _ tvs return wtctx Esymbol tyProp tus' tvs with
      | ctx_Top => ctx_Top
      | ctx_All t c => ctx_All t (migrate_wtctx mig c)
      | ctx_Hyp P c => ctx_Hyp (migrate_expr mig P) (migrate_wtctx mig c)
(*
      | ctx_Left G c =>
        ctx_Left (wtgoal_subst mig WtMigrator.vars_id G)
                 (migrate_wtctx mig c)
      | ctx_Right G c =>
        ctx_Right (wtgoal_subst mig WtMigrator.vars_id G)
                  (migrate_wtctx mig c)
*)
      end.

    Definition InCtxA_spec {tus tus' tvs T} (c : InCtxA tus tus' tvs T)
               (TD : T -> exprT TsymbolD tus' tvs (typeD TsymbolD tyProp))
    : Prop :=
      forall sub ctx,
        fmodels (fun t =>
                   match t with
                   | mkResultA val sub' mig =>
                     let ctx' := migrate_wtctx mig ctx in
                     Inst_evolves mig sub sub' /\
(*                     wtctx_migrates mig ctx ctx' /\ *)
                         (embed (InstD sub'))
                     |-- (wtctxD EsymbolD tyProp ctx'
                                 (fun us vs => TD val us vs))
                   end)
                (c sub ctx).

    Context {Monad_m : Monad m}.

    Global Instance Monad_WtInCtx {tus tvs} : Monad (InCtxA tus tus tvs) :=
    { ret := fun T val sub ctx => ret {| result := val
                                       ; resultSubst := sub
                                       ; resultMigrator := migrator_id |}
    ; bind := fun _ _ c k sub ctx =>
                bind (c sub ctx)
                     (fun val =>
                        match val with
                        | mkResultA val sub' mig =>
                          k val sub' (migrate_wtctx mig ctx)
                        end)
    }.
    Global Instance Functor_WtInCtx {tus tus' tvs} : Functor (InCtxA tus tus' tvs) :=
    { fmap := fun T U f x sub ctx =>
                fmap (fun val =>
                        match val with
                        | mkResultA val sub mig =>
                          mkResultA (f val) sub mig
                        end) (x sub ctx) }.

    Context {MLogic_m : MLogic m}.

(*
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
*)
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


  Section evar_tactic.
    Context {m : Type -> Type}.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.
    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.

    Variables Pre Post Post'
    : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.
    Variable Pre_migrate
    : forall tus t tvs, migrator Esymbol tus (tus ++ t :: nil) ->
                        Pre tus tvs -> Pre (tus ++ t :: nil) tvs.

    Arguments DepUtil.member_weaken {_} [_] _ [_] _.

    Definition Evar {tus tvs} t
    : InCtxA m tus (tus ++ t :: nil) tvs (member t (tus ++ t :: nil)) :=
      fun sub _ =>
        let mig := migrator_fresh t tus in
        ret {| result := DepUtil.member_weaken tus (MZ _ _)
(*             ; resultPrems := map (migrate_expr mig) prems *)
             ; resultSubst := Inst_fresh t sub
             ; resultMigrator := mig |}.

(*
    Fixpoint build_evars T (tus' : list (Tuvar Tsymbol)) (k : forall t X, member t X -> T X t) {struct tus'}
    : hlist (T tus') tus' :=
      match tus' as tus'
            return hlist (T tus') tus'
      with
      | nil => Hnil
      | t :: tus' =>
        Hcons (k _ _ (MZ _ _))
              (build_evars (fun X t' => T (t :: X) t') tus' (fun _ _ m => k _ _ (MN _ m)))
      end.
*)

    Definition InCtxA_pure {tus tvs} {T : Type} (x : T)
    : InCtxA m tus tus tvs T :=
      fun sub _ =>
        ret {| result      := x
             ; resultSubst := sub
             ; resultMigrator := migrator_id |}.

    Definition InCtxA_bind {tus tus' tus'' tvs} {T U}
               (x : InCtxA m tus tus' tvs T)
               (k : T -> InCtxA m tus' tus'' tvs U)
    : InCtxA m tus tus'' tvs U :=
      fun sub ctx =>
        bind (x sub ctx)
             (fun x =>
                let ctx' := migrate_wtctx x.(resultMigrator) ctx in
                bind (k x.(result) x.(resultSubst) ctx')
                     (fun r =>
                        ret {| result := r.(result)
                             ; resultSubst := r.(resultSubst)
                             ; resultMigrator := migrator_compose x.(resultMigrator) r.(resultMigrator) |})).

    (** This is really inefficient due to all of the casting *)
    Fixpoint Evars {tus tvs} tus'
    : InCtxA m tus (tus ++ tus') tvs (hlist (fun t => member t (tus ++ tus')) tus') :=
      match tus' as tus'
            return InCtxA m tus (tus ++ tus') tvs (hlist (fun t => member t (tus ++ tus')) tus')
      with
      | nil =>
        match eq_sym (app_nil_r_trans tus) in _ = X
              return InCtxA m tus X tvs (hlist (fun t => member t X) nil)
        with
        | eq_refl => InCtxA_pure Hnil
        end
      | t :: tus' =>
        InCtxA_bind (Evar t)
                    (fun u =>
                       match app_ass_trans tus (t :: nil) tus' in _ = X
                             return InCtxA m (tus ++ t :: nil) X tvs (hlist (fun t0 : Tuvar Tsymbol => member t0 X) (t :: tus'))
                       with
                       | eq_refl =>
                         fmap (fun us =>
                                 Hcons match app_nil_r_trans tus' in _ = Y
                                             return member t (_ ++ Y)
                                       with
                                       | eq_refl => @DepUtil.member_lift _ t nil tus' (tus ++ t :: nil)
                                                                         (match app_nil_r_trans (tus ++ t :: nil) in _ = X
                                                                                return member t X -> member t _
                                                                          with
                                                                          | eq_refl => fun x => x
                                                                          end u)
                                       end us) (Evars tus')
                              end)
      end.

  End evar_tactic.

  Require Import MirrorCore.LambdaWt.Unify.

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
      ; premises : list (wtexpr Esymbol tus (vars ++ tvs) tyProp)
      ; concl : C tus (vars ++ tvs)
      }.

      Definition lemmaD {tus tvs} (l : lemma tus tvs)
      : exprT TsymbolD tus tvs (typeD TsymbolD tyProp) :=
        fun us vs =>
          foralls_prop
            (fun vs' : Venv TsymbolD l.(vars) =>
               impls_prop
                 (map (fun e => wtexprD EsymbolD e us (hlist_app vs' vs))
                      l.(premises))
                 (CD l.(concl) us (hlist_app vs' vs))).

      Definition lift_lemma {tus tvs} {tus'} tvs'
                 (mig : migrator Esymbol tus tus')
                 (lem : lemma tus tvs)
      : lemma tus' (tvs' ++ tvs).
      Proof using.
      Admitted.

      Global Instance Migrate_lemma : Migrate Esymbol lemma.
      Admitted.
    End lemma.

    Arguments lift_lemma {_ _ _ _} _ _ _.
    About Evars.
    Arguments Evars {_ _ _} [_ _] _ _ _.
    Arguments migrate_expr {_ _} [_ _] _ [_ _] _.

    (** Soundness of unification should be justified once! *)
    Definition Unify {tus tvs t}
               (e1 e2 : wtexpr Esymbol tus tvs t)
    : InCtxA m tus tus tvs bool :=
      fun sub ctx =>
        match unify e1 e2 sub
              return m (resultA tus tus bool)
        with
        | None =>
          ret (m:=m)
              {| result := false
               ; resultSubst := sub
               ; resultMigrator := migrator_id
               |}
        | Some sub' =>
          ret {| result := true
               ; resultSubst := sub'
               ; resultMigrator := migrator_id
               |}
        end.

    (** TODO(gmalecha): move this to WtMigrator *)
    Definition migrator_pure {tus}
    : migrator Esymbol nil tus := Hnil.

    Definition inj_lemma {tus tvs}
               (lem : lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp) nil nil)
    : InCtxA m tus tus tvs (lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp) tus tvs) :=
      InCtxA_pure (
               match app_nil_r_trans tvs in _ = X return lemma _ _ X with
               | eq_refl => lift_lemma tvs (@migrator_pure tus) lem
               end).

    Arguments WtMigrator.vars_id {_ _ _ _}.

    Definition InCtxA_listen_migrator {tus tus' tvs T}
               (c : InCtxA m tus tus' tvs T)
    : InCtxA m tus tus' tvs (T * migrator Esymbol tus tus') :=
      fun sub ctx =>
        bind (c sub ctx)
             (fun x => ret {| result := (x.(result), x.(resultMigrator))
                            ; resultSubst := x.(resultSubst)
                            ; resultMigrator := x.(resultMigrator) |}).

    Require Import ExtLib.Data.List.
    Instance MonadZero_InCtxA {tus tus' tvs}
    : MonadZero (InCtxA m tus tus' tvs) :=
    {| mzero := fun _ _ _ => mzero |}.

    Section hlist_strong_map.
      Context {T U : Type} {f : T -> U} {F : T -> Type} {G : U -> Type}
              (FG : forall x, G (f x) -> F x).
      Fixpoint hlist_strong_map {ls}
      : hlist G (map f ls) -> hlist F ls :=
        match ls as ls return hlist G (map f ls) -> hlist F ls with
        | nil => fun _ => Hnil
        | l :: ls => fun h => Hcons (FG (hlist_hd h)) (hlist_strong_map (hlist_tl h))
        end.
    End hlist_strong_map.

    Definition EApply {tus tvs}
               (lem : lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp)
                            tus tvs)
               (gl : wtexpr Esymbol tus tvs tyProp)
    : InCtxA m tus (tus ++ List.map (fun t => (tvs,t)) lem.(vars)) tvs
             (list (wtexpr Esymbol (tus ++ List.map (fun t => (tvs,t)) lem.(vars)) tvs tyProp)).
    refine
      (let vs := List.map (fun t => (tvs,t)) lem.(vars) in
       InCtxA_bind (InCtxA_listen_migrator (Evars vs))
                   (fun us =>
                      let x : migrator Esymbol tus (tus ++ vs) := snd us in
                      let new_us : hlist (wtexpr Esymbol (tus ++ vs) tvs) (vars lem) :=
                          hlist_strong_map (fun _ X => wtUVar X WtMigrator.vars_id)
                                           (fst us)
                      in
                      let lem_migrator : forall t, wtexpr Esymbol tus (lem.(vars) ++ tvs) t ->
                                                   wtexpr Esymbol (tus ++ vs) tvs t
                          := (* subst (hlist_app new_us WtMigrator.vars_id) gl' *)
                          (* migrate_expr x lem.(concl) *) _
                      in
                      InCtxA_bind (Unify (migrate_expr x gl) (lem_migrator _ lem.(concl)))
                                  (fun x => if x then
                                              ret (fmap (lem_migrator tyProp) lem.(premises))
                                            else mzero))).
    intros.
    generalize (migrate_expr x X).
    eapply subst.
    eapply hlist_app.
    2: eapply WtMigrator.vars_id.
    eapply new_us.
    Defined.

  End apply_tactic.

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

    Fixpoint member_lower {T : Type} {t : T} {ts ts'} : member t (ts' ++ ts) -> option (member t ts) :=
      match ts' as ts'
            return member t (ts' ++ ts) -> option (member t ts)
      with
      | nil => Some
      | t' :: ts' => fun m =>
                       match m in member _ TS
                             return (member t (tl TS) -> option (member t ts)) -> option (member t ts)
                       with
                       | MZ _ _ => fun _ => None
                       | MN _ m => fun f => f m
                       end (fun m => @member_lower T t ts ts' m)
      end.

    Fixpoint member_skip {T : Type} {t : T} {ts ts' ts''} (f : member t ts -> option (member t ts''))
             {struct ts'}
    : member t (ts' ++ ts) -> option (member t (ts' ++ ts'')).
    refine
      match ts' as ts'
            return member t (ts' ++ ts) -> option (member t (ts' ++ ts''))
      with
      | nil => f
      | t' :: ts' => fun m =>
        match m in member _ (T :: TS)
              return T = t' -> (member t TS -> option (member t (ts' ++ ts''))) -> _
        with
        | MZ _ _ => fun pf _ => Some (MZ _ _)
        | MN _ m => fun pf f => fmap (@MN _ _ _ _) (f m)
        end eq_refl (fun m => member_skip _ _ _ _ _ f m)
      end.
    Defined.

    Fixpoint wtexpr_lower {tus} tvs tvs' tvs'' t (e : wtexpr Esymbol tus (tvs'' ++ tvs' ++ tvs) t)
    : option (wtexpr Esymbol tus (tvs'' ++ tvs) t).
    refine
      (match e in wtexpr _ _ _ t
             return option (wtexpr Esymbol tus (tvs'' ++ tvs) t)
       with
       | wtVar m => fmap (@wtVar _ _ _ _ _) (member_skip (ts':= tvs'') (member_lower) m)
       | wtApp f x => match wtexpr_lower tus tvs tvs' tvs'' _ f
                          , wtexpr_lower tus tvs tvs' tvs'' _ x
                      with
                      | Some f' , Some x' => Some (wtApp f' x')
                      | _ , _ => None
                      end
       | wtInj x => Some (wtInj x)
       | wtAbs e => fmap (@wtAbs _ _ _ _ _ _) (wtexpr_lower tus tvs tvs' (_ :: tvs'') _ e)
       | wtUVar u es =>
         fmap (wtUVar u) _
       end).
    admit.
    Admitted.

    Section find_premise_ctx.
      Context {tus : list (Tuvar Tsymbol)}.
      Variables (s : Inst tus).


      Fixpoint find_premise_ctx {tvs tvs'}
               (ctx : wtctx _ Esymbol tyProp tus tvs)
      : wtexpr Esymbol tus (tvs' ++ tvs) tyProp -> m (Inst tus) :=
        match ctx in wtctx _ _ _ _ tvs
               return wtexpr Esymbol tus (tvs' ++ tvs) tyProp -> m (Inst tus)
         with
         | ctx_Top => fun _ => mzero
         | ctx_All t ctx' => fun x =>
           @find_premise_ctx _ (tvs' ++ t::nil) ctx'
                             match eq_sym (app_ass_trans tvs' (t::nil) _) in _ = X
                                   return wtexpr Esymbol tus X tyProp
                             with
                             | eq_refl => x
                             end
         | ctx_Hyp P ctx' => fun gl =>
           match @wtexpr_lower _ _ _ nil _ gl with
           | None => mzero
           | Some gl' =>
             match unify P gl' s with
             | None => @find_premise_ctx _ nil ctx' gl'
             | Some s' => ret s'
             end
           end
(*
         | ctx_Left _ ctx' => fun x => find_premise_ctx ctx' x
         | ctx_Right _ ctx' => fun x => find_premise_ctx ctx' x
*)
         end.

      Arguments wtctxD {_ _ _} _ _ {_} [_ _] _ _ _ _ : clear implicits.

      Local Lemma find_premise_ctx_sound {tvs}
      : forall ctx tvs' gl,
          fmodels (fun inst' : Inst tus =>
                let trans := migrator_id in
                Inst_evolves trans s inst' /\
                foralls_uvar_prop
                  (fun
                      us : hlist
                             (fun tst : list (type Tsymbol) * type Tsymbol =>
                                hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                             tus =>
                      InstD inst' us ->
                      lentails ltrue
                               (wtctxD EsymbolD tyProp ctx
                                       (fun us vs => lforall (fun vs' => wtexprD EsymbolD gl us (hlist_app vs' vs)))
                                       us Hnil)))
             (@find_premise_ctx tvs tvs' ctx gl).
      Proof.
        induction ctx; simpl; intros.
        { eapply fmodels_mzero. }
        { lazymatch goal with
          | |- fmodels _ (find_premise_ctx _ ?X) =>
            generalize (IHctx (tvs' ++ t :: nil) X); clear IHctx
          end.
          eapply fmodels_conseq; simpl; intros.
          destruct H; split; [ assumption | ].
          revert H0.
          eapply foralls_uvar_prop_impl; intros.
          rewrite (H0 H1).
          clear H0 H1.
          admit. }
        { Require Import ExtLib.Tactics.
          consider (wtexpr_lower ts tvs' nil gl).
          { admit. }
          { intros. eapply fmodels_mzero. } }
(*
        { generalize (IHctx _ gl).
          eapply fmodels_conseq; simpl; intros.
          destruct H; split; [ eassumption | ].
          revert H0.
          eapply foralls_uvar_prop_impl; intros.
          specialize (H0 H1).
          rewrite H0.
          admit. }
        { generalize (IHctx _ gl).
          eapply fmodels_conseq; simpl; intros.
          destruct H; split; [ eassumption | ].
          revert H0.
          eapply foralls_uvar_prop_impl; intros.
          specialize (H0 H1).
          rewrite H0.
          admit. }
*)
      Admitted.

    End find_premise_ctx.

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
          match @unify _ _ _ gl p s with
          | None => find_premise ps
          | Some s' => mjoin (ret s') (find_premise ps)
          end
        end.

      Local Lemma find_premise_sound
      : forall prems,
          fmodels (fun inst' : Inst tus =>
                let trans := migrator_id in
                Inst_evolves trans s inst' /\
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
          { revert IHprems; eapply fmodels_conseq.
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

    Definition Assumption {tus tvs}
               (gl : wtexpr Esymbol tus tvs tyProp)
    : InCtxA m tus tus tvs unit :=
      fun sub ctx =>
        fmap (F:=m)
             (fun sub' => mkResultA tt sub' migrator_id)
             (find_premise_ctx sub (tvs':=nil) ctx gl).

    Theorem foralls_uvar_prop_sem'
      : forall (ts : list (Tuvar Tsymbol))
               (P : hlist
                      (fun tst : list (type Tsymbol) * type Tsymbol =>
                         hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                      ts -> Prop),
        foralls_uvar_prop P ->
        (forall
            xs : hlist
                   (fun tst : list (type Tsymbol) * type Tsymbol =>
                      hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                   ts, P xs).
    Proof.
      induction ts; simpl.
      { intros. rewrite (hlist_eta xs). apply H. }
      { intros. rewrite (hlist_eta xs).
        eapply IHts in H. eapply H. }
    Qed.

    Theorem Assumption_sound {tus tvs} gl
    : InCtxA_spec (@Assumption tus tvs gl)
                  (fun _ => wtexprD EsymbolD gl).
    Proof.
      red. unfold Assumption. intros.
      eapply fmodels_fmap; [ | eapply find_premise_ctx_sound ].
      { destruct 1.
        split; [ assumption | ].
        red. simpl.
        intros.
        eapply foralls_uvar_prop_sem' in H0.
        revert H0. instantiate (1 := us).
        intros.
        rewrite (hlist_eta vs).
        rewrite <- embedPropExists'.
        eapply lexistsL.
        intro.
        rewrite H0; eauto.
        admit. }
    Admitted.
  End assumption_tactic.

  Section cut_tactic.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.

    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.

    Definition Cut {tus tvs} (t gl : wtexpr Esymbol tus tvs tyProp)
    : InCtxA m tus tus tvs (wtgoal Esymbol tyProp tus tvs)%type :=
      fun sub ctx =>
        ret (@mkResultA _ _ _ (wtConj (wtGoal t) (wtHyp t (wtGoal gl)))
                        sub
                        migrator_id).

    Existing Instance Reflexive_Inst_evolves.

    Arguments wtctxD [_ _ _] _ _ {_} [_ _] _ _ _ _.
    Arguments wtctx [_] _ _ _ _.
    Lemma wtctxD_pure
      : forall tus tvs (ctx : wtctx Esymbol tyProp tus tvs) P,
        |-- P ->
        |-- wtctxD EsymbolD tyProp ctx P.
    Proof.
      induction ctx; simpl; intros; eauto.
      { eapply IHctx. red; simpl.
        intros. eapply lforallR. intros; eauto. }
      { eapply IHctx. red; simpl.
        intros. eapply limplAdj.
        rewrite <- H. charge_assumption. }
    Qed.

    Theorem Cut_sound
    : forall tus tvs t gl,
        InCtxA_spec (@Cut tus tvs t gl)
                    (fun gl' => wtgoalD EsymbolD gl' -->> wtexprD EsymbolD gl).
    Proof.
      unfold Cut. red. simpl; intros.
      eapply fmodels_ret.
      split; [ reflexivity | ].
      { simpl.
        intros.
        charge_clear.
        eapply wtctxD_pure.
        red; simpl; intros.
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
(*
  Section arrow_tactics.
    Context {m : Type -> Type}.
    Context {Monad_m : Monad m}.
    Context {Functor_m : Functor m}.
    Context {FLogic_m : FLogic m}.
    Context {MLogic_m : MLogic m}.

    Section pureA.
      Variables Pre Post
      : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.

      Definition pureA {tus tvs} (f : Pre tus tvs -> Post tus tvs)
      : logicA m Pre Post tus tus tvs :=
        fun prems sub goal =>
          ret {| result := f goal
               ; resultPrems := prems
               ; resultSubst := sub
               ; resultMigrator := migrator_id |}.

      Variable PreD : forall tus tvs,
          Pre tus tvs ->
          exprT TsymbolD tus tvs (typeD TsymbolD tyProp).
      Variable PostD : forall tus tvs,
          Post tus tvs ->
          exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

    End pureA.

    Section identA.
      Variables Pre
      : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.

      Definition identA {tus tvs} := @pureA Pre Pre tus tvs (fun x => x).

      Variable PreD : forall tus tvs,
          Pre tus tvs ->
          exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

      Theorem identA_sound
      : forall tus tvs, logicA_spec PreD PreD (@identA tus tvs).
      Proof.
      Admitted.
    End identA.

    Section composeA.
    Variables G G' G'' : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.

    Variable GD : forall tus tvs,
        G tus tvs ->
        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

    Variable GD' : forall tus tvs,
        G' tus tvs ->
        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

    Variable GD'' : forall tus tvs,
        G'' tus tvs ->
        exprT TsymbolD tus tvs (typeD TsymbolD tyProp).

    Context {tus tus' tus'' : list (Tuvar Tsymbol)}.
    Context {tvs : list (type Tsymbol)}.
    Definition composeA
               (a : logicA m G G' tus tus' tvs)
               (b : logicA m G' G'' tus' tus'' tvs)
    : logicA m G G'' tus tus'' tvs :=
      fun prems sub goal =>
        bind (a prems sub goal)
             (fun x =>
                match x with
                | mkResultA _ goal' prems' sub' mig' =>
                  fmap (fun x =>
                          match x with
                          | mkResultA _ goal'' prems'' sub'' mig'' =>
                            mkResultA _ goal'' prems'' sub''
                                      (migrator_compose mig' mig'')
                          end) (b prems' sub' goal')
                end).

    Theorem composeA_sound
    : forall a b,
        logicA_spec GD GD' a ->
        logicA_spec GD' GD'' b ->
        logicA_spec GD GD'' (composeA a b).
    Proof.
      intros.
      unfold composeA.
      red; simpl; intros; subst.
      eapply fmodels_bind.
      { eapply H; reflexivity. }
      { destruct x. destruct 1.
        eapply fmodels_fmap.
        2: eapply H0; reflexivity.
        destruct x; destruct 1.
        split.
        { eapply Inst_evolves_trans; eauto. }
        { admit. } }
    Admitted.

    Definition logicC_of_logicA (l : logicA m G G' tus tus' tvs)
    : logicC m G G' tus tvs :=
      fun prems sub goal =>
        fmap (fun x => mkResultC x) (l prems sub goal).

    End composeA.

    Definition prodA {tus tvs} {G1 G2 G3 G4}
               (a : logicA m G1 G2 tus tus tvs)
               (b : logicA m G3 G4 tus tus tvs)
    : logicA m
             (fun tus tvs => G1 tus tvs * G3 tus tvs)%type
             (fun tus tvs => G2 tus tvs * G4 tus tvs)%type
             tus tus tvs :=
      fun prems sub gl =>
        bind (a prems sub (fst gl))
             (fun a' =>
                match a' with
                | mkResultA _ gla prems' sub' mig' =>
                  fmap (F:=m)
                       (fun b' =>
                          match b' with
                          | mkResultA _ glb prems'' sub'' mig'' =>
                            {| result := (gla,glb)
                               ; resultPrems := prems''
                               ; resultSubst := sub''
                               ; resultMigrator := migrator_compose mig' mig''
                            |}
                          end)
                       (b prems' sub' (snd gl))
                      end).

  End arrow_tactics.

  Arguments identA {_ _ _ _ _} _ _ _.
  Arguments composeA {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _.
  Arguments pureA {_ _ _ _ _ _} _ _ _ _.

(*
    Section migrating.
      Context {tus tus' : list (Tuvar Tsymbol)}.
      Context {tvs : list (type Tsymbol)}.

      Context {Pre Post Val : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type}.
      Variable migVal : Migrate Esymbol Val.

      Definition migrating
                 (c : logicA m Pre Post tus tus' tvs)
      : logicA m
               (fun tus tvs => Pre tus tvs * Val tus tvs)%type
               (fun tus tvs => Post tus tvs * Val tus tvs)%type
               tus tus' tvs :=
        fun prems sub gl =>
          fmap (fun x =>
                  match x with
                  | mkResultA _ gl' prems' sub' mig' =>
                    mkResultA _ (gl', migrate mig' (snd gl))
                              prems' sub' mig'
                  end)
               (c prems sub (fst gl)).
    End migrating.
*)

    (** TODO(gmalecha): Fundamentally this operation is the problem.
     ** This type does not express the fact that the lemma is related to
     ** the outside lemma.
     **)
    Definition inj_lemma {tus tvs}
               (lem : lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp) nil nil)
    : logicA m
             (fun tus tvs => unit)
             (fun tus tvs => lemma (fun tus tvs => wtexpr Esymbol tus tvs tyProp) tus tvs)
             tus tus tvs :=
      pureA (fun _ =>
               match app_nil_r_trans tvs in _ = X return lemma _ _ X with
               | eq_refl => lift_lemma tvs (@migrator_pure tus) lem
               end).

    Definition Var {tus tvs} {t} (mem : member t tvs)
    : logicA m
             (fun _ _ => unit)
             (fun tus tvs => wtexpr Esymbol tus tvs t)
             tus tus tvs :=
      pureA (fun _ => wtVar mem).

    Definition Uvar {tus tvs} {ts t} (mem : member (ts,t) tus)
    : logicA m
             (fun tus tvs => hlist (wtexpr Esymbol tus tvs) ts)
             (fun tus tvs => wtexpr Esymbol tus tvs t)
             tus tus tvs :=
      pureA (fun hl => wtUVar mem hl).
*)