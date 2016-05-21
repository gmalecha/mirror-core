Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.LambdaWt.WtType.
Require Import MirrorCore.LambdaWt.WtExpr.

Set Implicit Arguments.
Set Strict Implicit.

(* This is the universe of the reified language *)
Universe Urefl.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.

  (** Instantiation **)
  Definition migrator (tus tus' : list (Tuvar Tsymbol)) : Type :=
    hlist (fun tst => wtexpr Esymbol tus' (fst tst) (snd tst)) tus.

  Definition migrator_tl
  : forall {a b c} (mig : migrator (b :: c) a),
      migrator c a := fun _ => @hlist_tl _ _.

  Definition migrate_env {tus tus'}
             (mig : migrator tus' tus) (e : Uenv TsymbolD tus)
  : Uenv TsymbolD tus' := Eval cbv beta in
    hlist_map (fun _ val => wtexprD EsymbolD val e) mig.

  Section migrate_expr.
    Context {tus tus'} (mig : migrator tus tus').

    Fixpoint migrate_expr {tvs t}
             (e : wtexpr Esymbol tus tvs t)
    : wtexpr Esymbol tus' tvs t :=
      match e in wtexpr _ _ _ t
            return wtexpr _ tus' tvs t
      with
      | wtVar v => wtVar v
      | wtInj v => wtInj v
      | wtApp f x => wtApp (migrate_expr f) (migrate_expr x)
      | wtAbs e => wtAbs (migrate_expr e)
      | wtUVar u vs => subst (hlist_map (@migrate_expr tvs) vs) (hlist_get u mig)
      end.
  End migrate_expr.

  Fixpoint migrator_compose {tus tus' tus''}
           (mig : migrator tus tus')
           (mig' : migrator tus' tus'')
  : migrator tus tus'' :=
    match mig in hlist _ tus
          return migrator tus tus''
    with
    | Hnil => Hnil
    | @Hcons _ _ l ls e mig'0 => Hcons (migrate_expr mig' e) (migrator_compose mig'0 mig')
    end.

  Theorem migrate_env_migrate_expr
  : forall tus tus' tvs t (mig : migrator tus tus')
           (e : wtexpr Esymbol tus tvs t),
      forall us vs,
        wtexprD EsymbolD (migrate_expr mig e) us vs =
        wtexprD EsymbolD e (migrate_env mig us) vs.
  Proof.
    induction e.
    { simpl. unfold Var_exprT. reflexivity. }
    { simpl. unfold Pure_exprT. reflexivity. }
    { simpl. unfold Ap_exprT. intros.
      rewrite IHe1. rewrite IHe2. reflexivity. }
    { simpl. unfold Abs_exprT. intros.
      eapply FunctionalExtensionality.functional_extensionality.
      intros. eapply IHe. }
    { simpl. intros. unfold UVar_exprT.
      unfold migrate_env at 1.
      rewrite hlist_get_hlist_map.
      generalize (hlist_get u mig); simpl.
      rewrite hlist_map_hlist_map.
      intros. rewrite wtexprD_subst.
      rewrite hlist_map_hlist_map.
      f_equal.
      clear - H.
      induction H; simpl.
      - reflexivity.
      - f_equal; eauto. }
  Qed.

  Section mid.
    Variable T : Tuvar Tsymbol -> Type.

    Local Fixpoint migrator_id' (tus : list (Tuvar Tsymbol)) {struct tus}
    : (forall ts t, member (ts,t) tus -> T (ts,t)) ->
      hlist T tus :=
      match tus as tus
            return (forall ts t, member (ts,t) tus -> T (ts,t)) ->
                   hlist T tus
      with
      | nil => fun _ => Hnil
      | (ts,t) :: tus => fun mk =>
                           Hcons (@mk _ _ (@MZ _ _ _))
                                 (migrator_id' (fun ts t z => @mk ts t (MN _ z)))
      end.
  End mid.

  Local Fixpoint vars_id {tus} tvs
  : hlist (wtexpr Esymbol tus tvs) tvs :=
    match tvs as tvs
          return hlist (wtexpr Esymbol tus tvs) tvs
    with
    | nil => Hnil
    | t :: ts =>
      Hcons (wtVar (MZ t ts))
            (hlist_map
               (fun t' : type Tsymbol => wtexpr_lift (t :: nil) nil)
               (vars_id ts))
    end.

  Definition migrator_id tus : migrator tus tus :=
    @migrator_id' _ tus (fun ts t x => wtUVar x (vars_id ts)).
  Arguments migrator_id {tus} : rename.

  Lemma hlist_get_migrator_id'
  : forall T ts t tus mk (m : member (ts,t) tus),
      hlist_get m (@migrator_id' T tus mk) = mk _ _ m.
  Proof.
    induction m; simpl; auto.
    destruct l. simpl. rewrite IHm. reflexivity.
  Qed.

  Lemma hlist_get_migrator_id
  : forall ts t tus (m : member (ts,t) tus),
      hlist_get m (migrator_id (tus:=tus)) = wtUVar m (vars_id _).
  Proof.
    intros. unfold migrator_id.
    rewrite hlist_get_migrator_id'. reflexivity.
  Qed.

  Theorem migrate_expr_migrator_id
  : forall tus tvs t (e : wtexpr _ tus tvs t),
      migrate_expr migrator_id e = e.
  Proof.
    induction e; simpl; intros; auto.
    { rewrite IHe1. rewrite IHe2. reflexivity. }
    { rewrite IHe. reflexivity. }
    { rewrite hlist_get_migrator_id. simpl.
      f_equal.
      clear - H.
      induction H; simpl; auto.
      f_equal; eauto.
      etransitivity; [ | eassumption ].
      rewrite hlist_map_hlist_map.
      eapply hlist_map_ext.
      intros.
      rewrite <- IHhlist_Forall.
      rewrite hlist_map_hlist_map.
      eapply (fun Z => @subst_wtexpr_lift _ _ tus nil _ _ t0 (t :: nil) _
                                          Hnil (Hcons Z Hnil)). }
  Qed.

  Lemma hlist_map_vars_id_id
  : forall (p : _) (x : Venv TsymbolD p)
           (l : list (Tuvar Tsymbol))
           (h : hlist
                  (fun tst : Tuvar Tsymbol =>
                     hlist (typeD TsymbolD) (fst tst) ->
                     typeD TsymbolD (snd tst)) l),
      hlist_map
        (fun (x0 : type Tsymbol) (x1 : wtexpr Esymbol l p x0) =>
           wtexprD EsymbolD x1 h x) (vars_id p) = x.
  Proof.
    induction x; simpl; auto.
    { intros. f_equal. rewrite hlist_map_hlist_map.
      etransitivity; [ | eapply IHx ].
      eapply hlist_map_ext.
      intros.
      erewrite wtexprD_wtexpr_lift
      with (vs'':=Hnil) (vs':=Hcons f Hnil) (vs:=x).
      reflexivity. }
  Qed.

  (** TODO(gmalecha): Move to ExtLib.Data.HList *)
  Lemma hlist_ext : forall T (F : T -> Type) (ls : list T)
                           (a b : hlist F ls),
      (forall t (m : member t ls), hlist_get m a = hlist_get m b) ->
      a = b.
  Proof using.
    clear.
    induction a; intros.
    { rewrite (hlist_eta b). reflexivity. }
    { rewrite (hlist_eta b).
      f_equal.
      { eapply (H _ (MZ _ _)). }
      { eapply IHa.
        intros. eapply (H _ (MN _ _)). } }
  Defined.

  Lemma migrate_env_migrator_id
  : forall tus (e : Uenv TsymbolD tus),
      migrate_env migrator_id e = e.
  Proof using.
    intros.
    eapply hlist_ext; intros.
    unfold migrate_env.
    rewrite hlist_get_hlist_map.
    destruct t.
    rewrite hlist_get_migrator_id with (m:=m).
    simpl. unfold UVar_exprT.
    eapply FunctionalExtensionality.functional_extensionality; intros.
    rewrite hlist_map_hlist_map.
    rewrite hlist_map_vars_id_id.
    reflexivity.
  Qed.

End simple_dep_types.

Arguments migrator {_} _ _ _.
Arguments migrator_id {_ _ tus}.