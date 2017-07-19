Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.
Require Import MirrorCore.LambdaWt.WtExpr.
Require Import MirrorCore.LambdaWt.WtMigrator.

Set Implicit Arguments.
Set Strict Implicit.
Set Primitive Projections.

Section substI.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.
  Let type := type Tsymbol.
  Variable Esymbol : type -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.
  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  Inductive Unifiable' {tus}
            (Inst_lookup : forall {ts t}, member (ts,t) tus -> option (wtexpr Esymbol tus ts t))
            (tvs : list type) (t : type)
  : wtexpr Esymbol tus tvs t -> wtexpr Esymbol tus tvs t -> Prop :=
  | Unif_UVar : forall ts (u : member (ts,t) tus) xs e,
      @Inst_lookup _ _ u = Some e ->
      @Unifiable' tus Inst_lookup tvs t (wtUVar u xs) (subst xs e).

  Definition inst_evolves {tus tus'} (mig : migrator Esymbol tus tus')
             (i1 : forall {ts t}, member (ts,t) tus -> option (wtexpr Esymbol tus ts t))
             (i2 : forall {ts t}, member (ts,t) tus' -> option (wtexpr Esymbol tus' ts t))
  : Prop :=
    forall tvs t (e1 e2 : wtexpr Esymbol tus tvs t),
      @Unifiable' _ (@i1) _ _ e1 e2 ->
      @Unifiable' _ (@i2) _ _ (migrate_expr mig e1) (migrate_expr mig e2).

  Variable (T : list (Tuvar Tsymbol) -> Type).

  Check wtexprD.

  Class Instantiation : Type :=
  { Inst_lookup : forall {tus} (i : T tus) {ts t} (uv : member (ts,t) tus),
                         option (wtexpr Esymbol tus ts t)
  ; Inst_set    : forall {tus ts t} (uv : member (ts,t) tus) (e : wtexpr Esymbol tus ts t)
                         (i : T tus), T tus
  ; Inst_fresh  : forall tst {tus}, T tus -> T (tus ++ tst :: nil)
  ; InstD       : forall {tus : list (Tuvar Tsymbol)}
                         (inst : T tus)
                         (us : hlist (fun tst =>
                                        hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                                     tus), Prop
  ; Inst_evolves : forall {tus tus'}, migrator Esymbol tus tus' -> T tus -> T tus' -> Prop :=
      fun tus tus' mig s s' =>
        inst_evolves mig (@Inst_lookup _ s) (@Inst_lookup _ s')
  ; Unifiable : forall {tus} (i : T tus) (tvs : list type) (t : type),
      wtexpr Esymbol tus tvs t -> wtexpr Esymbol tus tvs t -> Prop :=
      fun tus i => Unifiable' (@Inst_lookup _ i)
  ; Inst_set_ok : forall tus tvs ts t (u : member (ts,t) tus) w s s',
      Inst_set u w s = s' ->
      Inst_lookup s u = None ->
      inst_evolves migrator_id (@Inst_lookup _ s) (@Inst_lookup _ s') /\
      forall xs, Unifiable s' (wtUVar u xs) (subst (tvs:=tvs) xs w)
  ; Inst_lookup_ok : forall tus tvs ts t (u : member (ts,t) tus) w s,
      Inst_lookup s u = Some w ->
      forall xs, Unifiable s (wtUVar u xs) (subst (tvs:=tvs) xs w)
  ; InstD_ok : forall tus tvs i ts t u (e : wtexpr Esymbol _ ts t),
      @Inst_lookup tus i ts t u = Some e ->
      forall xs vs us,
        @InstD tus i us ->
        (** QUESTION: Is it better to write this in terms of subst or this way? *)
        @wtexprD _ _ _ EsymbolD tus tvs t (wtUVar u xs) us vs =
        @wtexprD _ _ _ EsymbolD tus ts t e us
                 (hlist_map (fun t e => @wtexprD _ _ _ EsymbolD tus tvs t e us vs) xs)
  }.

  Variable Inst : Instantiation.

  Theorem Inst_evolves_trans
  : forall tus tus' tus'' mig mig'
           (i : T tus) (i' : T tus') (i'' : T tus''),
      Inst_evolves mig i i' ->
      Inst_evolves mig' i' i'' ->
      Inst_evolves (migrator_compose mig mig') i i''.
  Proof.
    unfold Inst_evolves, inst_evolves.
    intros.
    repeat rewrite migrate_expr_migrator_compose.
    eapply H0. eapply H. assumption.
  Qed.

  Global Instance Reflexive_Inst_evolves tus
  : Reflexive (Inst_evolves (migrator_id (tus:=tus))).
  Proof.
    (* Coq bug! compute. *)
    repeat red. intros.
    repeat rewrite migrate_expr_migrator_id.
    assumption.
  Qed.

  Global Instance Transitive_Inst_evolves tus
  : Transitive (Inst_evolves (migrator_id (tus:=tus))).
  Proof.
    repeat red. intros.
    eapply H0.
    red in H. red in H.
    specialize (H _ _ e1 e2).
    repeat rewrite migrate_expr_migrator_id in H.
    eapply H.
    assumption.
  Qed.

End substI.


Section subst.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.
  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.
  Let type := type Tsymbol.
  Variable Esymbol : type -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.
  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  Let wtexpr := wtexpr Esymbol.
  Let Tuvar := Tuvar Tsymbol.

  Definition Acyclic (tus : list Tuvar)
             (h : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus)
  :=
    True.

  Record simple_inst (tus : list Tuvar) : Type :=
  { values   : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus
  ; _acyclic : Acyclic values }.

  Section instD.
    Variable tus' : list Tuvar.
    Variable us' : hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
            tus'.

    Fixpoint simple_instD' (tus : list Tuvar)
             (inst : hlist (fun tst => option (wtexpr tus' (fst tst) (snd tst))) tus)
    : hlist (fun tst => hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
            tus -> Prop :=
      match inst in hlist _ tus
            return hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                         tus -> Prop
      with
      | Hnil => fun _ => True
      | Hcons None ist => fun us => simple_instD' ist (hlist_tl us)
      | Hcons (Some val) ist => fun us =>
           (forall cs, hlist_hd us cs = wtexprD EsymbolD val us' cs)
        /\ simple_instD' ist (hlist_tl us)
      end.
  End instD.

  Definition instD (tus : list Tuvar)
             (inst : simple_inst tus)
             (us : hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                         tus)
  : Prop :=
    @simple_instD' tus us tus inst.(values) us.

  Definition simple_inst_lookup {tus} (i : simple_inst tus) {ts t} (uv : member (ts,t) tus)
  : option (wtexpr tus ts t) :=
    hlist_get uv i.(values).


  Section hlist_set.
    Context {T : Type} {F : T -> Type}.
    Variable t : T.
    Variable v : F t.

    Fixpoint hlist_set {ls : list T} (i : member t ls)
    : hlist F ls -> hlist F ls :=
      match i in member _ ls return hlist F ls -> hlist F ls with
      | MZ _ _ => fun hs => Hcons v (hlist_tl hs)
      | MN _ m => fun hs => Hcons (hlist_hd hs) (hlist_set m (hlist_tl hs))
      end.

    Lemma hlist_get_set
    : forall ls i hs,
        hlist_get (ls:=ls) i (hlist_set i hs) = v.
    Proof.
      induction i; simpl; intros; auto.
    Defined.

    Variable T_dec : EqDec T (@eq T).
    Lemma hlist_get_set_neq
    : forall ls i j hs,
        i <> j ->
        hlist_get (ls:=ls) i (hlist_set j hs) = hlist_get i hs.
    Proof.
      induction i; simpl; intros; auto.
      { destruct (member_case j).
        { destruct H0. subst.
          exfalso. apply H; clear H.
          rewrite (UIP_refl x). reflexivity. }
        { destruct H0. subst. reflexivity. } }
      { destruct (member_case j).
        { destruct H0. subst. simpl. auto. }
        { destruct H0. subst. simpl. eapply IHi.
          intro. apply H.
          subst. reflexivity. } }
    Defined.

    Lemma hlist_get_set_neq'
    : forall t' ls (i : member t' ls) j hs,
        (forall pf : t = t',
            i <> match pf with
                 | eq_refl => j
                 end) ->
        hlist_get (ls:=ls) i (hlist_set j hs) = hlist_get i hs.
    Proof.
      induction i; simpl; intros; auto.
      { destruct (member_case j).
        { destruct H0. subst.
          exfalso. specialize (H eq_refl). auto. }
        { destruct H0. subst. reflexivity. } }
      { destruct (member_case j).
        { destruct H0. subst. reflexivity. }
        { destruct H0. subst. simpl. eapply IHi.
          intros; intro. specialize (H pf). subst t'.
          subst i. tauto. } }
    Defined.

  End hlist_set.

  Definition simple_inst_set {tus ts t} (uv : member (ts,t) tus) (e : wtexpr tus ts t)
             (i : simple_inst tus)
  : simple_inst tus :=
    {| values := hlist_set (Some e) uv i.(values)
     ; _acyclic := I
     |}.

(*
  Inductive Unifiable {tus} (s : simple_inst tus) (tvs : list type) (t : type)
  : wtexpr tus tvs t -> wtexpr tus tvs t -> Prop :=
  | Unif_UVar : forall ts (u : member (ts,t) tus) xs e,
      Inst_lookup s u = Some e ->
      @Unifiable tus s tvs t (wtUVar u xs) (subst xs e).

  Definition Unifiable_eq {tus} s tvs t a b : Prop :=
    @Unifiable tus s tvs t a b \/ @Unifiable tus s tvs t b a.

  Definition Inst_evolves {tus tus'} (mig : migrator Esymbol tus' tus)
             (i1 : Inst tus) (i2 : Inst tus') : Prop :=
    forall tvs t (e1 e2 : wtexpr tus' tvs t),
      wtexpr_equiv (Unifiable i1) (migrate_expr mig e1) (migrate_expr mig e2) ->
      wtexpr_equiv (Unifiable i2) e1 e2.
*)


  Theorem simple_inst_set_ok
  : forall tus tvs ts t (u : member (ts,t) tus) w s s',
      simple_inst_set u w s = s' ->
      simple_inst_lookup s u = None ->
      inst_evolves migrator_id (@simple_inst_lookup _ s) (@simple_inst_lookup _ s') /\
      forall xs, Unifiable' (@simple_inst_lookup _ s')
                       (wtUVar u xs) (subst (tvs:=tvs) xs w).
  Proof.
    intros. subst.
    split.
    { red. intros.
      do 2 rewrite migrate_expr_migrator_id.
      destruct H. constructor.
      unfold simple_inst_lookup, simple_inst_set.
      simpl.
      rewrite <- H.
      eapply (@hlist_get_set_neq' _ _ _ (Some w) _ _ u0 u (values s)).
      clear - Tsymbol_eq_dec H H0.
      inversion pf. subst.
      rewrite (UIP_refl pf).
      intro. subst. congruence. }
    { intros.
      constructor. unfold simple_inst_lookup, simple_inst_set.
      simpl. rewrite hlist_get_set. reflexivity. }
    Unshelve.
    eapply pair_eq_dec; try eapply list_eq_dec;
      eapply type_eq_dec; eapply Tsymbol_eq_dec.
  Defined.

  Theorem simple_inst_lookup_ok
  : forall (tus : list (list (WtType.type Tsymbol) * WtType.type Tsymbol))
      (tvs ts : list (WtType.type Tsymbol)) (t : WtType.type Tsymbol)
      (u : member (ts, t) tus) (w : WtExpr.wtexpr Esymbol tus ts t)
      (s : simple_inst tus),
      simple_inst_lookup s u = Some w ->
      forall xs : hlist (WtExpr.wtexpr Esymbol tus tvs) ts,
        Unifiable' (@simple_inst_lookup tus s) (wtUVar u xs) (subst xs w).
  Proof.
    unfold simple_inst_lookup.
    destruct s. simpl.
    intros. constructor. assumption.
  Defined.

  Definition simple_inst_fresh
             (tst : WtExpr.Tuvar Tsymbol)
             {tus : list (WtExpr.Tuvar Tsymbol)}
             (i : simple_inst tus)
  : simple_inst (tus ++ tst :: nil) :=
    {| values :=
         hlist_app (hlist_map (fun t x =>
                                 fmap (F:=option)
                                      (migrate_expr (migrator_fresh tst _)) x)
                              i.(values))
                   (Hcons None Hnil)
     ; _acyclic := I |}.

  Global Instance Instantiation_simple_inst
  : @Instantiation Tsymbol TsymbolD Esymbol simple_inst :=
  { Inst_lookup := @simple_inst_lookup
  ; Inst_set    := @simple_inst_set
  ; Inst_fresh  := @simple_inst_fresh
  ; InstD       := @instD
  ; Inst_set_ok := simple_inst_set_ok
  ; Inst_lookup_ok := simple_inst_lookup_ok }.

End subst.

Arguments Inst_lookup {_ _ _ _ _} [_] _ [_ _] _.
Arguments Inst_set {_ _ _ _ _} [_ _ _] _ _ _.
Arguments Inst_fresh {_ _ _ _ _} _ [_] _.