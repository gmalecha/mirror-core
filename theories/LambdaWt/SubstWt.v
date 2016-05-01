Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.LambdaWt.WtExpr.

Set Implicit Arguments.
Set Strict Implicit.
Set Primitive Projections.

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

  Record Inst (tus : list Tuvar) : Type :=
  { values   : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus
  ; _acyclic : Acyclic values }.

  Section instD.
    Variable tus' : list Tuvar.
    Variable us' : hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
            tus'.

    Fixpoint InstD' (tus : list Tuvar)
             (inst : hlist (fun tst => option (wtexpr tus' (fst tst) (snd tst))) tus)
    : hlist (fun tst => hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
            tus -> Prop :=
      match inst in hlist _ tus
            return hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                         tus -> Prop
      with
      | Hnil => fun _ => True
      | Hcons None ist => fun us => InstD' ist (hlist_tl us)
      | Hcons (Some val) ist => fun us =>
           (forall cs, hlist_hd us cs = wtexprD EsymbolD val us' cs)
        /\ InstD' ist (hlist_tl us)
      end.
  End instD.

  Definition InstD (tus : list Tuvar)
             (inst : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus)
             (us : hlist (fun tst =>
                            hlist (typeD TsymbolD) (fst tst) -> typeD TsymbolD (snd tst))
                         tus)
  : Prop :=
    @InstD' tus us tus inst us.

  Definition Inst_lookup {tus} (i : Inst tus) {ts t} (uv : member (ts,t) tus)
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

  Definition Inst_set {tus ts t} (uv : member (ts,t) tus) (e : wtexpr tus ts t)
             (i : Inst tus)
  : Inst tus :=
    {| values := hlist_set (Some e) uv i.(values)
     ; _acyclic := I
     |}.

  Inductive Unifiable {tus} (s : Inst tus) (tvs : list type) (t : type)
  : wtexpr tus tvs t -> wtexpr tus tvs t -> Prop :=
  | Unif_UVar : forall ts (u : member (ts,t) tus) xs e,
      Inst_lookup s u = Some e ->
      @Unifiable tus s tvs t (wtUVar u xs) (subst xs e).

(*
  Definition Unifiable_eq {tus} s tvs t a b : Prop :=
    @Unifiable tus s tvs t a b \/ @Unifiable tus s tvs t b a.
*)

  Definition Inst_evolves {tus} (i1 i2 : Inst tus) : Prop :=
    forall tvs t (e1 e2 : wtexpr tus tvs t),
      wtexpr_equiv (Unifiable i1) e1 e2 ->
      wtexpr_equiv (Unifiable i2) e1 e2.


  Theorem Inst_set_ok : forall tus tvs ts t (u : member (ts,t) tus) w s s',
      Inst_set u w s = s' ->
      Inst_lookup s u = None ->
      Inst_evolves s s' /\
      forall xs, Unifiable s' (wtUVar u xs) (subst (tvs:=tvs) xs w).
  Proof.
    intros. subst.
    split.
    { red. intros.
      induction H; try solve [ constructor; eauto ].
      - constructor.
        clear - H.
        induction H; constructor; auto.
      - constructor.
        inversion pf. constructor. subst.
        unfold Inst_lookup, Inst_set. simpl.
        etransitivity; [ | eapply H ].
        unfold Inst_lookup.
        clear - H0 H u0 u Tsymbol_eq_dec.
        eapply (@hlist_get_set_neq' _ _ _ (Some w) _ _ u0 u (values s)).
        intros. intro.
        subst. unfold Inst_lookup in *.
        inversion pf. subst.
        rewrite (UIP_refl pf) in H.
        congruence.
      - eapply eqTrans; eauto. }
    { intros.
      constructor. unfold Inst_lookup, Inst_set.
      simpl. rewrite hlist_get_set. reflexivity. }
    Unshelve.
    eapply pair_eq_dec.
    eapply list_eq_dec. eapply type_eq_dec. eapply Tsymbol_eq_dec.
    eapply type_eq_dec. eapply Tsymbol_eq_dec.
  Defined.

End subst.
