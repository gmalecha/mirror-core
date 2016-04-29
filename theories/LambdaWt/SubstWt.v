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

  Definition Acyclic (tus : list Tuvar) (h : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus) :=
    True.

  Record Inst (tus : list Tuvar) : Type :=
  { values   : hlist (fun tst => option (wtexpr tus (fst tst) (snd tst))) tus
  ; _acyclic : Acyclic values }.

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

    Lemma hlist_get_set : forall ls i hs, hlist_get (ls:=ls) i (hlist_set i hs) = v.
    Proof.
      induction i; simpl; intros; auto.
    Defined.
  End hlist_set.

  Definition Inst_set {tus ts t} (uv : member (ts,t) tus) (e : wtexpr tus ts t) (i : Inst tus)
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
        admit.
      - eapply eqTrans; eauto. }
    { intros.
      constructor. unfold Inst_lookup, Inst_set.
      simpl. rewrite hlist_get_set. reflexivity. }
  Admitted.
End subst.
