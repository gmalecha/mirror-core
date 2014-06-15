(** A simple programming language **)
Require Import Coq.Strings.String.
Require Import ExtLib.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.String.

Definition var := string.

Inductive op :=
| Plus | Minus.

Inductive aexpr :=
| Op : op -> aexpr -> aexpr -> aexpr
| Read : var -> aexpr
| Const : nat -> aexpr.

Inductive bexpr :=
| Eq : aexpr -> aexpr -> bexpr
| Lt : aexpr -> aexpr -> bexpr.

Inductive imp :=
| Write : var -> aexpr -> imp
| Seq   : imp -> imp -> imp
| If    : bexpr -> imp -> imp -> imp
| Loop  : bexpr -> imp -> imp
| Fail
| Skip.

Definition state := var -> option nat.

Definition state_upd (v : var) (n : nat) (s : state) : state :=
  fun v' => if v ?[ eq ] v' then Some n else s v'.

Section with_state.
  Variable s : state.

  Fixpoint denote_aexpr (e : aexpr) : option nat :=
    match e with
      | Op o a b =>
        ap (ap (pure match o with
                       | Plus => plus
                       | Minus => minus
                     end) (denote_aexpr a)) (denote_aexpr b)
      | Const n => pure n
      | Read v => s v
    end.

  Definition denote_bexpr (e : bexpr) : option bool :=
    match e with
      | Eq a b =>
        ap (ap (pure (fun a b => a ?[ eq ] b)) (denote_aexpr a)) (denote_aexpr b)
      | Lt a b =>
        ap (ap (pure (fun a b => a ?[ lt ] b)) (denote_aexpr a)) (denote_aexpr b)
    end.

End with_state.

Inductive step : state -> imp -> imp -> state -> Prop :=
| SWrite : forall s v a val,
             denote_aexpr s a = Some val ->
             step s (Write v a) Skip (state_upd v val s)
| SWriteFail : forall s v a,
                 denote_aexpr s a = None ->
                 step s (Write v a) Fail s
| SSeq1 : forall s c1 c2 c1' s',
            step s c1 c1' s' ->
            step s (Seq c1 c2) (Seq c1' c2) s'
| SSeqFail : forall s c,
               step s (Seq Fail c) Fail s
| SSeqSkip : forall s c,
               step s (Seq Skip c) c s
| SIfFail : forall s b tr fa,
              denote_bexpr s b = None ->
              step s (If b tr fa) Fail s
| SIfTrue : forall s b tr fa,
              denote_bexpr s b = Some true ->
              step s (If b tr fa) tr s
| SIfFalse : forall s b tr fa,
               denote_bexpr s b = Some false ->
               step s (If b tr fa) fa s
| SLoop : forall s b i,
            step s (Loop b i) (If b (Seq i (Loop b i)) Skip) s.

Inductive steps : state -> imp -> imp -> state -> Prop :=
| SSRefl : forall s a, steps s a a s
| SSTrans : forall s c c' s' c'' s'',
              step s c c' s' ->
              steps s' c' c'' s'' ->
              steps s c c'' s''.

Definition triple (P : state -> Prop) (c : imp) (Q : state -> Prop) : Prop :=
  forall s,
    P s ->
       (~exists s', steps s c Fail s')
    /\ (forall s', steps s c Skip s' -> Q s').

Theorem HConseq : forall (P P' Q Q' : state -> Prop) c,
                    (forall s, P s -> P' s) ->
                    (forall s, Q' s -> Q s) ->
                    triple P' c Q' ->
                    triple P c Q.
Proof.
  unfold triple. intros.
  { apply H in H2. apply H1 in H2.
    intuition. }
Qed.

Theorem HSkip : forall (P : state -> Prop),
                  triple P Skip P.
Proof.
  red. intros.
  split.
  { intro. destruct H0. inversion H0. subst. inversion H1. }
  { intros. inversion H0. subst; auto. subst. inversion H1. }
Qed.

Lemma Seq_Fail : forall s a b s',
                     steps s (Seq a b) Fail s' ->
                     (exists s', steps s a Fail s') \/
                     (exists s' s'', steps s a Skip s' /\ steps s' b Fail s'').
Proof.
  intros. remember (Seq a b). remember Fail.
  generalize dependent a.
  generalize dependent b.
  induction H.
  { subst. congruence. }
  { intros; subst.
    inversion H; clear H; subst.
    { specialize (IHsteps eq_refl _ _ eq_refl). intuition.
      { destruct H. left. exists x. eapply SSTrans; eauto. }
      { do 3 destruct H.
        right. exists x. exists x0.
        split. eapply SSTrans; eauto. assumption. } }
    { left. eauto. }
    { right. do 2 eexists. split. eapply SSRefl. eassumption. } }
Qed.

Lemma Seq_Skip : forall s a b s',
                     steps s (Seq a b) Skip s' ->
                     (exists s'', steps s a Skip s'' /\ steps s'' b Skip s').
Proof.
  intros. remember (Seq a b). remember Skip.
  generalize dependent a.
  generalize dependent b.
  induction H.
  { subst. congruence. }
  { intros; subst.
    inversion H; clear H; subst.
    { specialize (IHsteps eq_refl _ _ eq_refl). intuition.
      destruct IHsteps. destruct H.
      eexists. split. eapply SSTrans; eauto. eauto. }
    { inversion H0. subst. inversion H. }
    { inversion H0; clear H0; subst.
      { eexists; split; eauto using SSRefl. }
      { eexists; split; eauto using SSRefl.
        eapply SSTrans; eauto. } } }
Qed.

Theorem HSeq : forall (P Q R : state -> Prop) c1 c2,
                 triple P c1 Q ->
                 triple Q c2 R ->
                 triple P (Seq c1 c2) R.
Proof.
  unfold triple; intros.
  eapply H in H1.
  destruct H1.
  split.
  { intro. destruct H3. eapply Seq_Fail in H3. destruct H3; eauto.
    { do 3 destruct H3.
      eapply H2 in H3. eapply H0 in H3. intuition. eauto. } }
  { intros. eapply Seq_Skip in H3.
    do 2 destruct H3.
    eapply H2 in H3. eapply H0 in H3. destruct H3. eauto. }
Qed.

Theorem Skip_to_Fail : forall s s', steps s Skip Fail s' -> False.
Proof.
  intros.
  inversion H; clear H; subst.
  inversion H0.
Qed.

Theorem HFail : forall (P : state -> Prop),
                  triple (fun _ => False) Fail P.
Proof.
  red. destruct 1.
Qed.

Theorem HIf : forall (P Q : state -> Prop) b tr fa,
                (forall s, P s -> denote_bexpr s b <> None) ->
                triple (fun s => P s /\ denote_bexpr s b = Some true)
                       tr Q ->
                triple (fun s => P s /\ denote_bexpr s b = Some false)
                       fa Q ->
                triple P (If b tr fa) Q.
Proof.
  unfold triple.
  intuition.
  { destruct H3. inversion H3; clear H3; subst.
    inversion H4; clear H4; subst; eauto.
    { destruct (H0 s'); eauto. }
    { destruct (H1 s'); eauto. } }
  { inversion H3; clear H3; subst.
    inversion H4; clear H4; subst; eauto.
    { exfalso; eauto. }
    { destruct (H0 s'0); eauto. }
    { destruct (H1 s'0); eauto. } }
Qed.

Theorem HWrite : forall (P : state -> Prop) v e,
                   (forall s, P s -> denote_aexpr s e <> None) ->
                   triple P (Write v e) (fun s =>
                                           exists s' val,
                                             P s' /\
                                             denote_aexpr s' e = Some val /\
                                             s = state_upd v val s').
Proof.
  red. intros. intuition.
  { destruct H1. inversion H1; clear H1; subst.
    inversion H2; clear H2; subst.
    { eapply Skip_to_Fail in H3. assumption. }
    { eauto. } }
  { inversion H1; clear H1; subst.
    inversion H2; clear H2; subst.
    { exists s. rewrite H8. exists val. intuition.
      inversion H3; clear H3; subst. auto. inversion H1. }
    { exfalso. eauto. } }
Qed.

Theorem HLoop : forall (I : state -> Prop) b s,
                  (forall s, I s -> denote_bexpr s b <> None) ->
                  triple (fun s => I s /\ denote_bexpr s b = Some true)
                         s
                         I ->
                  triple I
                         (Loop b s)
                         (fun s => I s /\ denote_bexpr s b = Some false).
Proof.
  unfold triple.
  intros. split.
  { intro. destruct H2.
    admit. }
  { admit. }
Qed.