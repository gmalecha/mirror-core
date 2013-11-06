(** This file contains generic functions for manipulating,
 ** i.e. substituting and finding, unification variables
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Cases.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.
Require Import MirrorCore.Subst.

Set Implicit Arguments.
Set Strict Implicit.

(** Temporary **)
Require Import FunctionalExtensionality.

Section substU.
  Variable func : Type.
  Variable u : uvar.
  Variable e' : expr func.

  Fixpoint substU (under : nat) (e : expr func) : expr func :=
    match e with
      | Var _ => e
      | Inj _ => e
      | App l r => App (substU under l) (substU under r)
      | Abs t e => Abs t (substU (S under) e)
      | UVar u' =>
        if u ?[ eq ] u' then
          lift 0 under e'
        else UVar u'
    end.
End substU.

Section instantiate.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.
  Variable lookup : uvar -> option (expr func).

  Local Hint Immediate RSym_func : typeclass_instances.

  Fixpoint instantiate (under : nat) (e : expr func) : expr func :=
    match e with
      | Var _
      | Inj _ => e
      | App l r => App (instantiate under l) (instantiate under r)
      | Abs t e => Abs t (instantiate (S under) e)
      | UVar u =>
        match lookup u with
          | None => UVar u
          | Some e => lift 0 under e
        end
    end.

  Theorem typeof_expr_instantiate : forall tu tg,
    (forall u e',
       lookup u = Some e' ->
       exists t',
         nth_error tu u = Some t' /\
         typeof_expr tu tg e' = Some t') ->
    forall e tg',
      typeof_expr tu (tg' ++ tg) (instantiate (length tg') e) =
      typeof_expr tu (tg' ++ tg) e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ =>
               rewrite H
           end; auto.
    { specialize (IHe (t :: tg')). simpl in *.
      rewrite IHe. reflexivity. }
    { consider (lookup u); intros; simpl; auto.
      specialize (H _ _ H0). destruct H.
      intuition.
      generalize (typeof_expr_lift _ tu nil tg' tg e); simpl.
      congruence. }
  Qed.

  Theorem exprD'_instantiate : forall us gs',
    (forall u e',
       lookup u = Some e' ->
       exists tval,
         nth_error us u = Some tval /\
         ExprD.exprD us gs' e' (projT1 tval) = Some (projT2 tval)) ->
    forall e t v,
      let (tv',vs') := EnvI.split_env gs' in
      match ExprD.exprD' us (v ++ tv') e t ,
            ExprD.exprD' us (v ++ tv') (instantiate (length v) e) t
      with
        | Some l , Some r => forall vs,
                               l (hlist_app vs vs') = r (hlist_app vs vs')
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    unfold ExprD.exprD. intros us gs'.
    destruct (split_env gs'). intros Hlookup.
    induction e; simpl; intros; autorewrite with exprD_rw; auto.
    { change (
          let zzz z (pf : Some z = nth_error (v0 ++ x) v) cast :=
              fun e : hlist (typD ts nil) (v0 ++ x) =>
                           match
                             pf in (_ = t'')
                             return
                             (match t'' with
                                | Some t0 => typD ts nil t0
                                | None => unit
                              end -> typD ts nil t)
                           with
                             | eq_refl => fun x0 : typD ts nil z => cast x0
                           end (hlist_nth e v)
                in
          match
            match
              nth_error (v0 ++ x) v as z
              return
              (z = nth_error (v0 ++ x) v ->
               option (hlist (typD ts nil) (v0 ++ x) -> typD ts nil t))
            with
              | Some z =>
                fun pf : Some z = nth_error (v0 ++ x) v =>
                  match typ_cast_typ ts (fun x0 : Type => x0) nil z t with
                    | Some cast =>
                      Some (zzz z pf cast)
                    | None => None
                  end
              | None => fun _ : None = nth_error (v0 ++ x) v => None
            end eq_refl
          with
            | Some l =>
              match
                match
                  nth_error (v0 ++ x) v as z
                  return
                  (z = nth_error (v0 ++ x) v ->
                   option (hlist (typD ts nil) (v0 ++ x) -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (v0 ++ x) v =>
                      match typ_cast_typ ts (fun x0 : Type => x0) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (v0 ++ x) v => None
                end eq_refl
              with
                | Some r =>
                  forall vs : hlist (typD ts nil) v0,
                    l (hlist_app vs h) = r (hlist_app vs h)
                | None => False
              end
            | None =>
              match
                match
                  nth_error (v0 ++ x) v as z
                  return
                  (z = nth_error (v0 ++ x) v ->
                   option (hlist (typD ts nil) (v0 ++ x) -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (v0 ++ x) v =>
                      match typ_cast_typ ts (fun x0 : Type => x0) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (v0 ++ x) v => None
                end eq_refl
              with
                | Some _ => False
                | None => True
              end
          end).
      intro zzz; clearbody zzz; revert zzz; gen_refl.
      destruct (nth_error (v0 ++ x) v); auto.
      destruct (typ_cast_typ ts (fun x0 : Type => x0) nil t0 t); auto. }
    { forward. }
    { rewrite typeof_expr_instantiate.
      { consider (typeof_expr (typeof_env us) (v ++ x) e1); auto.
        destruct t0; auto.
        specialize (IHe1 (tyArr t0_1 t0_2) v).
        specialize (IHe2 t0_1 v).
        repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; auto.
        inv_all; subst. rewrite IHe2. rewrite IHe1. reflexivity. }
      { clear - Hlookup.
        intros. specialize (Hlookup _ _ H).
        destruct Hlookup. intuition.
        rewrite nth_error_typeof_env.
        rewrite H1.
        eexists; split; eauto.
        consider (ExprD.exprD' us x e' (projT1 x0)); try congruence; intros.
        eapply ExprD.typeof_expr_exprD'. eauto. } }
    { destruct t0; auto.
      specialize (IHe t0_2 (t :: v)). simpl in *.
      repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto.
      eapply functional_extensionality. intros.
      specialize (IHe (Hcons (p x0) vs)). simpl in *; auto. }
    { specialize (Hlookup u).
      destruct (lookup u).
      { unfold lookupAs.
        destruct (Hlookup _ eq_refl); clear Hlookup.
        intuition.
        rewrite H0. destruct x0; simpl in *.
        generalize (exprD'_lift _ us nil v x e t); simpl.
        consider (x0 ?[ eq ] t); intros; subst.
        { consider (ExprD.exprD' us x e t); try congruence; intros.
          consider (ExprD.exprD' us (v ++ x) (lift 0 (length v) e) t);
            consider (ExprD.exprD' us x e t); intuition; try congruence.
          inv_all. rewrite typ_cast_typ_refl.
          intros.
          specialize (H4 Hnil vs h). simpl in *. subst; auto. }
        { match goal with
            | |- match match match ?X with _ => _ end with _ => _ end with _ => _ end =>
              consider X; intros
          end.
          { generalize (typ_cast_typ_eq _ _ _ _ _ H3). congruence. }
          { repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto.
            clear - H H1 H4.
            assert (typeof_expr (typeof_env us) x e = Some t).
            { eapply ExprD.typeof_expr_exprD'; eauto. }
            assert (typeof_expr (typeof_env us) x e = Some x0).
            { eapply ExprD.typeof_expr_exprD'; eauto. }
            rewrite H2 in H0. inv_all; auto. } } }
      { autorewrite with exprD_rw.
        destruct (lookupAs us u t); auto. } }
  Qed.
End instantiate.

Section mentionsU.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Section param.
    Variable u : uvar.

    Fixpoint mentionsU (e : expr func) : bool :=
      match e with
        | Var _
        | Inj _ => false
        | UVar u' => EqNat.beq_nat u u'
        | App f e => if mentionsU f then true else mentionsU e
        | Abs _ e => mentionsU e
      end.
  End param.

  Lemma mentionsU_lift : forall u e a b,
    mentionsU u (lift a b e) = mentionsU u e.
  Proof.
    induction e; simpl; intros; rewrite lift_lift'; simpl; intuition;
    repeat rewrite <- lift_lift' in *; intuition.
    { destruct (NPeano.ltb v a); auto. }
    { rewrite IHe1. rewrite IHe2. auto. }
  Qed.

  Theorem mentionsU_substU : forall u u' e' e under,
    mentionsU u (substU u' e under e') =
    if u ?[ eq ] u' then
      if mentionsU u e' then mentionsU u e else false
    else
      if mentionsU u e' then true else if mentionsU u' e' then mentionsU u e else false.
  Proof.
    induction e'; simpl; try congruence; intros;
    repeat match goal with
             | H : _ |- _ => rewrite H
             | |- context [ ?X ?[ eq ] ?Y ] =>
               consider (X ?[ eq ] Y); try congruence; intros; auto
             | |- context [ EqNat.beq_nat ?X ?Y ] =>
               consider (EqNat.beq_nat X Y); try congruence; intros; subst; auto
             | |- context [ mentionsU ?X ?Y ] =>
               consider (mentionsU X Y); try congruence; intros; subst; auto
             | |- _ =>
               rewrite mentionsU_lift in *
           end; simpl in *; eauto.
    consider (EqNat.beq_nat u' u0); congruence.
    consider (EqNat.beq_nat u0 u0); congruence.
    consider (EqNat.beq_nat u u0); congruence.
  Qed.

  Lemma mentionsU_WellTyped : forall tu e tv t,
    WellTyped_expr tu tv e t ->
    forall n : uvar, length tu <= n -> mentionsU n e = false.
  Proof.
    induction e; simpl; intros; auto.
    { rewrite WellTyped_expr_App in H.
      do 2 destruct H. intuition.
      erewrite IHe1; eauto. }
    { rewrite WellTyped_expr_Abs in H.
      destruct H; intuition; subst.
      eapply IHe; eauto. }
    { rewrite WellTyped_expr_UVar in *.
      consider (EqNat.beq_nat n u); intros; auto.
      subst. exfalso.
      rewrite <- (app_nil_r tu) in H.
      rewrite nth_error_app_R in *; auto.
      destruct (u - length tu); inversion H. }
  Qed.

  Theorem typeof_expr_mentionsU_strengthen : forall tu e tg t',
    mentionsU (length tu) e = false ->
    typeof_expr (tu ++ t' :: nil) tg e =
    typeof_expr tu tg e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | _ : context [ match ?X with _ => _ end ] |- _ =>
               consider X; intros; try congruence
             | H : _ |- _ =>
               erewrite H by eauto
           end; auto.
    destruct (Compare_dec.lt_eq_lt_dec (length tu) u) as [ [ | ] | ].
    { rewrite nth_error_past_end.
      rewrite nth_error_past_end; auto.
      omega. rewrite app_length. simpl. omega. }
    { consider (EqNat.beq_nat (length tu) u); try congruence. }
    { rewrite nth_error_app_L by auto. auto. }
  Qed.

  Lemma typeof_expr_mentionsU_strengthen_multi_lem : forall tu tu' e tg,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    typeof_expr (tu ++ rev tu') tg e =
    typeof_expr tu tg e.
  Proof.
    intros. induction tu'; simpl.
    { rewrite app_nil_r. reflexivity. }
    { rewrite <- app_ass.
      rewrite typeof_expr_mentionsU_strengthen.
      eapply IHtu'.
      rewrite app_length. rewrite H; auto.
      omega. }
  Qed.

  Theorem typeof_expr_mentionsU_strengthen_multi : forall tu tu' e tg,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    typeof_expr (tu ++ tu') tg e =
    typeof_expr tu tg e.
  Proof.
    intros.
    rewrite <- (rev_involutive tu').
    eapply typeof_expr_mentionsU_strengthen_multi_lem. auto.
  Qed.

  Lemma exprD'_mentionsU_strengthen : forall tu u e,
    mentionsU (length tu) e = false ->
    forall tg t,
    match ExprD.exprD' (tu ++ u :: nil) tg e t
        , ExprD.exprD' tu tg e t
    with
      | None , None => True
      | Some l , Some r => forall vs,
                             l vs = r vs
      | _ , _ => False
    end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw;
    repeat match goal with
             | _ : context [ match ?X with _ => _ end ] |- _ =>
               consider X; try congruence; intros
           end.
    { change (
          let zzz z (pf : Some z = nth_error tg v) cast :=
              (fun e : hlist (typD ts nil) tg =>
                           match
                             pf in (_ = t'')
                             return
                             (match t'' with
                                | Some t0 => typD ts nil t0
                                | None => unit
                              end -> typD ts nil t)
                           with
                             | eq_refl => fun x : typD ts nil z => cast x
                           end (hlist_nth e v))
          in
          match
            match
              nth_error tg v as z
              return
              (z = nth_error tg v ->
               option (hlist (typD ts nil) tg -> typD ts nil t))
            with
              | Some z =>
                fun pf : Some z = nth_error tg v =>
                  match typ_cast_typ ts (fun x : Type => x) nil z t with
                    | Some cast =>
                      Some (zzz z pf cast)
                    | None => None
                  end
              | None => fun _ : None = nth_error tg v => None
            end eq_refl
          with
            | Some l =>
              match
                match
                  nth_error tg v as z
                  return
                  (z = nth_error tg v ->
                   option (hlist (typD ts nil) tg -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error tg v =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error tg v => None
                end eq_refl
              with
                | Some r => forall vs : hlist (typD ts nil) tg, l vs = r vs
                | None => False
              end
            | None =>
              match
                match
                  nth_error tg v as z
                  return
                  (z = nth_error tg v ->
                   option (hlist (typD ts nil) tg -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error tg v =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (zzz z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error tg v => None
                end eq_refl
              with
                | Some _ => False
                | None => True
              end
          end).
      intro zzz; clearbody zzz; revert zzz.
      gen_refl. destruct (nth_error tg v); auto.
      destruct (typ_cast_typ ts (fun x : Type => x) nil t0 t); auto. }
    { forward. }
    { rewrite typeof_env_app. simpl in *.
      rewrite typeof_expr_mentionsU_strengthen by (rewrite typeof_env_length; auto).
      consider (typeof_expr (typeof_env tu) tg e1); auto; intros.
      destruct t0; auto.
      specialize (H0 eq_refl tg (tyArr t0_1 t0_2)).
      specialize (IHe2 H1 tg t0_1).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
             end; inv_all; subst; auto.
      rewrite H4. rewrite IHe2. reflexivity. }
    { destruct t0; auto.
      specialize (IHe H (t :: tg) t0_2).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
             end; inv_all; subst; auto.
      eapply functional_extensionality; eauto. }
    { unfold lookupAs.
      destruct (Compare_dec.lt_eq_lt_dec (length tu) u0) as [ [ | ] | ].
      { repeat rewrite nth_error_past_end by (try rewrite app_length; simpl; omega).
        auto. }
      { exfalso.
        consider (EqNat.beq_nat (length tu) u0); congruence. } 
      { rewrite nth_error_app_L by omega.
        destruct (nth_error tu u0); auto.
        destruct s.
        destruct (TypesI.typ_cast (fun x0 : Type => x0) nil x t); auto. } }
  Qed.

  Lemma exprD'_mentionsU_strengthen_multi_lem : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      match ExprD.exprD' (tu ++ rev tu') tg e t
          , ExprD.exprD' tu tg e t
      with
        | None , None => True
        | Some l , Some r => forall vs,
                               l vs = r vs
        | _ , _ => False
      end.
  Proof.
    induction tu'; intros; simpl.
    { rewrite app_nil_r. destruct (ExprD.exprD' tu tg e t); auto. }
    { rewrite <- app_ass.
      assert (mentionsU (length (tu ++ rev tu')) e = false).
      { rewrite H; auto. rewrite app_length; omega. }
      generalize (exprD'_mentionsU_strengthen (tu ++ rev tu') a e H0 tg t).
      intros.
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X; intuition
             end.
      etransitivity. eapply H1. eapply IHtu'. }
  Qed.

  Theorem exprD'_mentionsU_strengthen_multi : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      match ExprD.exprD' (tu ++ tu') tg e t
          , ExprD.exprD' tu tg e t
      with
        | None , None => True
        | Some l , Some r => forall vs,
                               l vs = r vs
        | _ , _ => False
      end.
  Proof.
    intros.
    rewrite <- (rev_involutive tu').
    eapply exprD'_mentionsU_strengthen_multi_lem. auto.
  Qed.

  Theorem exprD_mentionsU_strength_multi : forall tu e,
    (forall n, length tu <= n -> mentionsU n e = false) ->
    forall tg t tu',
      ExprD.exprD (tu ++ tu') tg e t = ExprD.exprD tu tg e t.
  Proof.
    intros; unfold ExprD.exprD.
    destruct (split_env tg).
    generalize (exprD'_mentionsU_strengthen_multi tu e H x t tu').
    intros;
    repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X; intuition
             end.
    f_equal. eapply H0.
  Qed.

End mentionsU.


(** TODO: This is generic to [expr] **)
Section getInstantiation.
  Require Import MirrorCore.ExprI.
  Require Import MirrorCore.Ext.ExprD.

  Variable T : Type.
  Variable func : Type.
  Variable Subst_T : Subst T (expr func).

  Definition getInstantiation (s : T) : uvar -> nat -> option (list (expr func)) :=
    (fix recurse f l : option (list (expr func)) :=
       match l with
         | 0 => Some nil
         | S n =>
           match lookup f s with
             | None => None
             | Some z =>
               match recurse (S f) n with
                 | None => None
                 | Some zs' => Some (z :: zs')
               end
           end
       end).

  Variable ts : types.
  Variable RSym_func : RSym (typD ts) func.
  Variable SubstOk : SubstOk (Expr_expr _) Subst_T.
  Variable NormalizedSubstOk : NormalizedSubstOk Subst_T (@mentionsU func).

  Lemma getInstantiation_S : forall s b a,
    getInstantiation s a (S b) =
    match lookup a s with
      | None => None
      | Some e => match getInstantiation s (S a) b with
                    | None => None
                    | Some es => Some (e :: es)
                  end
    end.
  Proof. reflexivity. Qed.

  Lemma getInstantiation_0 : forall s a,
    getInstantiation s a 0 = Some nil.
  Proof. reflexivity. Qed.

  Lemma getInstantiation_contains_each : forall s b a i,
    getInstantiation s a b = Some i ->
    forall n,
      n < b ->
      exists e,
        lookup (a + n) s = Some e /\
        nth_error i n = Some e.
  Proof.
    induction b; intros.
    { exfalso. omega. }
    { rewrite getInstantiation_S in *.
      consider (lookup a s); try congruence; intros.
      consider (getInstantiation s (S a) b); try congruence; intros.
      inv_all; subst.
      specialize (IHb _ _ H1).
      destruct n.
      { rewrite Plus.plus_0_r. rewrite H. simpl; eauto. }
      { rewrite <- plus_n_Sm. eapply IHb. omega. } }
  Qed.

  Lemma nth_error_Some_len : forall T (ls : list T) n v,
    nth_error ls n = Some v ->
    n < length ls.
  Proof.
    induction ls; destruct n; simpl; unfold error, value; intros; try congruence.
    omega. eapply IHls in H. omega.
  Qed.

  Lemma WellTyped_getInstantiation : forall s us vs us' i,
    WellTyped_subst (SubstOk := SubstOk) (us ++ us') vs s ->
    getInstantiation s (length us) (length us') = Some i ->
    forall n,
      match nth_error us' n with
        | None => True
        | Some t =>
          exists e,
               nth_error i n = Some e
            /\ Safe_expr (Expr := Expr_expr _) us vs e t
      end.
  Proof.
    intros.
    specialize (getInstantiation_contains_each _ _ H0); intro.
    consider (nth_error us' n); auto; intros.
    generalize (nth_error_Some_len _ _ H2); intro.
    destruct (H1 _ H3).
    exists x.
    intuition.
    destruct (WellTyped_lookup _ _ _ _ H H5).
    rewrite nth_error_app_R in H4. 2: omega.
    cutrewrite (length us + n - length us = n) in H4; try omega.
    rewrite H2 in *. intuition; inv_all; subst.
    unfold Safe_expr in *; simpl in *.
    red in H8.
    rewrite typeof_expr_mentionsU_strengthen_multi in H8.
    eapply H8.
    intros.
    consider (length (us ++ us') ?[ le ] n0).
    { intros; eapply mentionsU_WellTyped with (n := n0); eauto. }
    { intros.
      destruct NormalizedSubstOk.
      destruct (H1 (n0 - length us)).
      { rewrite app_length in H7; omega. }
      { eapply lookup_normalized; try eassumption.
        replace (length us + (n0 - length us)) with n0 in H9 by omega.
        intuition eauto. } }
  Qed.
End getInstantiation.