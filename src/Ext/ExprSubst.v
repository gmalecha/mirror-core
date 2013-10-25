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
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

(** Temporary **)
Require Import FunctionalExtensionality.

Section substU.
  Variable u : uvar.
  Variable e' : expr.

  Fixpoint substU (under : nat) (e : expr) : expr :=
    match e with
      | Var _ => e
      | Func _ _ => e
      | Not e => Not (substU under e)
      | Equal t l r => Equal t (substU under l) (substU under r)
      | App l r => App (substU under l) (substU under r)
      | Abs t e => Abs t (substU (S under) e)
      | UVar u' =>
        if u ?[ eq ] u' then
          lift 0 under e'
        else UVar u'
    end.
End substU.

Section instantiate.
  Variable T : Type.
  Variable lookup : uvar -> T -> option expr.

  Fixpoint instantiate (under : nat) (e : expr) (s : T) : expr :=
    match e with
      | Var _
      | Func _ _ => e
      | Not e => Not (instantiate under e s)
      | Equal t l r => Equal t (instantiate under l s) (instantiate under r s)
      | App l r => App (instantiate under l s) (instantiate under r s)
      | Abs t e => Abs t (instantiate (S under) e s)
      | UVar u =>
        match lookup u s with
          | None => UVar u
          | Some e => lift 0 under e
        end
    end.

  Theorem typeof_expr_instantiate : forall tfs tu tg s,
    (forall u e',
       lookup u s = Some e' ->
       exists t',
         nth_error tu u = Some t' /\
         typeof_expr tfs tu tg e' = Some t') ->
    forall e tg',
      typeof_expr tfs tu (tg' ++ tg) (instantiate (length tg') e s) =
      typeof_expr tfs tu (tg' ++ tg) e.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ =>
               rewrite H
           end; auto.
    { specialize (IHe (t :: tg')). simpl in *.
      rewrite IHe. reflexivity. }
    { consider (lookup u s); intros; simpl; auto.
      specialize (H _ _ H0). destruct H.
      intuition.
      generalize (typeof_expr_lift tfs tu nil tg' tg e); simpl.
      congruence. }
  Qed.

  Theorem exprD'_instantiate : forall ts (fs : functions ts) us gs' s,
    (forall u e',
       lookup u s = Some e' ->
       exists tval,
         nth_error us u = Some tval /\
         ExprD.exprD fs us gs' e' (projT1 tval) = Some (projT2 tval)) ->
    forall e t v,
      let (tv',vs') := EnvI.split_env gs' in
      match ExprD.exprD' fs us (v ++ tv') e t ,
            ExprD.exprD' fs us (v ++ tv') (instantiate (length v) e s) t
      with
        | Some l , Some r => forall vs,
                               l (hlist_app vs vs') = r (hlist_app vs vs')
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    unfold ExprD.exprD. intros ts fs us gs'.
    destruct (split_env gs'). intros s Hlookup.
    induction e; simpl; intros; autorewrite with exprD_rw; auto.
    { 
      
      change (
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
    { destruct (nth_error fs f); auto.
      destruct (type_apply ts (fenv f0) l nil (ftype f0) (fdenote f0)); auto.
      destruct (typ_cast_typ ts (fun x0 : Type => x0) nil
         (instantiate_typ l (ftype f0)) t); auto. }
    { rewrite typeof_expr_instantiate.
      { consider (typeof_expr (typeof_funcs fs) (typeof_env us) (v ++ x) e1); auto.
        destruct t0; auto.
        specialize (IHe1 (tvArr t0_1 t0_2) v).
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
        consider (ExprD.exprD' fs us x e' (projT1 x0)); try congruence; intros.
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
      destruct (lookup u s).
      { unfold lookupAs.
        destruct (Hlookup _ eq_refl); clear Hlookup.
        intuition.
        rewrite H0. destruct x0; simpl in *.
        generalize (exprD'_lift fs us nil v x e t); simpl.
        consider (x0 ?[ eq ] t); intros; subst.
        { consider (ExprD.exprD' fs us x e t); try congruence; intros.
          consider (ExprD.exprD' fs us (v ++ x) (lift 0 (length v) e) t);
            consider (ExprD.exprD' fs us x e t); intuition; try congruence.
          inv_all. rewrite typ_cast_typ_refl.
          intros.
          specialize (H5 Hnil vs h). simpl in *. subst; auto. }
        { match goal with
            | |- match match match ?X with _ => _ end with _ => _ end with _ => _ end =>
              consider X; intros
          end.
          { generalize (typ_cast_typ_eq _ _ _ _ _ H4). congruence. }
          { repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto.
            eapply H2.
            clear - H1 H5.
            assert (typeof_expr (typeof_funcs fs) (typeof_env us) x e = Some t).
            eapply ExprD.typeof_expr_exprD'; eauto.
            assert (typeof_expr (typeof_funcs fs) (typeof_env us) x e = Some x0).
            eapply ExprD.typeof_expr_exprD'; eauto.
            rewrite H in H0. inv_all; auto. } } }
      { autorewrite with exprD_rw.
        destruct (lookupAs us u t); auto. } }
    { destruct t0; auto.
      specialize (IHe1 t v); specialize (IHe2 t v).
      repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto. }
    { destruct t; auto.
      specialize (IHe tvProp v).
      repeat match goal with
                 | _ : context [ match ?X with _ => _ end ] |- _ =>
                   consider X; try congruence; intros
                 | |- context [ match ?X with _ => _ end ] =>
                   consider X; try congruence; intros
               end; inv_all; subst; auto. }
  Qed.
End instantiate.

Section mentionsU.
  Section param.
    Variable u : uvar.

    Fixpoint mentionsU (e : expr) : bool :=
      match e with
        | Var _
        | Func _ _ => false
        | UVar u' => EqNat.beq_nat u u'
        | App f e => if mentionsU f then true else mentionsU e
        | Abs _ e => mentionsU e
        | Equal _ e1 e2 => if mentionsU e1 then true else mentionsU e2
        | Not e => mentionsU e
      end.
  End param.

  Lemma mentionsU_lift : forall u e a b,
    mentionsU u (lift a b e) = mentionsU u e.
  Proof.
    induction e; simpl; intros; rewrite lift_lift'; simpl; intuition;
    repeat rewrite <- lift_lift' in *; intuition.
    { destruct (NPeano.ltb v a); auto. }
    { rewrite IHe1. rewrite IHe2. auto. }
    { rewrite IHe1. rewrite IHe2. auto. }
  Qed.

  Theorem typeof_expr_mentionsU_strengthen : forall tfs tu e tg t',
    mentionsU (length tu) e = false ->
    typeof_expr tfs (tu ++ t' :: nil) tg e =
    typeof_expr tfs tu tg e.
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

  Lemma exprD'_mentionsU_strengthen : forall ts (fs : functions ts) tu u e,
    mentionsU (length tu) e = false ->
    forall tg t,
    match ExprD.exprD' fs (tu ++ u :: nil) tg e t
        , ExprD.exprD' fs tu tg e t
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
    { destruct (nth_error fs f); auto.
      destruct (type_apply ts (fenv f0) l nil (ftype f0) (fdenote f0)); auto.
      destruct (typ_cast_typ ts (fun x : Type => x) nil (instantiate_typ l (ftype f0)) t); auto. }
    { rewrite typeof_env_app. simpl in *.
      rewrite typeof_expr_mentionsU_strengthen by (rewrite typeof_env_length; auto).
      consider (typeof_expr (typeof_funcs fs) (typeof_env tu) tg e1); auto; intros.
      destruct t0; auto.
      specialize (H0 eq_refl tg (tvArr t0_1 t0_2)).
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
    { destruct t0; auto.
      specialize (H0 eq_refl tg t); specialize (IHe2 H1 tg t).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
             end; inv_all; subst; auto. }
    { destruct t; auto.
      specialize (IHe H tg tvProp).
      repeat match goal with
               | _ : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; try congruence; intros
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; try congruence; intros
              end; inv_all; subst; auto. }
  Qed.

End mentionsU.
