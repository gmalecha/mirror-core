Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

(** Pattern matching via unification **)

Section patterns.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Inductive mpattern :=
  | PGet (i : nat) (t : typ)
  | PVar (v : nat)
  | PUVar (u : uvar)
  | PInj (f : sym)
  | PApp (l r : mpattern)
  | PAbs (t : typ) (e : mpattern).

  (** The type of an [mpattern] **)
  Fixpoint typeof_mpattern (tus tvs : list typ) (p : mpattern)
  : option typ :=
    match p with
      | PGet _ t => Some t
      | PVar v => nth_error tvs v
      | PUVar u => nth_error tus u
      | PInj f => typeof_sym f
      | PApp l r =>
        bind (typeof_mpattern tus tvs l)
             (fun tf =>
                bind (typeof_mpattern tus tvs r) (type_of_apply tf))
      | PAbs t e =>
        bind (typeof_mpattern tus (t :: tvs) e)
             (fun t' => ret (tyArr t t'))
    end.

  Fixpoint typecheck_mpattern (tgs : list typ) (p : mpattern) : bool :=
    match p with
      | PGet g t => nth_error tgs g ?[ eq ] Some t
      | PVar _ => true
      | PUVar _ => true
      | PInj _ => true
      | PApp l r => if typecheck_mpattern tgs l then
                      typecheck_mpattern tgs r
                    else false
      | PAbs _ e => typecheck_mpattern tgs e
    end.

  (** Convert an [mpattern] to an [expr]. [PGet] turn into unification
   ** variables indexed from [Ubase].
   **)
  Definition expr_of_mpattern (Ubase : uvar) : mpattern -> expr sym :=
    fix recur (p : mpattern) : expr sym :=
      match p with
        | PGet u _ => UVar (Ubase + u)
        | PVar v => Var v
        | PUVar v => UVar v
        | PInj f => Inj f
        | PApp l r => App (recur l) (recur r)
        | PAbs t e => Abs t (recur e)
      end.

  Fixpoint satisfies {T} (c : list (option T)) (ls : list T) : Prop :=
    match c with
      | nil => True
      | None :: cs => match ls with
                        | nil => False
                        | _ :: ls => satisfies cs ls
                      end
      | Some c :: cs => match ls with
                          | nil => False
                          | l :: ls => l = c /\ satisfies cs ls
                        end
    end.

  Fixpoint list_set (n : nat) (t : typ) (ls : list (option typ))
  : list (option typ) :=
    match n with
      | 0 => Some t :: tl ls
      | S n => match ls with
                 | nil => None :: list_set n t nil
                 | t' :: ts => t' :: list_set n t ts
               end
    end.

  Fixpoint getEnv' (p : mpattern) (ls : list (option typ))
  : option (list (option typ)) :=
    match p with
      | PGet u t =>
        match nth_error ls u with
          | None
          | Some None => Some (list_set u t ls)
          | Some (Some t') =>
            if t ?[ eq ] t' then Some ls else None
        end
      | PVar _ => Some ls
      | PInj _ => Some ls
      | PApp l r =>
        bind (getEnv' l ls) (getEnv' r)
      | PAbs _ e => getEnv' e ls
      | PUVar _ => Some ls
    end.

  Lemma satisfies_nth_error : forall i tgs t,
    nth_error tgs i ?[ eq ] Some t = true <->
    satisfies (list_set i t nil) tgs.
  Proof.
    induction i; destruct tgs; simpl; intros.
    { intuition. }
    { intuition.
      consider (typ_eqb t t0); intuition.
      subst. consider (typ_eqb t0 t0); intuition. }
    { intuition. }
    { eapply IHi. }
  Qed.

  Theorem getEnv_satisfies : forall a b c d,
    satisfies c d ->
    getEnv' a b = Some c ->
    satisfies b d.
  Proof.
    induction a; simpl; intros; forward_unsafe; subst; inv_all; subst; eauto.
    { generalize dependent i. revert d.
      induction b; simpl; intros; auto.
      destruct i; simpl in *; forward; intuition; subst.
      { inversion H2. }
      { destruct a; intuition; subst; eauto. } }
    { generalize dependent i. revert d.
      induction b; simpl; intros; auto.
      destruct i; simpl in *; forward; intuition; subst.
      { inversion H2. }
      { destruct a; intuition; subst; eauto. } }
  Qed.

  Theorem WellTyped_expr_expr_of_mpattern : forall tus ptrn tvs tgs t,
    typeof_mpattern tus tvs ptrn = Some t ->
    forall x tgs',
      getEnv' ptrn x = Some tgs' ->
      satisfies tgs' tgs ->
      WellTyped_expr (tus ++ tgs) tvs (expr_of_mpattern (length tus) ptrn) t.
  Proof.
    unfold WellTyped_expr.
    induction ptrn; simpl; intros; inv_all; subst; forward; eauto.
    { rewrite ListNth.nth_error_app_R by omega.
      replace (length tus + i - length tus) with i by omega.
      forward_unsafe; subst.
      { inv_all; subst.
        generalize dependent tgs'. clear. revert tgs.
        induction i; destruct tgs'; intuition; simpl in *;
        unfold error, value in *; intuition; inv_all; subst; try congruence.
        forward. destruct o; destruct tgs; intuition; subst; eauto. }
      { inv_all.
        rewrite <- rel_dec_correct.
        clear - H2 H1. subst.
        generalize dependent x; revert tgs.
        induction i; destruct tgs; simpl; intros; intuition; subst.
        consider (typ_eqb t0 t0); intuition.
        destruct x; simpl in *; intuition try congruence.
        destruct o; intuition.
        destruct x; simpl in *; intuition try congruence; eauto.
        destruct o; intuition eauto. }
      { inv_all; subst.
        clear - H1.
        generalize dependent x. revert tgs.
        induction i; simpl; intros; forward; intuition; subst; auto.
        { destruct x; destruct tgs; simpl in *; intuition eauto.
          destruct o; intuition.
          destruct o; intuition eauto. } } }
    { erewrite ListNth.nth_error_weaken; eauto. }
    { erewrite IHptrn1; eauto.
      erewrite IHptrn2; eauto.
      eauto using getEnv_satisfies. }
    { inv_all; subst.
      erewrite IHptrn; eauto. }
  Qed.

  Definition binders_of_mpattern (ptrn : mpattern) : option (list typ) :=
    match getEnv' ptrn nil with
      | None => None
      | Some r => mapT (fun x => x) r
    end.

  Lemma satisfies_mapT : forall T l tus',
    mapT (fun x => x) l = Some tus' ->
    satisfies (T := T) l tus'.
  Proof.
    induction l; simpl; intros; auto.
    forward. inv_all. subst.
    inversion H3; clear H3; subst.
    intuition.
  Qed.

  Theorem WellTyped_expr_binders_of_mpattern
  : forall ptrn tus tvs ty tus',
      binders_of_mpattern ptrn = Some tus' ->
      typeof_mpattern tus tvs ptrn = Some ty ->
      WellTyped_expr (tus ++ tus') tvs (expr_of_mpattern (length tus) ptrn) ty.
  Proof.
    intros.
    unfold binders_of_mpattern in *.
    consider (getEnv' ptrn nil); intros; try congruence.
    eapply WellTyped_expr_expr_of_mpattern; eauto using satisfies_mapT.
  Qed.
End patterns.