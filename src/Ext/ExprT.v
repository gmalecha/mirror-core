(* A type system for Expr
 * This achieves a phase split between the 'well-formedness' of expressions
 * and their meaning
 *)
Require Import List Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable types : types.

  Definition WellTyped_func (tf : tfunction) (f : function types) : Prop :=
    tf.(tfenv) = f.(fenv) /\ tf.(tftype) = f.(ftype).

  Fixpoint WellTyped_funcs (tfs : tfunctions) (fs : functions types) : Prop :=
    Forall2 WellTyped_func tfs fs.

  Fixpoint WellTyped_env (tes : tenv typ) (es : env (typD types)) : Prop :=
    Forall2 (fun x y => x = projT1 y) tes es.

  Definition typeof_func (f : function types) : tfunction :=
    {| tfenv := fenv f ; tftype := ftype f |}.

  Definition typeof_funcs : functions types -> tfunctions :=
    map typeof_func.

  Section typeof_expr.
    Variable fs : tfunctions.
    Variable uvars : tenv typ.

    Fixpoint typeof_expr (var_env : tenv typ) (e : expr) : option typ :=
      match e with
        | Var x  => nth_error var_env x
        | UVar x => nth_error uvars x
        | Func f ts =>
          match nth_error fs f with
            | None => None
            | Some r =>
              if EqNat.beq_nat (length ts) (tfenv r) then
                Some (instantiate_typ ts (tftype r))
              else
                None
          end
        | App e e' =>
          Monad.bind (typeof_expr var_env e) (fun tf =>
          Monad.bind (typeof_expr var_env e') (fun tx =>
          type_of_apply tf tx))
        | Abs t e =>
          match typeof_expr (t :: var_env) e with
            | None => None
            | Some t' => Some (tvArr t t')
          end
        | Equal t e1 e2 =>
          match typeof_expr var_env e1 with
            | Some t' =>
              if t ?[ eq ] t' then
                match typeof_expr var_env e2 with
                  | Some t' =>
                    if t ?[ eq ] t' then Some tvProp else None
                  | None => None
                end
              else None
            | None => None
          end
        | Not e =>
          match typeof_expr var_env e with
            | Some t' => if tvProp ?[ eq ] t' then Some tvProp else None
            | None => None
          end
      end.

    Definition WellTyped_expr (var_env : tenv typ) (e : expr) (t : typ) : Prop :=
      typeof_expr var_env e = Some t.

    Theorem WellTyped_expr_Var : forall g v t',
      WellTyped_expr g (Var v) t' <-> nth_error g v = Some t'.
    Proof.
      unfold WellTyped_expr; simpl; intros; intuition.
    Qed.

    Theorem WellTyped_expr_Func : forall g f t' aps,
      WellTyped_expr g (Func f aps) t' <->
      (exists ft, nth_error fs f = Some ft /\
         length aps = tfenv ft /\
         instantiate_typ aps (tftype ft) = t').
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (nth_error fs f).
      { consider (EqNat.beq_nat (length aps) (tfenv t));
        try congruence; intuition.
        { inversion H0; clear H0; subst. eexists; eauto. }
        { destruct H0. intuition. inversion H1; subst; auto. }
        congruence.
        destruct H0. intuition. exfalso. inversion H1; clear H1; subst. auto. }
      { intuition; try congruence.
        destruct H. intuition congruence. }
    Qed.

    Theorem WellTyped_expr_UVar : forall g v t',
      WellTyped_expr g (UVar v) t' <-> nth_error uvars v = Some t'.
    Proof.
      unfold WellTyped_expr; simpl; intros; intuition.
    Qed.

    Theorem WellTyped_expr_Not : forall g e t,
      WellTyped_expr g (Not e) t <-> (t = tvProp /\ WellTyped_expr g e tvProp).
    Proof.
      Opaque rel_dec.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e); intuition try congruence.
      { consider (tvProp ?[ eq ] t0); congruence. }
      { consider (tvProp ?[ eq ] t0); try congruence. }
      { subst. inversion H1; clear H1; subst.
        match goal with
          | |- (if ?X then _ else _) = _ =>
            consider X; intros; try reflexivity
        end.
        intuition. }
    Qed.

    Theorem WellTyped_expr_Equal : forall g e1 e2 t t',
      WellTyped_expr g (Equal t e1 e2) t' <->
      (t' = tvProp /\ WellTyped_expr g e1 t /\ WellTyped_expr g e2 t).
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e1); destruct (typeof_expr g e2);
      intros; split; intros;
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : context [ if ?X then _ else _ ] |- _ ] =>
                 consider X; intros; subst
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; auto; try congruence.
      { consider (t ?[ eq ] t); intuition. }
    Qed.

    Theorem WellTyped_expr_Abs : forall g e t t',
      WellTyped_expr g (Abs t e) t' <->
      exists t'', t' = tvArr t t'' /\ WellTyped_expr (t :: g) e t''.
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr (t :: g) e); intuition; inv_all; subst; eauto.
      destruct H; intuition; inv_all; subst; auto.
      congruence.
      destruct H; intuition; congruence.
    Qed.

    Theorem WellTyped_expr_App : forall g e e' t,
      WellTyped_expr g (App e e') t <->
      (exists tf tx,
         WellTyped_expr g e tf /\
         WellTyped_expr g e' tx /\
         type_of_apply tf tx = Some t).
    Proof.
      unfold WellTyped_expr; simpl; intros.
      destruct (typeof_expr g e).
      { destruct (typeof_expr g e').
        { intuition eauto.
          do 2 destruct H; intuition. inv_all; subst; auto. }
        { intuition try congruence. do 2 destruct H; intuition congruence. } }
      { intuition; try congruence. do 2 destruct H. intuition congruence. }
    Qed.

    (** NOTE: This is suboptimal **)
(*
    Theorem WellTyped_expr_det : forall g e t1 t2,
      WellTyped_expr g e t1 ->
      WellTyped_expr g e t2 ->
      t1 = t2.
    Proof.
      unfold WellTyped_expr. intros. rewrite H in H0. congruence.
    Qed.
*)
  End typeof_expr.

  Theorem nth_error_typeof_funcs : forall (fs : functions types) n,
    nth_error (typeof_funcs fs) n = match nth_error fs n with
                                      | None => None
                                      | Some x => Some (typeof_func x)
                                    end.
  Proof.
    unfold typeof_funcs; intros.
    rewrite nth_error_map. reflexivity.
  Qed.

  Theorem nth_error_typeof_env : forall (fs : env (typD types)) n,
    nth_error (typeof_env fs) n = match nth_error fs n with
                                    | None => None
                                    | Some x => Some (projT1 x)
                                  end.
  Proof.
    unfold typeof_env; intros.
    rewrite nth_error_map. reflexivity.
  Qed.

  (* Lemma fold_left_monadic_fail : forall T U (f : option U -> T -> option U) y z, *)
  (*   (forall x, f None x = None) -> *)
  (*   fold_left f y None = Some z -> False. *)
  (* Proof. *)
  (*   induction y; simpl; intros; try congruence. eapply IHy. auto. *)
  (*   rewrite H in H0. eauto. *)
  (* Qed. *)

  (* Theorem typeof_typeof_expr : forall (fs : functions types)  uenv e venv t, *)
  (*   typeof_expr (typeof_funcs fs) (typeof_env uenv) venv e = Some t -> *)
  (*   typeof fs uenv venv e = Some t. *)
  (* Proof. *)
  (*   induction e; simpl; intros; *)
  (*   repeat match goal with *)
  (*            | [ H : _ |- _ ] => rewrite H in * *)
  (*            | [ H : Some _ = Some _ |- _ ] => *)
  (*              inversion H; clear H; subst *)
  (*            | _ => rewrite nth_error_typeof_funcs in * *)
  (*            | _ => rewrite nth_error_typeof_env in * *)
  (*            | [ H : match ?X with _ => _ end = _ |- _ ] => *)
  (*              (consider X; intros; try congruence); [ ] *)
  (*            | [ H : (if ?X then _ else _) = _ |- _ ] => *)
  (*              (consider X; intros; try congruence); [ ] *)
  (*            | [ H : (if ?X then _ else _) = _ |- _ ] => *)
  (*              solve [ consider X; intros; try congruence ] *)
  (*            | [ H : forall x, _ = _ -> _ |- _ ] => *)
  (*              specialize (H _ eq_refl) *)
  (*            | |- None = Some _ => exfalso *)
  (*          end; simpl; try congruence; auto. *)
  (*   { change (EqNat.beq_nat f0.(fenv) f0.(fenv)) with (f0.(fenv) ?[ eq ] f0.(fenv)). *)
  (*     rewrite rel_dec_eq_true; eauto with typeclass_instances. } *)
  (*   { erewrite IHe1 by eauto. *)
  (*     erewrite IHe2 by eauto. eauto. } *)
  (*   { erewrite IHe; eauto. } *)
  (* Qed. *)

(*
  Lemma exprD_typof_expr_iff' : forall (fs : functions types) uenv e venv t,
    typeof_expr (typeof_funcs fs) (typeof_env uenv) (typeof_env venv) e = Some t ->
    exists v, exprD fs uenv venv e t = Some v.
  Proof.
    induction e; simpl; intros;
    autorewrite with exprD_rw ;
    repeat match goal with
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             | _ => congruence
             | [ H : typ_cast_val _ _ _ _ = None |- _ ] =>
               eapply typ_cast_val_refl_None_False in H ;
               inversion H
             | |- context [ match ?X with _ => _ end ] =>
               match X with
                 | match _ with _ => _ end => fail 1
                 | _ => (consider X; try congruence); [ intros ]
               end
             | [ H : match ?X with _ => _ end = _ |- _ ] =>
               (consider X; intros; try congruence); [ ]
             | [ H : match ?X with _ => _ end = _ |- _ ] =>
               solve [ consider X; intros; try congruence ]
             | [ H : context [ if ?X then _ else _ ] |- _ ] =>
               (consider X; intros; try congruence); [ ]
             | [ H : _ = _ |- _ ] => rewrite H in *
             | _ => rewrite nth_error_typeof_funcs in *
             | _ => rewrite nth_error_typeof_env in *
             | [ H : typeof_expr _ _ _ _ = Some _
                     , H' : typeof _ _ _ _ = None |- _ ] =>
               eapply typeof_typeof_expr in H; congruence
             | [ H : typ_eqb _ _ = true |- _ ] => apply typ_eqb_true in H; subst
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H' : forall x y, typeof_expr _ _ _ ?X = Some _ -> _
                 , H : typeof_expr _ _ _ ?X = Some _ |- _ ] =>
               specialize (H' _ _ H)
             | [ |- exists x, None = Some _ ] => exfalso
           end; try solve [ congruence | eauto | auto ].
    { unfold lookupAs. rewrite H. destruct s. simpl.
      rewrite typ_cast_typ_refl. eauto. }
    { destruct f0; simpl in *. rewrite exprD_Func.
    Focus 3.
    change (map (@projT1 _ _) venv) with (typeof_env venv).
    erewrite typeof_typeof_expr by eauto.
    destruct t0; simpl in H1; try congruence.
    rewrite H3. change (typ_eqb t0_1 t1) with (t0_1 ?[ eq ] t1) in H1.
    consider (t0_1 ?[ eq ] t1); try congruence; intros. subst; inv_all; subst.
    rewrite H2. rewrite typ_eq_odec_Some_refl. eauto.
    rewrite H.
    subst.
    simpl in *.
    { match goal with
        | |- context [ @eq_refl ?Y ?X ] =>
          generalize (@eq_refl Y X)
      end.
      pattern (nth_error tvenv v) at 1 3.
      rewrite H.
      intros.
      change (typ_cast_typ types (fun x => x) nil t t)
        with (@typ_cast _ _ (@RType_typ types) (fun x => x) nil t t).
      destruct (@typ_cast_refl _ _ (RType_typ types) _ nil t (fun x => x)).
      intuition.
      match goal with
        | H : ?X = _ |- context [ match ?Y with _ => _ end ] =>
          change Y with X; rewrite H
      end. eauto. }
    { eapply typ_cast_val_refl in H2; auto. }
    { destruct f0; simpl in *.
      destruct (type_apply_length_equal ftype ts nil fdenote H2).
      match type of H1 with
        | ?X = _ => match type of H0 with
                      | ?Y = _ => change Y with X in H0; rewrite H1 in H0
                    end
      end.
      congruence. }
    { unfold lookupAs in *. rewrite H in *. destruct s; simpl in *.
      destruct (@typ_cast_refl _ _ (RType_typ types) _ nil x (fun x => x)).
      intuition.
      match goal with
        | H : ?X = _ |- _ =>
          change (typ_cast_typ types (fun x => x) nil x x) with X in H0 ;
            rewrite H in H0
      end.
      congruence. }
    { consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv e); intros.
      { rewrite (typeof_typeof_expr _ _ _ _ H0) in H1.
        inv_all; subst.
        eapply IHe in H0.
        destruct H0. rewrite H2 in H0. inv_all; subst.
        clear - H H3. generalize dependent t. generalize dependent t0.
        induction H; simpl; intros; inv_all; subst.
        { change (typ_cast_typ types (fun x0 : Type => x0) nil t t)
            with (@typ_cast _ _ (RType_typ types) (fun x => x) nil t t).
          destruct (@typ_cast_refl _ _ (RType_typ types) _ nil t (fun x => x)).
          intuition.
          match goal with
            | H : ?X = _ |- context [ match ?Y with _ => _ end ] =>
              change Y with X ; rewrite H
          end. eauto. }
        { consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv x);
          intros.
          destruct t0; simpl;
          try solve [ exfalso; eapply fold_left_monadic_fail; eauto ; reflexivity ].
          simpl in *. change (typ_eqb t0_1 t1) with (t0_1 ?[ eq ] t1) in *.
          consider (t0_1 ?[ eq ] t1); intros.
          { subst. eapply H in H1. destruct H1. rewrite H1.
            eapply IHForall in H3; eauto. }
          { exfalso; eapply fold_left_monadic_fail; eauto; reflexivity. }
          { exfalso; eapply fold_left_monadic_fail; eauto; reflexivity. } } }
      { exfalso; eapply fold_left_monadic_fail; eauto; reflexivity. } }
    { consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv e); intros.
      { rewrite (typeof_typeof_expr _ _ _ _ H0) in H1.
        inv_all; subst.
        eapply IHe in H0. destruct H0; intuition congruence. }
      { exfalso; eapply fold_left_monadic_fail; eauto; reflexivity. } }
    { consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv e); intros.
      { rewrite (typeof_typeof_expr _ _ _ _ H0) in H1.
        inv_all; subst.
        eapply IHe in H0. destruct H0; intuition congruence. }
      { exfalso; eapply fold_left_monadic_fail; eauto; reflexivity. } }
    { change (typ_cast_typ types (fun x0 : Type => x0) nil t1 t1)
        with (@typ_cast _ _ (RType_typ types) (fun x => x) nil t1 t1) in H1.
      destruct (@typ_cast_refl _ _ (RType_typ types) _ nil t1 (fun x => x)).
      intuition.
      match goal with
        | H : ?X = Some _ , H' : ?Y = None |- _ =>
          change Y with X in H' ; rewrite H in H'
      end. congruence. }
  Qed.

  Theorem WellTyped_expr_exprD : forall (fs : functions types) uenv e venv t,
    WellTyped_expr (typeof_funcs fs) (typeof_env uenv) (typeof_env venv) e t <->
    exists v, exprD fs uenv venv e t = Some v.
  Proof.
    unfold WellTyped_expr. intuition.
    { eapply exprD_typof_expr_iff' in H. unfold exprD.
      destruct H. consider (split_env venv); intros.
      assert (x0 = typeof_env venv).
      unfold typeof_env. rewrite <- split_env_projT1. rewrite H0. reflexivity.
      subst. rewrite H. eauto. }
    { unfold exprD in *.
      consider (split_env venv); intros.
      assert (x = typeof_env venv).
      unfold typeof_env. rewrite <- split_env_projT1. rewrite H. reflexivity.
      subst. destruct H0. clear H.
      generalize dependent (typeof_env venv); intros.
      consider (exprD' fs uenv t0 e t); intros; try congruence.
      inv_all; subst.
      clear - H. generalize dependent t. generalize dependent t0.
      admit.
    (*
    induction e; simpl; intros.
    { destruct (nth_error t0 v).
    { destruct (typ_eq_odec t t1); subst; auto; congruence. }
    { match goal with
        | [ H : match _ with _ => _ end ?X = _ |- _ ] =>
          generalize dependent X
      end.
      generalize (nth_error t0 v) at 2 3.
      destruct e; simpl; intros; try congruence.
      destruct (typ_eq_odec t2 t); subst; auto. congruence. } }
    { rewrite nth_error_typeof_funcs. destruct (nth_error fs f); try congruence.
      match goal with
        | [ H : match ?X with _ => _ end = _ |- _ ] =>
          consider X; intros; try congruence
      end.
      eapply type_apply_length_equal' in H.
      simpl in *.
      destruct (typ_eq_odec (instantiate_typ ts (ftype f0)) t); try congruence.
      inversion H0; clear H0; subst.
      change EqNat.beq_nat with (@rel_dec _ (@eq nat) _).
      consider (length ts ?[ eq ] tfenv (typeof_func f0)); intros; auto.
      exfalso; destruct f0; simpl in *; auto. }
    { rewrite nth_error_typeof_env. unfold lookupAs in *.
      destruct (nth_error uenv v); try congruence.
      destruct (typ_eq_odec (projT1 s) t); try congruence. }
    { consider (typeof fs uenv t0 e); intros; try congruence.
      consider (exprD' fs uenv t0 e t2); try congruence; intros.
      specialize (IHe _ _ _ H1).
      rewrite IHe. clear - H2 H.
      generalize dependent t0. revert t2. revert t.
      induction H; simpl; intros.
      { destruct (typ_eq_odec t2 t); subst; auto; congruence. }
      { destruct t2; try congruence.
        consider (exprD' fs uenv t0 x t2_1); try congruence; intros.
        specialize (H _ _ _ H1). rewrite H in *.
        change typ_eqb with rel_dec.
        rewrite rel_dec_eq_true; eauto with typeclass_instances. } }
    { generalize dependent t. destruct t1; try congruence; intros.
      change typ_eqb with eq_dec in *. consider (eq_dec t1_1 t); intros; subst.
      consider (exprD' fs uenv (t :: t0) e t1_2); try congruence; intros.
      rewrite (IHe _ _ _ H); auto.
      congruence. }
    { destruct t1; try congruence.
      consider (exprD' fs uenv t0 e1 t); intros; try congruence.
      consider (exprD' fs uenv t0 e2 t); intros; try congruence.
      erewrite IHe1 by eauto. erewrite IHe2 by eauto.
      change typ_eqb with rel_dec. rewrite rel_dec_eq_true; eauto with typeclass_instances. }
    { destruct t; try congruence.
      consider (exprD' fs uenv t0 e tvProp); intros; try congruence.
      inversion H0; clear H0; subst.
      erewrite IHe by eauto. reflexivity. } }
     *) }
  Qed.
*)

End typed.
