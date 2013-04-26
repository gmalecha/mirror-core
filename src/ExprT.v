(* A type system for Expr
 * This achieves a phase split between the 'well-formedness' of expressions
 * and their meaning
 *)
Require Import List Bool.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.ExprCore.

Set Implicit Arguments.
Set Strict Implict.

Section typed.
  Variable ts : types.

  Definition typeof_func (f : function ts) : tfunction :=
    {| tfenv := fenv f ; tftype := ftype f |}.

  Definition well_typed_func (tf : tfunction) (f : function ts) : bool :=
    (tfenv tf) ?[ eq ] (fenv f) && typ_eqb (tftype tf) (ftype f).

  Definition typeof_funcs : functions ts -> tfunctions :=
    map typeof_func.

  Fixpoint well_typed_funcs (tfs : tfunctions) (fs : functions ts) : bool :=
    match tfs , fs with
      | nil , nil => true
      | tf :: tfs , f :: fs =>
        if well_typed_func tf f then well_typed_funcs tfs fs else false
      | _ , _ => false
    end.

  Definition typeof_env : env ts -> tenv :=
    map (@projT1 _ _).

  Fixpoint well_typed_env (tes : tenv) (es : env ts) : bool :=
    match tes , es with
      | nil , nil => true
      | t :: tes , e :: es => 
        if typ_eqb t (projT1 e) then well_typed_env tes es else false
      | _ , _ => false
    end.      

  Variable fs : tfunctions.
  Variable uvars : tenv.

  Fixpoint typeof_expr (var_env : tenv) (e : expr ts) : option typ :=
    match e with
      | Const t' _ => Some t'
      | Var x  => nth_error var_env x
      | UVar x => nth_error uvars x 
      | Func f ts =>
        match nth_error fs f with
          | None => None
          | Some r => 
            if EqNat.beq_nat (length ts) (tfenv r) then
              Some (instantiate_typ (rev ts) (tftype r))
            else
              None
        end
      | App e es =>
        match typeof_expr var_env e with
          | None => None
          | Some tf => type_of_apply tf (map (typeof_expr var_env) es)
        end
      | Abs t e =>
        match typeof_expr (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal t e1 e2 => 
        match typeof_expr var_env e1 with
          | Some t' =>
            if typ_eqb t t' then 
              match typeof_expr var_env e2 with
                | Some t' =>
                  if typ_eqb t t' then Some tvProp else None
                | None => None
              end
            else None
          | None => None
        end
      | Not e =>
        match typeof_expr var_env e with
          | Some t' => if typ_eqb tvProp t' then Some tvProp else None
          | None => None
        end            
    end.

  Definition WellTyped_expr (var_env : tenv) (e : expr ts) (t : typ) : Prop :=
    typeof_expr var_env e = Some t.
  
End typed.

Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.ListNth.

Theorem nth_error_typeof_funcs : forall ts (fs : functions ts) n, 
  nth_error (typeof_funcs fs) n = match nth_error fs n with
                                    | None => None
                                    | Some x => Some (typeof_func x)
                                  end.
Proof.
  unfold typeof_funcs; intros.
  rewrite nth_error_map. reflexivity.
Qed.

Theorem nth_error_typeof_env : forall ts (fs : env ts) n, 
  nth_error (typeof_env fs) n = match nth_error fs n with
                                  | None => None
                                  | Some x => Some (projT1 x)
                                end.
Proof.
  unfold typeof_env; intros.
  rewrite nth_error_map. reflexivity.
Qed.

Theorem typeof_typeof_expr : forall ts fs uenv e venv t, 
  typeof_expr (ts := ts) (typeof_funcs fs) (typeof_env uenv) venv e = Some t ->
  typeof fs uenv venv e = Some t.
Proof.
  induction e; simpl; intros;
    repeat match goal with 
             | [ H : _ |- _ ] => rewrite H in *
             | [ H : Some _ = Some _ |- _ ] =>
               inversion H; clear H; subst                 
             | _ => rewrite nth_error_typeof_funcs in *
             | _ => rewrite nth_error_typeof_env in *
             | [ H : match ?X with _ => _ end = _ |- _ ] =>
               (consider X; intros; try congruence); [ ]
             | [ H : (if ?X then _ else _) = _ |- _ ] =>
               (consider X; intros; try congruence); [ ]
             | [ H : (if ?X then _ else _) = _ |- _ ] =>
               solve [ consider X; intros; try congruence ]
             | [ H : forall x, _ = _ -> _ |- _ ] =>
               specialize (H _ eq_refl)
             | |- None = Some _ => exfalso
           end; simpl; try congruence; auto.
  { eapply IHe in H0. rewrite H0. 
    clear - H H1. revert H1. revert t0. induction H; simpl; intros; auto.
    consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) venv x); intros; try congruence.
    erewrite H by eassumption.
    destruct t0; auto. destruct (typ_eqb t0_1 t1); auto. }
  { eapply IHe in H. rewrite H in *. reflexivity. }
Qed.

Theorem type_apply_length_equal : forall ts ft ts' n z fd,
  length ts' = n ->
  exists r, type_apply ts n ts' z ft fd = Some r.
Proof.
  induction ts'; simpl in *; intros; subst; simpl; eauto.
  match goal with
    [ |- exists x, match ?X with _ => _ end = _ ] =>
    consider X
  end; intros; eauto.
  destruct (@IHts' (length ts') (typD ts z a :: z) (fd (typD ts z a)) eq_refl).  
  simpl in *. clear - H H0.
  match goal with
    | [ H : ?X = None , H' : ?Y = Some _ |- _ ] =>
      let H'' := fresh in
        assert (H'' : X = Y) by reflexivity; congruence
  end.
Qed.

Theorem exprD_typof_expr_iff' : forall ts (fs : functions ts) uenv e tvenv t,
  typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv e = Some t ->
  exists v, exprD' fs uenv tvenv e t = Some v.
Proof.
  unfold WellTyped_expr.
  induction e; simpl; intros;
    repeat match goal with
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             | _ => congruence
             | [ H : typ_eq_odec _ _ = None |- _ ] => 
               apply typ_eq_odec_None in H
             | |- context [ match ?X with _ => _ end ] =>
               match X with
                 | match _ with _ => _ end => fail 1
                 | _ => consider X; intros
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
  { match goal with
      | |- context [ @eq_refl _ ?X ] =>
        generalize (@eq_refl _ X)
    end.
    pattern (nth_error tvenv v) at 2 3.
    rewrite H.
    rewrite typ_eq_odec_Some_refl.
    intros. eauto. }
  { destruct f0; simpl in *.  
    eapply type_apply_length_equal with (fd := fdenote) in H2. rewrite H1 in H2. 
    destruct H2; congruence. }
  { unfold lookupAs in *. rewrite H in *.
    rewrite typ_eq_odec_Some_refl in H0. congruence. }
  { revert H3. eapply typeof_typeof_expr in H0. rewrite H1 in H0.
    inversion H0; clear H0; subst. rewrite H4 in H2. inversion H2; clear H2; subst.
    clear - H. generalize dependent t2.
    induction H; simpl; intros.
    { inversion H3; clear H3; subst. rewrite typ_eq_odec_Some_refl. eauto. }
    { consider (typeof_expr (typeof_funcs fs) (typeof_env uenv) tvenv x); intros; try congruence.
      destruct t2; try congruence.
      change (typ_eqb t2_1 t0) with (t2_1 ?[ eq ] t0) in *.
      consider (t2_1 ?[ eq ] t0); intros; try congruence; subst.
      eapply H in H1. destruct H1. rewrite H1. eauto. } }
  { eapply typeof_typeof_expr in H0. rewrite H1 in H0.
    inversion H0; clear H0; subst. congruence. }
Qed.
