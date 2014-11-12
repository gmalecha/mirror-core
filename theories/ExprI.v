Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Eq.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.OpenT.

Set Implicit Arguments.
Set Strict Implicit.

Definition var := nat.
Definition uvar := nat.

Section Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.

  Variable expr : Type.

  Definition exprT (us : tenv typ) (vs : tenv typ) (T : Type) : Type :=
    OpenT typD us (OpenT typD vs  T).

  Definition Applicative_exprT tus tvs : Applicative (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ ap pure Applicative_OpenT ] in
  {| pure := fun _ x => pure (pure x)
   ; ap := fun _ _ f x => ap (T:=OpenT typD tus)
          (ap (T:=OpenT typD tus) (pure (ap (T:=OpenT typD tvs))) f) x
   |}.
  Existing Instance Applicative_exprT.

  Definition Functor_exprT tus tvs : Functor (exprT tus tvs) :=
    Eval cbv beta iota zeta delta [ fmap Functor_OpenT ] in
  {| fmap := fun _ _ f x => fmap (fmap f) x
  |}.
  Existing Instance Functor_exprT.

  Definition RexprT (tus tvs : tenv typ) {T} (R : relation T)
  : relation (exprT tus tvs T) :=
    OpenTeq (OpenTeq R).
  Arguments RexprT _ _ {_} _ _ _.

  Global Instance Reflexive_RexprT tus tvs T (R : relation T) (_ : Reflexive R)
  : Reflexive (RexprT tus tvs R).
  Proof.
    red. eapply Reflexive_OpenTeq. eapply Reflexive_OpenTeq. assumption.
  Qed.

  Global Instance Symmetric_RexprT tus tvs T (R : relation T) (_ : Symmetric R)
  : Symmetric (RexprT tus tvs R).
  Proof.
    red. eapply Symmetric_OpenTeq. eapply Symmetric_OpenTeq. assumption.
  Qed.

  Global Instance Transitive_RexprT tus tvs T (R : relation T) (_ : Transitive R)
  : Transitive (RexprT tus tvs R).
  Proof.
    red. eapply Transitive_OpenTeq. eapply Transitive_OpenTeq. assumption.
  Qed.


  Theorem eq_exprT_eq_F tus tvs
  : forall (T : Type) (F : T -> Type) (a b : T) (pf : a = b)
         (val : exprT tus tvs (F a)),
       match pf in (_ = x) return exprT tus tvs (F x) with
       | eq_refl => val
       end =
       fun a b =>
         match pf in (_ = x) return F x with
           | eq_refl => val a b
         end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq tus tvs
  : forall (a b : Type) (pf : a = b)
         (val : exprT tus tvs a),
       match pf in (_ = x) return (exprT tus tvs x) with
       | eq_refl => val
       end =
       fun a b =>
         match pf in (_ = x) return x with
           | eq_refl => val a b
         end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq_tus tvs
  : forall T a b (pf : a = b)
         (val : exprT a tvs T),
       match pf in (_ = x) return (exprT x tvs T) with
       | eq_refl => val
       end =
       fun us =>
         val match eq_sym pf in (_ = x) return hlist _ x with
               | eq_refl => us
             end.
  Proof.
    destruct pf; reflexivity.
  Qed.
  Theorem eq_exprT_eq_tvs tvs
  : forall T a b (pf : a = b)
         (val : exprT tvs a T),
       match pf in (_ = x) return exprT tvs x T with
       | eq_refl => val
       end =
       fun us vs =>
         val us match eq_sym pf in (_ = x) return hlist _ x with
                  | eq_refl => vs
                end.
  Proof.
    destruct pf; reflexivity.
  Qed.

  Definition exprT_UseV tus tvs (n : nat)
  : option { t : typ & exprT tus tvs (typD t) } :=
    match nth_error_get_hlist_nth _ tvs n with
      | None => None
      | Some (existT t get) =>
        Some (existT (fun t => exprT tus tvs (_ t)) t (fun _ vs => get vs))
    end.

  Definition exprT_UseU tus tvs (n : nat)
  : option { t : typ & exprT tus tvs (typD t) } :=
    match nth_error_get_hlist_nth _ tus n with
      | None => None
      | Some (existT t get) =>
        Some (existT (fun t => exprT tus tvs (_ t)) t (fun us _ => get us))
    end.

  Definition exprT_Inj tus tvs :=
    Eval simpl in @pure (exprT tus tvs)
                        (Applicative_exprT tus tvs).

  Hint Rewrite eq_exprT_eq eq_exprT_eq_F
       eq_exprT_eq_tus eq_exprT_eq_tvs : eq_rw.

  (** NOTE:
   ** - Right now this is intensionally weak, but it should probably include
   **   a few more operations given that it is already specialized for both
   **   [UVar] and [Var].
   ** - An alternative is to generalize it monadically and eliminate the
   **   specialized variable environments.
   ** - Note that this interface does not support GADTs
   **)
  Class Expr : Type :=
  { exprD' : forall (us vs : tenv typ),
               expr -> forall (t : typ),
                         option (exprT us vs (typD t))
  ; Expr_acc : relation expr
  ; wf_Expr_acc : well_founded Expr_acc
    (** This is derivable from information in variables, it is also
     ** bad for reasoning about
     **)
(*  ; mentionsAny : (uvar -> bool) -> (var -> bool) -> expr -> bool *)
  }.

  Theorem exprD'_conv (E : Expr)
  : forall tus tus' tvs tvs' e t
      (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD' tus tvs e t = match pfu in _ = tus'
                               , pfv in _ = tvs'
                                 return option (exprT tus' tvs' (typD t))
                           with
                             | eq_refl , eq_refl => exprD' tus' tvs' e t
                           end.
  Proof.
    destruct pfu. destruct pfv. reflexivity.
  Qed.

  Definition Safe_expr {E : Expr} (tus tvs : tenv typ) (e : expr) (t : typ)
  : Prop :=
    exists val, exprD' tus tvs e t = Some val.

  Theorem Safe_expr_exprD {E : Expr}
  : forall us vs e t,
      Safe_expr us vs e t <->
      exists val, exprD' us vs e t = Some val.
  Proof. reflexivity. Qed.

  Definition exprD {E : Expr} (uvar_env var_env : env) (e : expr) (t : typ)
  : option (typD t) :=
    let (tus,us) := split_env uvar_env in
    let (tvs,vs) := split_env var_env in
    match exprD' tus tvs e t with
      | None => None
      | Some f => Some (f us vs)
    end.

(*
  Definition mentionsV {Expr : Expr} (v : var) (e : expr) : bool :=
    mentionsAny (fun _ => false) (fun v' => v ?[ eq ] v') e.
  Definition mentionsU {Expr : Expr} (u : uvar) (e : expr) : bool :=
    mentionsAny (fun u' => u ?[ eq ] u') (fun _ => false) e.
*)

  Class ExprOk (E : Expr) : Type :=
  { exprD'_weaken
    : forall tus tvs e t val,
        exprD' tus tvs e t = Some val ->
        forall tus' tvs',
        exists val',
             exprD' (tus ++ tus') (tvs ++ tvs') e t = Some val'
          /\ forall us vs us' vs',
               val us vs = val' (hlist_app us us') (hlist_app vs vs')
    (** TODO: These are in Variables **)
(*
  ; exprD'_strengthenU_single
    : forall tus tvs e t t' val,
      mentionsU (length tus) e = false ->
      exprD' (tus ++ t :: nil) tvs e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val (hlist_app us (Hcons u Hnil)) vs = val' us vs
  ; exprD'_strengthenV_single
    : forall tus tvs e t t' val,
      mentionsV (length tvs) e = false ->
      exprD' tus (tvs ++ t :: nil) e t' = Some val ->
      exists val',
        exprD' tus tvs e t' = Some val' /\
        forall us vs u,
          val us (hlist_app vs (Hcons u Hnil)) = val' us vs
  ; Proper_mentionsAny
    : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) mentionsAny
  ; mentionsAny_factor
    : forall fu fu' fv fv' e,
          mentionsAny (fun u => fu u || fu' u) (fun v => fv v || fv' v) e
        = mentionsAny fu fv e || mentionsAny fu' fv' e
*)
  }.

  Context {Expr_expr : Expr}.

  Lemma exprD'_weakenU (EOk : ExprOk Expr_expr)
  : forall tus tus' tvs e t val,
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' (tus ++ tus') tvs e t = Some val'
        /\ forall us vs us',
             val us vs = val' (hlist_app us us') vs.
  Proof.
    intros.
    eapply (@exprD'_weaken Expr_expr) with (tus' := tus') (tvs' := nil) in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    erewrite exprD'_conv with (tus' := tus ++ tus') (tvs' := tvs ++ nil).
    instantiate (1 := app_nil_r_trans _).
    instantiate (1 := eq_refl).
    simpl.
    rewrite H.
    exists (match
               app_nil_r_trans tvs in (_ = tvs')
               return (hlist _ (tus ++ tus') -> hlist _ tvs' -> typD t)
             with
               | eq_refl => x
             end).
    split.
    { clear. revert x. destruct (app_nil_r_trans tvs). reflexivity. }
    { intros. erewrite H0.
      instantiate (1 := Hnil).
      instantiate (1 := us').
      clear.
      rewrite hlist_app_nil_r at 1.
      revert x. revert vs. destruct (app_nil_r_trans tvs).
      reflexivity. }
  Qed.

  Lemma exprD'_weakenV (EOk : ExprOk Expr_expr)
  : forall tus tvs tvs' e t val,
      exprD' tus tvs e t = Some val ->
      exists val',
        exprD' tus (tvs ++ tvs') e t = Some val'
        /\ forall us vs vs',
             val us vs = val' us (hlist_app vs vs').
  Proof.
    intros.
    eapply (@exprD'_weaken Expr_expr) with (tus' := nil) (tvs' := tvs') in H; eauto.
    destruct H as [ ? [ ? ? ] ].
    erewrite exprD'_conv with (tus' := tus ++ nil) (tvs' := tvs ++ tvs').
    instantiate (1 := @eq_refl _ _).
    instantiate (1 := app_nil_r_trans _).
    simpl.
    rewrite H.
    exists (match
               app_nil_r_trans tus in (_ = tus')
               return (hlist _ tus' -> _ -> typD t)
             with
               | eq_refl => x
             end).
    split.
    { clear. revert x. destruct (app_nil_r_trans tus). reflexivity. }
    { intros. erewrite H0.
      instantiate (1 := vs').
      instantiate (1 := Hnil).
      clear.
      rewrite hlist_app_nil_r at 1.
      revert x. revert us. destruct (app_nil_r_trans tus).
      reflexivity. }
  Qed.

  Theorem exprD_weaken (EOk : ExprOk Expr_expr)
  : forall us us' vs vs' e t val,
      exprD us vs e t = Some val ->
      exprD (us ++ us') (vs ++ vs') e t = Some val.
  Proof.
    unfold exprD. intros.
    repeat rewrite split_env_app.
    destruct (split_env us); destruct (split_env us');
    destruct (split_env vs); destruct (split_env vs').
    consider (exprD' x x1 e t); intros; try congruence.
    inversion H0; clear H0; subst.
    eapply exprD'_weaken in H; eauto with typeclass_instances.
    destruct H. destruct H.
    rewrite H. rewrite <- H0. reflexivity.
  Qed.

  Lemma list_rev_ind
  : forall T (P : list T -> Prop),
      P nil ->
      (forall l ls, P ls -> P (ls ++ l :: nil)) ->
      forall ls, P ls.
  Proof.
    clear. intros. rewrite <- rev_involutive.
    induction (rev ls).
    apply H.
    simpl. auto.
  Qed.

(*
*)

End Expr.

Arguments Safe_expr {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD' {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprT {_ RType} _ _ _ : rename.
Arguments exprT_Inj {_ _} _ _ {_} _ _ _ : rename.
Arguments exprT_UseU {_ _} tus tvs n : rename.
Arguments exprT_UseV {_ _} tus tvs n : rename.
Arguments RexprT {typ RType} tus tvs {_} _ _ _ : rename.

Export MirrorCore.TypesI.
Export MirrorCore.EnvI.
Export MirrorCore.OpenT.

Hint Rewrite eq_exprT_eq eq_exprT_eq_F
     eq_exprT_eq_tus eq_exprT_eq_tvs : eq_rw.