Require Import Coq.Lists.List.
Require Import Relations.Relation_Definitions.
Require Import Classes.RelationClasses.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Generic.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section Expr.
  Variable typ : Type.
  Variable RType_typ : RType typ.

  Variable expr : Type.

  Definition ResType (us vs : tenv typ) (T : Type) : Type :=    option (hlist (typD nil) us -> hlist (typD nil) vs -> T).

  (** TODO:
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
                         ResType us vs (typD nil t)
  ; Expr_acc : relation expr
  ; wf_Expr_acc : well_founded Expr_acc
  }.

  Theorem exprD'_conv (E : Expr)
  : forall tus tus' tvs tvs' e t
      (pfu : tus' = tus) (pfv : tvs' = tvs),
      exprD' tus tvs e t = match pfu in _ = tus'
                               , pfv in _ = tvs'
                                 return ResType tus' tvs' (typD nil t)
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
  : option (typD nil t) :=
    let (tus,us) := split_env uvar_env in
    let (tvs,vs) := split_env var_env in
    match exprD' tus tvs e t with
      | None => None
      | Some f => Some (f us vs)
    end.

  Class ExprOk (E : Expr) : Type :=
  { exprD'_weaken
    : forall tus tvs e t val,
        exprD' tus tvs e t = Some val ->
        forall tus' tvs',
        exists val',
             exprD' (tus ++ tus') (tvs ++ tvs') e t = Some val'
          /\ forall us vs us' vs',
               val us vs = val' (hlist_app us us') (hlist_app vs vs')
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
               return (hlist _ (tus ++ tus') -> hlist _ tvs' -> typD nil t)
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
               return (hlist _ tus' -> _ -> typD nil t)
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

(*
  Class FuncInstance0 (T : Type) (F : T) : Type :=
  { typ0_witness : TypInstance0 typD T
  ; ctor0 : expr
  ; ctor0_match : forall (R : expr -> Type)
      (caseCtor : unit -> R ctor0)
      (caseElse : forall e, R e)
      (e : expr), R e
  }.

  Class FuncInstance0Ok (T : Type) (F : T) (FI : @FuncInstance0 T F) : Type :=
  { ctor0_iso : forall us vs P,
      match exprD us vs ctor0 (@typ0 _ _ _ typ0_witness) with
        | None => False
        | Some G =>  P F <-> P (soutof (iso := typ0_iso nil) (fun x => x) G)
      end
  ; ctor0_match_ctor0 : forall R caseCtor caseElse,
                          @ctor0_match _ _ FI R caseCtor caseElse ctor0 = caseCtor tt
  }.

  (** I think something is missing for the iso **)
  Class FuncInstance1 (T : Type -> Type) (F : forall x, T x) : Type :=
  { typ1_witness : TypInstance1 typD T
  ; ctor1 : typ -> expr
  ; ctor1_match : forall (R : expr -> Type)
      (caseCtor : forall t, R (ctor1 t))
      (caseElse : forall e, R e)
      (e : expr), R e
  }.

  Class FuncInstance1Ok T F (FI : @FuncInstance1 T F) : Type :=
  { ctor1_iso : forall us vs t P,
      match exprD us vs (ctor1 t) (@typ1 _ _ _ typ1_witness t) with
        | None => False
        | Some G =>
          P (F (typD nil t)) <-> P (soutof (iso := typ1_iso nil t) (fun x => x) G)
      end
  }.

  Class FuncInstance2 (T : Type -> Type -> Type) (F : forall x y, T x y) : Type :=
  { typ2_witness : TypInstance2 typD T
  ; ctor2 : typ -> typ -> expr
  ; ctor2_iso : forall us vs t u P,
      match exprD us vs (ctor2 t u) (typ2 t u) with
        | None => False
        | Some G =>
          P (F (typD nil t) (typD nil u)) <-> P (soutof (iso := typ2_iso nil t u) (fun x => x) G)
      end
  ; ctor2_match : forall (R : expr -> Type)
      (caseCtor : forall t1 t2, R (ctor2 t1 t2))
      (caseElse : forall e, R e)
      (e : expr), R e
  }.

  (** This represents a function application **)
  Class AppInstance (TF TD TR : typ) : Type :=
  { fun_iso : forall ts, Iso (typD ts TF) (typD ts TD -> typD ts TR)
  ; sapp : forall ts, typD ts TF -> typD ts TD -> typD ts TR
  ; app1 : expr -> expr -> expr
  ; app1_check : forall e : expr, option { x : expr * expr & Expr_acc (fst x) e /\ Expr_acc (snd x) e }
  }.

  Class AppInstanceOk d r f (AI : @AppInstance f d r) : Type :=
  { app1_iso : forall us vs a b x y,
                 exprD us vs a f = Some x ->
                 exprD us vs b d = Some y ->
                 exprD us vs (app1 a b) r = Some (sapp x y)
  }.

  (** Generic application **)
  Record AppN (ft : typ) (dom : list typ) (ran : typ) : Type := mkAppN
  { appn : expr -> vector expr (length dom) -> expr
  ; appn_check : forall e : expr,
                   option { x : expr * vector expr (length dom) & Expr_acc (fst x) e /\ ForallV (fun x => Expr_acc x e) (snd x) }
  }.

(*
  Definition App0 A : AppN A nil A :=
    mkAppN A nil A (fun f _ => f).

  Definition AppS AS A R R' F (AI : @AppInstance F A R) (AI2 : @AppN R AS R') : AppN F (A :: AS) R'.
  refine (mkAppN F (A :: AS) R'
                 (fun f (args : vector expr (S (length AS))) =>
                    appn AI2 (app1 f (vector_hd args)) (vector_tl args))).
  Defined.
*)

  (** Application of a special symbol **)
  Section exp.
    Variable T : Type.

    Fixpoint exp (n : nat) : Type :=
      match n with
        | 0 => T
        | S n => T -> exp n
      end.

    Fixpoint app (n : nat) : exp n -> vector T n -> T :=
      match n with
        | 0 => fun x _ => x
        | S n => fun x v => app (x (vector_hd v)) (vector_tl v)
      end.

  End exp.


  Record SymAppN (n : nat) (dom : list (vector typ n -> typ)) (ran : exp typ n) : Type := mkSymAppN
  { sappn : vector typ n -> vector expr (length dom) -> expr
  ; sappn_check : forall e : expr, option { x : vector typ n * vector expr (length dom) & ForallV (fun x => Expr_acc x e) (snd x) }
  }.

  Definition SymApp0_0 T F `(FI : @FuncInstance0 T F) : @SymAppN 0 nil (@typ0 _ _ _ (@typ0_witness _ _ FI)).
  refine (@mkSymAppN 0 nil (@typ0 _ _ _ (@typ0_witness _ _ FI))
                    (fun _ _ => @ctor0 _ _ FI)
                    (fun e => @ctor0_match _ _ FI _ (fun x => Some (existT _ (Vnil _, Vnil _) _)) (fun e => None) e));
  constructor.
  Defined.

  Definition SymApp1_0 T F `(FI : @FuncInstance1 T F) : @SymAppN 1 nil (@typ1 _ _ _ (@typ1_witness _ _ FI)).
  refine (@mkSymAppN 1 nil (@typ1 _ _ _ (@typ1_witness _ _ FI))
                    (fun vs _ => @ctor1 _ _ FI (vector_hd vs))
                    (fun e => @ctor1_match _ _ FI _ (fun x => Some (existT _ (Vcons x (Vnil _), Vnil _) _)) (fun e => None) e));
  constructor.
  Defined.


  Definition SymAppS n A AS F R `(FI : forall ts, @AppInstance (app F ts) (A ts) (app R ts)) (Ap : @SymAppN n AS F)
  : @SymAppN n (A :: AS) R.
  refine (@mkSymAppN n (A :: AS) R
                    (fun ts args => @app1 _ _ _ (FI ts) (sappn Ap ts (vector_tl args)) (vector_hd args))
                    (fun e =>
                       match sappn_check Ap e with
                         | None => None
                         | Some (existT (ts_es) pf) =>
                           match @app1_check _ _ _ (FI (fst ts_es)) e with
                             | None => None
                             | Some (existT (e_e') pf') =>
                               let npf := @ForallV_cons _ (fun x => Expr_acc x e) _ _ _ (proj2 pf') pf in
                               Some (existT _ (fst ts_es, Vcons (snd e_e') (snd ts_es)) npf)
                           end
                       end)).
  Defined.

  (** Binder **)
  Record Lambda : Type :=
  { lambda : typ -> expr -> expr
  ; lambda_check : forall e : expr, option { x : typ * expr & Expr_acc (snd x) e }
  ; subst0 : expr -> expr -> expr
  }.

(*
  Definition App2 A B C D (AI : @AppInstance A B C) (AI2 : @AppInstance B D C) : AppN D (A :: B :: nil) C.
  refine (mkAppN D (A :: B :: nil) C
                 (fun f (args : vector expr 2) => app1 (app1 f (vector_hd args)) (vector_hd (vector_tl args)))).
  Defined.
*)
*)

End Expr.

Arguments Safe_expr {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD' {_ _ _ Expr} _ _ _ _ : rename.
Arguments exprD {_ _ _ Expr} _ _ _ _ : rename.
Arguments ResType {_ RType} _ _ _ : rename.