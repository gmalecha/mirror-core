Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import Relations.Relation_Definitions.
Require Import Classes.RelationClasses.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.Fin.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Generic.
Require Import MirrorCore.Iso.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.EnvI.

Set Implicit Arguments.
Set Strict Implicit.

Section Expr.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.

  Variable expr : Type.

  (** TODO:
   ** - Right now this is intensionally weak, but it should probably include
   **   a few more operations given that it is already specialized for both
   **   [UVar] and [Var].
   ** - An alternative is to generalize it monadically and eliminate the
   **   specialized variable environments.
   **)
  Class Expr : Type :=
  { exprD : env typD -> env typD -> expr -> forall t : typ, option (typD nil t)
  ; Safe_expr : list typ -> list typ -> expr -> typ -> Prop
  ; acc : relation expr
  ; wf_acc : well_founded acc
  }.

  Class ExprOk (E : Expr) : Type :=
  { Safe_expr_exprD : forall us vs e t,
                        Safe_expr (typeof_env us) (typeof_env vs) e t <->
                        exists val, exprD us vs e t = Some val
  ; exprD_weaken : forall us us' vs vs' e t val,
                     exprD us vs e t = Some val ->
                     exprD (us ++ us') (vs ++ vs') e t = Some val
  }.

  Context {Expr_expr : Expr}.

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
        | Some G => P F <-> P (soutof (iso := typ0_iso nil) (fun x => x) G)
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
  ; app1_check : forall e : expr, option { x : expr * expr & acc (fst x) e /\ acc (snd x) e }
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
                   option { x : expr * vector expr (length dom) & acc (fst x) e /\ ForallV (fun x => acc x e) (snd x) }
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
  ; sappn_check : forall e : expr, option { x : vector typ n * vector expr (length dom) & ForallV (fun x => acc x e) (snd x) }
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
                               let npf := @ForallV_cons _ (fun x => acc x e) _ _ _ (proj2 pf') pf in
                               Some (existT _ (fst ts_es, Vcons (snd e_e') (snd ts_es)) npf)
                           end
                       end)).
  Defined.

  (** Binder **)
  Record Lambda : Type :=
  { lambda : typ -> expr -> expr
  ; lambda_check : forall e : expr, option { x : typ * expr & acc (snd x) e }
  ; subst0 : expr -> expr -> expr
  }.

(*
  Definition App2 A B C D (AI : @AppInstance A B C) (AI2 : @AppInstance B D C) : AppN D (A :: B :: nil) C.
  refine (mkAppN D (A :: B :: nil) C
                 (fun f (args : vector expr 2) => app1 (app1 f (vector_hd args)) (vector_hd (vector_tl args)))).
  Defined.
*)

End Expr.
