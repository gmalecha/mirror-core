Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.VarsToUVars.
Require Import MirrorCore.Instantiate.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.ExprSubstitute.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.

  Let M t := forall T, (t -> T) -> (expr typ func -> T) -> T.

  Definition or {t} (l r : M t) : M t :=
    fun T good bad => l T good (fun _ => r T good bad).

  Definition ret {t} (v : t) : M t :=
    fun _ good _ => good v.

  Definition ptrn (t : Type) : Type :=
    expr typ func -> M t.

  Definition tptrn (t : Type) : Type :=
    expr typ func -> forall T, (t -> T) -> T.

  Definition por {t} (l r : ptrn t) : ptrn t :=
    fun e T good bad =>
      l e T good (fun x => r x T good bad).

  Definition pmap {t u} (f : t -> u) (p : ptrn t) : ptrn u :=
    fun e T good bad =>
      p e T (fun x => good (f x)) bad.

  Definition get : ptrn (expr typ func) :=
    fun e _ good _ => good e.

  Definition pret {t} (v : t) : ptrn t :=
    fun e _ good _ => good v.

  Definition fail : ptrn Empty_set :=
    fun e _ _ bad => bad e.

  Definition app {T U} (f : ptrn T) (g : ptrn U) : ptrn (T * U) :=
    fun e _T good bad =>
      match e with
      | App l r => f l _T (fun f => g r _T (fun x => good (f,x)) bad) bad
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end%type.

  Definition var : ptrn nat :=
    fun e _T good bad =>
      match e with
      | Var v => good v
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Inj a => bad (Inj a)
      end.

  Definition uvar : ptrn nat :=
    fun e _T good bad =>
      match e with
      | UVar v => good v
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end.

  Definition inj : ptrn func :=
    fun e _T good bad =>
      match e with
      | UVar v => bad (UVar v)
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | Var a => bad (Var a)
      | Inj a => good a
      end.

  Definition abs {T} (p : ptrn T) : ptrn (typ * T) :=
    fun e _T good bad =>
      match e with
      | Abs t e' => p e _T (fun x => good (t, x)) bad
      | UVar v => bad (UVar v)
      | App a b => bad (App a b)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end%type.

  Definition exact (e : expr typ func) : ptrn unit.
  Admitted.

  Definition pdefault {T} (p : ptrn T) (d : T) : tptrn T :=
    fun e _T good => p e _T good (fun _ => good d).

  Definition list_case (t : typ) (s_cons : typ -> expr typ func) (s_nil : typ -> expr typ func)
             {P:Type}
             (f_nil : P) (f_cons : expr typ func -> expr typ func -> P) (f_default : P) : tptrn P :=
    Eval compute in
    pdefault (por (pmap (fun _ => f_nil) (exact (s_nil t)))
                  (pmap (fun xy =>
                           match xy with
                           | ((_,x),y) => f_cons x y
                           end) (app (app (exact (s_cons t)) get) get)))
             f_default.

End setoid.

(*
  Print list_case.

  Eval compute in por (pmap (fun _ => 1) (app get get))
                      (pmap (fun _ => 2) (var)).

Require Import MirrorCore.Util.Nat.
Check lt_rem.

  Definition under (n : nat) : ptrn nat :=
    fun e _T good bad =>
      match e with
      | Var v => match lt_rem v n with
                 | None => bad
                 | Some v => good v
                 end
      | _ => bad
      end.
*)