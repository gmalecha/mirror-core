Add Rec LoadPath "/Users/jebe/git/Charge/Charge!/bin/Charge" as Charge.
Add Rec LoadPath "/Users/jebe/git/coq-ext-lib/theories" as ExtLib.
Add Rec LoadPath "/Users/jebe/git/mirror-core/theories" as MirrorCore.
Add Rec LoadPath "/Users/jebe/git/mirror-core/examples" as McExamples.

Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.Lemma.
Require Import MirrorCore.RTac.RTac.
Require Import McExamples.Cancel.Lang.

Require Import Charge.ModularFunc.ListFunc.
Require Import Charge.ModularFunc.BaseType.
Require Import Charge.ModularFunc.ListType.

Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.


Set Implicit Arguments.
Set Strict Implicit.

Section canceller.
  Variables typ func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ2_func : Typ2 RType_typ Fun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.
  Context {RelDeq_eq : RelDec (@eq typ)}.

  Context {BT : BaseType typ} {BTD : BaseTypeD BT}.
  Context {LT : ListType typ} {LTD : ListTypeD LT}.

  Context {LF : ListFunc typ func}.
  Context {LFOk : ListFuncOk typ func}.

  Fixpoint expr_eqb e1 e2 :=
    match e1, e2 with
      | Var v1, Var v2 => Some (v1 ?[ eq ] v2)
      | Inj f1, Inj f2 => sym_eqb f1 f2
      | App e1 e3, App e2 e4 =>
        match expr_eqb e1 e2, expr_eqb e3 e4 with
          | Some b1, Some b2 => Some ((b1 && b2)%bool)
          | _, _ => None
        end
      | Abs t1 e1, Abs t2 e2 =>
        match expr_eqb e1 e2 with
          | Some b => Some ((t1 ?[ eq ] t2 && b)%bool)
          | None => None
        end
      | UVar u1, UVar u2 => Some (u1 ?[ eq ] u2)
      | _, _ => None
    end.

  Fixpoint remove (e lst : expr typ func) :=
    list_cases (e := lst) (fun _ => option (expr typ func))
               (fun _ _ _ _ => None)
               (fun _ _ x xs _ _ =>
                  match expr_eqb x e with
                    | Some true => Some xs
                    | Some false => 
                      match remove e xs with
                        | Some xs' => Some (mkCons tyNat x xs')
                        | None => None
                      end
                    | None => None
                  end) 
               None.

  Fixpoint cancel (lst1 lst2 : expr typ func) :=
    list_cases (e := lst1) (fun _ => option (expr typ func * expr typ func))
               (fun _ _ _ _ => Some (mkNil tyNat, lst2))
               (fun _ _ x xs _ _ =>
                  match remove x lst2 with
                    | Some lst2' => cancel xs lst2'
                    | None => 
                      match cancel xs lst2 with
                        | Some (lst1', lst2') => Some (mkCons tyNat x lst1', lst2')
                        | None => None
                      end
                  end)
               None.

End canceller.