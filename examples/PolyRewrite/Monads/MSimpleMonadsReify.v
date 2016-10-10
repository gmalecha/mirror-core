Require Import Coq.Lists.List.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.Lambda.ExprCore.
Require Import McExamples.PolyRewrite.MSimpleMonads.
Require Import ExtLib.Structures.Monad.

(* Notes from Greg
   "OnGoal" tactic. Inspect goal, and use same functions from rewriter *)

(* Catch-all for things that fail to reify *)
Definition otherFunc : BinNums.positive -> expr typ func :=
  fun _ => Inj (N 0).
Opaque otherFunc.

Module Type Monad.
  Parameter M : Type -> Type.
End Monad.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Module RMonad (MM : Monad).

  (** Declare patterns (cannot be done inside section) **)
  Reify Declare Patterns patterns_simplemon_typ : typ.
  Reify Declare Patterns patterns_simplemon : (expr typ func).
  Reify Declare Typed Table table_terms : BinNums.positive => typ.

  (* We should see if they can go in module *)
  Reify Pattern patterns_simplemon_typ += (!! nat)  => (tyBase0 tyNat).
  Reify Pattern patterns_simplemon_typ += (!! bool) => (tyBase0 tyBool).
  Reify Pattern patterns_simplemon_typ += (!! Prop) => (@tyProp typ').
  Reify Pattern patterns_simplemon += (@RGet 0 RConst) => (fun (n : @id nat) => @Inj typ func (N n)).
  Reify Pattern patterns_simplemon += (!! plus) => (Inj (typ:=typ) Plus).
  Reify Pattern patterns_simplemon += (!! NPeano.Nat.ltb) => (Inj (typ:=typ) Lt).
  Reify Pattern patterns_simplemon += (!! and) => (Inj (typ:=typ) And).
  Reify Pattern patterns_simplemon += (!! or) => (Inj (typ:=typ) Or).
  Reify Pattern patterns_simplemon += (!! Basics.impl) => (Inj (typ:=typ) Impl).

  (* += doesn't restrict. but the pattern you're matching on must be closed... *)
  Import MM.

  (* Used so the user can reify the specific monad she wants *)
  Reify Declare Patterns patterns_simplemon_typ_special : typ.

  (* exactly option applied to ?0 goes to function reify_typ -> *)
  Reify Declare Syntax reify_simplemon_typ :=
    CFix
      (CFirst
         (CPattern (ls := _ :: _ :: nil) (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) (fun (a b : function (CRec 0)) => tyArr a b) ::
         @CPatterns typ patterns_simplemon_typ ::
         @CPatterns typ patterns_simplemon_typ_special ::
         nil)).

  (** Declare syntax **)
  Reify Declare Syntax reify_simplemon :=
    CFix
      (CFirst (CPatterns patterns_simplemon ::
                         CApp (CRec 0) (CRec 0) (@ExprCore.App typ func) ::
                         CAbs (CCall reify_simplemon_typ) (CRec 0) (@ExprCore.Abs typ func) ::
                         CVar (@ExprCore.Var typ func) ::

                         CPattern (ls := _ :: nil) (!! (@eq) @ ?0)
                         (fun (t : function (CCall reify_simplemon_typ)) => Inj (typ:=typ) (Eq t)) ::

                         CPattern (ls := _ :: _ :: nil) (RPi (?0) (?1))
                         (fun (t : function (CCall reify_simplemon_typ)) (b : function (CRec 0)) =>
                            (App (Inj (All t)) (Abs (func:=func) t b))) ::

                         CPattern (ls :=  _ :: nil) (!! (@ex) @ ?0)
                         (fun (t : function (CCall reify_simplemon_typ)) => Inj (typ := typ) (Ex t)) ::

                         (* First 2 parameters : M, Monad instance for M  *)
                         CPattern (ls := _ :: nil) (!! (@ret) @ # @ # @ ?0)
                         (fun t : function (CCall reify_simplemon_typ) => Inj (typ := typ) (Ret t)) ::

                         (* First 2 parameters : M, Monad instance for M  *)
                         CPattern (ls := _ :: _ :: nil) (!! (@bind) @ # @ # @ ?0 @ ?1)
                         (fun t u : function (CCall reify_simplemon_typ) => Inj (typ := typ) (Bind t u)) ::
                         
                         CMap otherFunc (CTypedTable (CCall reify_simplemon_typ) table_terms)
                         :: nil)).

  Instance Reify_expr_simple : Reify (expr typ func) :=
    { reify_scheme := CCall reify_simplemon }.

  Instance Reify_simple_type : Reify typ :=
    { reify_scheme := CCall reify_simplemon_typ }.
End RMonad.


(* using Option as our monad *)
Module MonadOption <: Monad.
                       Definition M := option.
End MonadOption.

Module RMonadOption := RMonad MonadOption.
Import RMonadOption.

Reify Pattern patterns_simplemon_typ_special += (!! (@option) @ ?0) => (fun (x : function (CCall reify_simplemon_typ)) => tyBase1 tyMonad x).

(*
Definition reify_option_typ : Command (mtyp typ') :=
  CFix
    (CFirst
       ((CPattern (ls := _ :: nil) (!! option @ ?0) (fun x : function (CRec 0) => tyBase1 tyMonad x)) ::
        (CCall reify_simplemon_typ) ::
         nil)).
*)                              

Ltac reify_typ trm :=
  let k e :=
      refine e
  in
  (* originally reify_simplemon_typ *)
  reify_expr (CCall reify_simplemon_typ) k [[ True ]] [[ trm ]].

Ltac reify trm :=
  let k e :=
      refine e
  in
  reify_expr (CCall reify_simplemon) k [[ True ]] [[ trm ]].

Ltac reify_simple trm k :=
  reify_expr (CCall reify_simplemon) k [[ True ]] [[ trm ]].

Definition test_typ : typ.
                          reify_typ (nat -> nat).
Defined.
Print test_typ.

(* Order tables *)

Definition test_montyp : typ.
                           reify_typ (nat -> option nat).
Defined.
Print test_montyp.

Definition test_typ_2 : typ.
                          reify_typ ((nat -> nat) -> nat -> (nat -> nat -> nat -> nat)).
Defined.
Print test_typ_2.

Definition test_1 : expr typ func.
                      reify (0 = 0).
Defined.
Print test_1.

Definition test_2 : expr typ func.
                      reify ((NPeano.Nat.ltb 0 1) = (NPeano.Nat.ltb 0 0)).
Defined.
Print test_2.

Definition test_3 : expr typ func.
                      reify ((fun x => x) 1).
Defined.
Print test_3.

Definition test_4 : expr typ func.
                      reify ((fun x => x) 1).
Defined.
Print test_4.

Definition test_5 : expr typ func.
                      reify ((fun x y => x) 1 3).
Defined.
Print test_5.

Definition test_6 : expr typ func.
                      reify ((fun x : nat => x) = (fun y : nat => y)).
Defined.
Print test_6.

Definition test_7 : expr typ func.
                      reify (forall x : nat, 1 = 1 -> (x + 1) = 1).
Defined.
Print test_7.

(** Something that doesn't fit **)
Definition id T (x : T) : T := x.

Definition test_fail : expr typ func.
                         reify (id nat 0).
Defined.
Print test_fail.

Definition foo : nat := 6.

Reify Seed Typed Table table_terms += 1 => [[ MSimpleMonads.tyNat , foo ]].

Definition test_table : expr typ func.
                          reify (foo).
Defined.
Print test_table.
