Require Import List Bool.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Generic.

Set Implicit Arguments.
Set Strict Implicit.

Class Iso (A B : Type) : Type :=
{ into : A -> B
; outof : B -> A
}.

Class RType (typ : Type) (typD : list Type -> typ -> Type) : Type :=
{ typ_cast : forall env (a b : typ), option (typD env a -> typD env b)
; eqb : forall ts (t : typ), (forall a b : typD ts t, option bool)
; typeFor : forall ts (t : typ), type (typD ts t)
; instantiate_typ : list typ -> typ -> typ
; type_of_apply : forall (tv : typ) (es : list typ), option typ
; type_apply : forall (n : nat) (ls : list typ) (acc : list Type) (t : typ),
                 parametric n acc (fun env : list Type => typD env t) ->
                 option (typD acc (instantiate_typ (rev ls) t))
}.

Class RTypeOk typ typD (RType_typ : @RType typ typD) : Type :=
{ eqb_ok : forall ts t a b,
             match eqb ts t a b with
               | None => True
               | Some true => equal (type := typeFor _ t) a b
               | Some false => ~equal (type := typeFor _ t) a b
             end
; typ_cast_iso : forall ts a b f, 
    typ_cast ts a b = Some f ->
    exists g, 
      typ_cast ts b a = Some g /\
      (forall x, f (g x) = x)
; typ_cast_refl : forall ts t, 
                    exists f, typ_cast ts t t = Some f /\
                              (forall x, f x = x)
(*
; type_of_apply_nil : forall t, type_of_apply t nil = Some t
; type_of_apply_cons : forall t t' t'' ts, 
  type_of_apply t (Some t' :: ts) = Some t'' <-> 
*)  
}.

Section typed.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  
(* You can't write the generic version of this
  Class TypInstance (n : nat) (F : quant Type n) : Type :=
  { ctor     : quant typ n
(*  ; ctor_iso : @parametric typ n nil (fun ls => let ls := rev ls in
                                                match qapply n ls ctor , qapply n (map typD ls) F with
                                                  | None , None => unit
                                                  | Some t , Some t' => Iso t' (typD t)
                                                  | _ , _ => Empty_set
                                                end)
*)
  ; ctor_match : forall (R : typ -> Type -> Type)
      (caseCtor : forall args : vector typ n, R (qapply_v _ n args ctor) (typD (qapply_v _ n args ctor)))
      (caseElse : forall t : typ, R t (typD t))
      (t : typ), R t (typD t)
  }.
*)

  Class TypInstance0 (F : Type) : Type :=
  { ctor0     : typ
  ; ctor0_iso : forall ts, Iso F (typD ts ctor0)
  ; ctor0_match : forall ts (R : typ -> Type -> Type)
      (caseCtor : unit -> R ctor0 F)
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance1 (F : Type -> Type) : Type :=
  { ctor1     : typ -> typ
  ; ctor1_iso : forall ts t, Iso (F (typD ts t)) (typD ts (ctor1 t))
  ; ctor1_match : forall ts (R : typ -> Type -> Type)
      (caseCtor : forall t, R (ctor1 t) (typD ts (ctor1 t)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance2 (F : Type -> Type -> Type) : Type :=
  { ctor2     : typ -> typ -> typ
  ; ctor2_iso : forall ts t1 t2, Iso (F (typD ts t1) (typD ts t2)) (typD ts (ctor2 t1 t2))
  ; ctor2_match : forall ts (R : typ -> Type -> Type)
      (caseCtor : forall t1 t2, R (ctor2 t1 t2) (typD ts (ctor2 t1 t2)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.


End typed.  

