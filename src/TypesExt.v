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

Class StrongIso (A B : Type) : Type :=
{ sinto : forall (P : Type -> Type), P A -> P B
; soutof : forall (P : Type -> Type), P B -> P A
}.

Class StrongIsoOk A B (SIso : StrongIso A B) : Type :=
{ into_outof : forall R x,
  sinto R (soutof R x) = x
; outof_into : forall R x,
  soutof R (sinto R x) = x
}.

Arguments sinto {_ _} {iso} P _ : rename.
Arguments soutof {_ _} {iso} P _ : rename.

Class RType (typ : Type) (typD : list Type -> typ -> Type) : Type :=
{ typ_cast : forall (F : Type -> Type) env (a b : typ), option (F (typD env a) -> F (typD env b))
; typ_eqb : typ -> typ -> bool
; eqb : forall ts (t : typ), (forall a b : typD ts t, option bool)
; typeFor : forall ts (t : typ), type (typD ts t)
; instantiate_typ : list typ -> typ -> typ
; type_of_apply : forall (tv : typ) (es : list (option typ)), option typ
; type_apply : forall (n : nat) (ls : list typ) (acc : list Type) (t : typ),
                 parametric n acc (fun env : list Type => typD env t) ->
                 option (typD acc (instantiate_typ (rev ls) t))
}.

Class RTypeOk typ typD (RType_typ : @RType typ typD) : Type :=
{ (** eqb **)
  eqb_ok : forall ts t a b,
             match eqb ts t a b with
               | None => True
               | Some true => equal (type := typeFor _ t) a b
               | Some false => ~equal (type := typeFor _ t) a b
             end
  (** typ_eqb **)
; typ_eqb_ok : forall a b, typ_eqb a b = true -> a = b
  (** typ_cast **)
; typ_cast_iso : forall F ts a b f, 
    typ_cast F ts a b = Some f ->
    exists g, 
      typ_cast F ts b a = Some g /\
      (forall x, f (g x) = x)
; typ_cast_refl : forall ts t F, 
                    exists f, typ_cast F ts t t = Some f /\
                              (forall x, f x = x)
  (** type_of_apply **)
; type_of_apply_nil : forall t, type_of_apply t nil = Some t
; type_of_apply_cons : forall t t' t'' ts ts', 
  type_of_apply t (Some t' :: ts) = Some t'' ->
  exists T, typD ts' t = (typD ts' t' -> typD ts' T) /\
            type_of_apply T ts = Some t''  
; type_of_apply_None_cons : forall t ts, 
  type_of_apply t (None :: ts) = None
  (** instantiate_typ **)
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
  { typ0     : typ
  ; typ0_iso : forall ts, StrongIso F (typD ts typ0)
  ; typ0_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : unit -> R typ0 F)
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance0_Ok F (ti : TypInstance0 F) : Type :=
  { typ0_match_typ0 : forall ts R caseTyp caseElse,
      (typ0_match ts R caseTyp caseElse typ0) = sinto (iso := typ0_iso ts) _ (caseTyp tt)
  ; typ0_isoOk : forall ts, StrongIsoOk (typ0_iso ts)
  }.

  Class TypInstance1 (F : Type -> Type) : Type :=
  { typ1     : typ -> typ
  ; typ1_iso : forall ts t,
                  StrongIso (F (typD ts t)) (typD ts (typ1 t))
  ; typ1_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : forall t, R (typ1 t) (F (typD ts  t)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance1_Ok F (ti : TypInstance1 F) : Type :=
  { typ0_match_typ1 : forall ts R caseTyp caseElse t,
      (typ1_match ts R caseTyp caseElse (typ1 t)) = sinto (iso := typ1_iso ts t) _ (caseTyp t)
  ; typ1_isoOk : forall ts t, StrongIsoOk (typ1_iso ts t)
  }.

  Class TypInstance2 (F : Type -> Type -> Type) : Type :=
  { typ2     : typ -> typ -> typ
  ; typ2_iso : forall ts t1 t2, 
                  StrongIso (F (typD ts t1) (typD ts t2)) (typD ts (typ2 t1 t2))
  ; typ2_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : forall t1 t2, R (typ2 t1 t2) (F (typD ts t1) (typD ts t2)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance2_Ok F (ti : TypInstance2 F) : Type :=
  { typ2_match_typ2 : forall ts R caseTyp caseElse t u,
      (typ2_match ts R caseTyp caseElse (typ2 t u)) = sinto (iso := typ2_iso ts t u) _ (caseTyp t u)
  ; typ2_isoOk : forall ts t u, StrongIsoOk (typ2_iso ts t u)
  }.

  Section instances.
    Global Instance TypInstance0_app F T 
           (f : TypInstance1 F) (t : TypInstance0 T)
    : TypInstance0 (F T) :=
    { typ0 := typ1 typ0
    ; typ0_iso := fun ts => {| sinto := fun _ => _ ; soutof := fun _ => _ |}
    ; typ0_match := fun ts R caseTyp caseElse t =>
        typ1_match ts R (fun t' => 
                           typ0_match ts (fun ty Ty => R (typ1 ty) (F Ty)) 
                                      caseTyp
                                      (fun _ => _) t') caseElse t 
    }.
    { apply typ1_iso. apply typ0_iso. refine (fun x => x). }
    { apply typ1_iso. apply typ0_iso. refine (fun x => x). }
    { apply typ1_iso. apply caseElse. }
    Defined.

    Global Instance TypInstance0_app2 F T1 T2 
           (f : TypInstance2 F) (t1 : TypInstance0 T1) (t2 : TypInstance0 T2) 
    : TypInstance0 (F T1 T2) :=
    { typ0 := typ2 (typ0 (TypInstance0 := t1)) (typ0 (TypInstance0 := t2))
    ; typ0_iso := fun ts => {| sinto := fun _ => _ ; soutof := fun _ => _ |}
    ; typ0_match := fun ts R caseTyp caseElse t =>
        typ2_match ts R 
           (fun t1' t2' => 
              typ0_match (TypInstance0 := t1) ts 
                 (fun ty Ty => R (typ2 ty t2') (F Ty (typD ts t2')))
                 (fun _ =>
                    typ0_match (TypInstance0 := t2) ts
                        (fun ty Ty => R (typ2 (typ0 (TypInstance0 := t1)) ty)
                                        (F T1 Ty))
                        caseTyp
                        (fun _ => _)
                        t2')
                 (fun _ => _)
                 t1') caseElse t

    }.
    { apply typ2_iso. apply typ0_iso. apply typ0_iso. refine (fun x => x). }
    { apply typ2_iso. apply typ0_iso. apply typ0_iso. refine (fun x => x). }
    { eapply (soutof (iso := typ0_iso ts) (fun x => R (typ2 typ0 t0) (F x (typD ts t0)))). 
      eapply (soutof (iso := typ2_iso ts _ _) _).
      apply caseElse. }
    { eapply (soutof (iso := typ2_iso ts _ _) _). 
      apply caseElse. }
    Defined.

  End instances.

End typed.  
