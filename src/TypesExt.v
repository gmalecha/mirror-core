Require Import List Bool.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Generic.
Require Import MirrorCore.Iso.
Require Import MirrorCore.IsoTac.

Set Implicit Arguments.
Set Strict Implicit.

(** AXIOMS **)
Require Import FunctionalExtensionality.

Class RType (typ : Type) (typD : list Type -> typ -> Type) : Type :=
{ typ_cast : forall (F : Type -> Type) env (a b : typ), 
               option (F (typD env a) -> F (typD env b))
; typ_eqb :> RelDec (@eq typ)
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
; typ_eqb_ok :> RelDec_Correct typ_eqb
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
  ; typ0_iso : forall ts, Equiv F (typD ts typ0)
  ; typ0_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : unit -> R typ0 F)
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance0_Ok F (ti : TypInstance0 F) : Type :=
  { typ0_match_typ0 : forall ts R caseTyp caseElse (f : IsoFunctor (R typ0)), IsoFunctorOk f ->
      (typ0_match ts R caseTyp caseElse typ0) = sinto (iso := typ0_iso ts) _ (caseTyp tt)
  ; typ0_isoOk : forall ts, EquivOk (typ0_iso ts)
  }.

  Class TypInstance1 (F : Type -> Type) : Type :=
  { typ1     : typ -> typ
  ; typ1_iso : forall ts t,
                  Equiv (F (typD ts t)) (typD ts (typ1 t))
  ; typ1_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : forall t, R (typ1 t) (F (typD ts  t)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance1_Ok F (ti : TypInstance1 F) : Type :=
  { typ1_match_typ1 : forall ts R caseTyp caseElse t (f : IsoFunctor (R (typ1 t))), IsoFunctorOk f ->
      (typ1_match ts R caseTyp caseElse (typ1 t)) = sinto (iso := typ1_iso ts t) _ (caseTyp t)
  ; typ1_isoOk : forall ts t, EquivOk (typ1_iso ts t)
  }.

  Class TypInstance2 (F : Type -> Type -> Type) : Type :=
  { typ2     : typ -> typ -> typ
  ; typ2_iso : forall ts t1 t2, 
                  Equiv (F (typD ts t1) (typD ts t2)) (typD ts (typ2 t1 t2))
  ; typ2_match : forall ts (R : typ -> Type -> Type)
      (caseTyp : forall t1 t2, R (typ2 t1 t2) (F (typD ts t1) (typD ts t2)))
      (caseElse : forall t : typ, R t (typD ts t))
      (t : typ), R t (typD ts t)
  }.

  Class TypInstance2_Ok F (ti : TypInstance2 F) : Type :=
  { typ2_match_typ2 : forall ts R caseTyp caseElse t u,
      (typ2_match ts R caseTyp caseElse (typ2 t u)) = sinto (iso := typ2_iso ts t u) _ (caseTyp t u)
  ; typ2_isoOk : forall ts t u, EquivOk (typ2_iso ts t u)
  }.

  Theorem compose_into_into_Iso_compose : forall A B C (iAB : Iso A B) (iBC : Iso B C),
                                            compose (@into _ _ iBC) (@into _ _ iAB) =
                                            @into _ _ (Iso_compose iBC iAB).
  Proof. reflexivity. Qed.
  Theorem compose_outof_outof_Iso_compose : forall A B C (iAB : Iso A B) (iBC : Iso B C),
                                              compose (@outof _ _ iAB) (@outof _ _ iBC) =
                                              @outof _ _ (Iso_compose iBC iAB).
  Proof. reflexivity. Qed.

  Theorem Iso_ext : forall A B (iAB : Iso A B),
                      {| into := into ; outof := outof |} = iAB.
  Proof. destruct iAB; auto. Qed.

  Section Equiv_compose.
    Variables A B C : Type.
    Variable F : Type -> Type.
    Variable eAB : Equiv A B.
    Variable eFT : Equiv (F B) C.
    Definition Equiv_compose : Equiv (F A) C :=
    {| siso := fun F' => {| into := fun x => 
                                      sinto (iso := eFT) F' (sinto (iso := eAB) (fun x => F' (F x)) x)
                          ; outof := fun x => 
                                       soutof (iso := eAB) (fun x => F' (F x)) (soutof (iso := eFT) F' x) |} |}.

    Variable eokAB : EquivOk eAB.
    Variable eokFT : EquivOk eFT.
    Variable iF : IsoFunctor F.
    Variable iokF : IsoFunctorOk iF.

    Theorem EquivOk_compose : EquivOk Equiv_compose.
    Proof.
      Set Printing Implicit.
      constructor.
      { red; simpl; intros.
        unfold sinto, soutof.
        repeat match goal with
                 | |- appcontext [ fun x => @into _ _ ?F (@into _ _ ?G x) ] =>
                   change (fun x => @into _ _ F (@into _ _ G x)) with (compose (@into _ _ F) (@into _ _ G))
                 | |- appcontext [ fun x => @outof _ _ ?F (@outof _ _ ?G x) ] =>
                   change (fun x => @outof _ _ F (@outof _ _ G x)) with (compose (@outof _ _ F) (@outof _ _ G))
               end.
        repeat rewrite compose_into_into_Iso_compose.
        repeat rewrite compose_outof_outof_Iso_compose.
        repeat rewrite Iso_ext. 
        rewrite <- isomap_compose.
        f_equal.
        { eapply dist_over; eauto with typeclass_instances. }
        { eapply (fun y => @dist_over (F A) (F B) (fun F' => @siso A B eAB (fun x : Type => F' (F x))) y F0 _ _).
          destruct eokAB. red. red in siso_dist.
          intros. 
          assert (@IsoFunctorOk (fun x : Type => F1 (F x)) (@IsoFunctor_compose F1 F func0 iF)).
          eauto with typeclass_instances.
          specialize (siso_dist (fun x => F1 (F x)) _ H).
          etransitivity. 2: eapply siso_dist.
          simpl. f_equal.
          symmetry. eapply dist_over. eauto. } }
      { unfold Equiv_compose. constructor; intros; simpl;
        repeat  match goal with
                 | |- appcontext [ @into _ _ (@siso _ _ ?E ?X) ?Y ] => 
                   let x := constr:(@into _ _ (@siso _ _ E X) Y) in
                   let y := constr:(sinto (iso := E) X Y) in
                   change x with y
               end; 
        repeat (   (erewrite sinto_app; eauto with typeclass_instances)
                || (rewrite sinto_const; eauto)
                || (rewrite soutof_const; eauto)
                || (erewrite sinto_soutof; eauto with typeclass_instances)
                || (erewrite soutof_sinto; eauto with typeclass_instances)). }
    Qed.
  End Equiv_compose.
        

  Section instances.
    Global Instance TypInstance0_app F T 
           (f : TypInstance1 F) (t : TypInstance0 T)
    : TypInstance0 (F T) :=
    { typ0 := typ1 typ0
    ; typ0_iso := fun ts => _ (* {| siso := fun F => {| into := _ ; outof := _ |} |} *)
    ; typ0_match := fun ts R caseTyp caseElse t =>
        typ1_match ts R (fun t' => 
                           typ0_match ts (fun ty Ty => R (typ1 ty) (F Ty)) 
                                      caseTyp
                                      (fun _ => _) t') caseElse t 
    }.
    { eapply Equiv_compose. eapply typ0_iso. eapply typ1_iso. }
    { apply typ1_iso. apply caseElse. }
    Defined.

    Global Instance TypInstance0_Ok_app F T f t (func : IsoFunctor F) (funcOk : IsoFunctorOk func)
           (fok : @TypInstance1_Ok F f) (tok : @TypInstance0_Ok T t)
    : TypInstance0_Ok (TypInstance0_app f t).
    Proof.
      constructor.
      { simpl; intros.
        erewrite typ1_match_typ1; eauto.
        erewrite typ0_match_typ0; eauto with typeclass_instances. }
      { intros. eapply EquivOk_compose; eauto with typeclass_instances.
        eapply typ0_isoOk.
        eapply typ1_isoOk. }
    Qed.

    Global Instance TypInstance0_app2 F T1 T2 
           (f : TypInstance2 F) (t1 : TypInstance0 T1) (t2 : TypInstance0 T2) 
    : TypInstance0 (F T1 T2) :=
    { typ0 := typ2 (typ0 (TypInstance0 := t1)) (typ0 (TypInstance0 := t2))
    ; typ0_iso := fun ts => {| siso := fun F => {| into := _ ; outof := _ |} |}
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
