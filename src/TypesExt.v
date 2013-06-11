Require Import List Bool.
Require Import Relations.Relation_Definitions.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Generic.
Require Import MirrorCore.Iso.

Set Implicit Arguments.
Set Strict Implicit.

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

    Existing Instance Functor_const.
    Existing Instance FunctorOk_const.
    Existing Instance IsoFunctor_Functor.
    Existing Instance IsoFunctorOk_Functor.
    Existing Instance IsoFunctor_compose.
    Existing Instance IsoFunctorOk_compose.
    Definition IsoFunctor_eta F (f : IsoFunctor F) : IsoFunctor (fun x => F x) :=
      {| isomap := fun _ _ f => isomap f |}.
    Definition IsoFunctorOk_eta F (f : IsoFunctor F) (fok : IsoFunctorOk f) : IsoFunctorOk (IsoFunctor_eta f).
    Proof.
      constructor.
      { intros; simpl. eapply isomap_id. }
      { intros; simpl. eapply isomap_flip. }
    Qed.
    Hint Immediate Functor_eta FunctorOk_eta IsoFunctor_eta IsoFunctorOk_eta : typeclass_instances.


  Section Equiv_compose.
    Variables A B C : Type.
    Variable F : Type -> Type.
    Variable eAB : Equiv A B.
    Variable eFT : Equiv (F B) C.
    Definition Equiv_compose : Equiv (F A) C.
    Proof.
      constructor; intros.
      constructor.
      { eapply eFT. eapply eAB. refine (fun x => x). }
      { eapply eFT. eapply eAB. refine (fun x => x). }
    Defined.

    Variable eokAB : EquivOk eAB.
    Variable eokFT : EquivOk eFT.
    Variable iF : IsoFunctor F.
    Variable iokF : IsoFunctorOk iF.

    Theorem EquivOk_compose : EquivOk Equiv_compose.
    Proof.
      Set Printing Implicit.
      constructor.
      { red; simpl; intros.
        assert (@IsoFunctorOk (fun Ty : Type => F0 (F Ty))
                              (@IsoFunctor_compose F0 func F iF)).
        { simple eapply IsoFunctorOk_compose; eauto with typeclass_instances. }
        assert (@IsoFunctorOk (fun _ : Type => F0 (F A))
                              (@IsoFunctor_Functor (fun _ : Type => F0 (F A)) (Functor_const (F0 (F A))))).
        { eapply IsoFunctorOk_Functor; eauto with typeclass_instances. }
        assert (@IsoFunctorOk (fun _ : Type => F A)
                              (@IsoFunctor_Functor (fun _ : Type => F A) (Functor_const (F A)))).
        { eapply IsoFunctorOk_Functor; eauto with typeclass_instances. }
        repeat  match goal with
                 | |- appcontext [ @into _ _ (@siso _ _ ?E ?X) ?Y ] => 
                   let x := constr:(@into _ _ (@siso _ _ E X) Y) in
                   let y := constr:(sinto (iso := E) X Y) in
                   change x with y
               end;
        repeat (   (erewrite sinto_app; eauto with typeclass_instances)
                || (rewrite sinto_const; eauto with typeclass_instances)
                || (rewrite soutof_const; eauto with typeclass_instances)
                || (erewrite sinto_soutof; eauto with typeclass_instances)
                || (erewrite soutof_sinto; eauto with typeclass_instances)).
(*        assert (forall F1 : Type -> Type, Iso (F1 A) (F1 B)).
        { intros. eapply siso. eassumption.

eapply typ0_isoOk. *)
        assert (forall F0 : Type -> Type,
                                Iso (F0 (F A)) (F0 C)).
        { intros. eapply eFT. eapply eAB. eapply Iso_ident. }
        Show Proof.
         generalize (@dist_over (F A) C _ _ F0 func _); intro.
         
         
        
        
}

        admit. }
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
    { generalize (typ1_iso ts typ0). generalize (typ0_iso ts).
      generalize dependent (typD ts).
      generalize dependent (typ0). generalize dependent (typ1).
      clear; intros.
 
    { apply typ1_iso. apply typ0_iso. refine (fun x => x). }
    { apply typ1_iso. apply typ0_iso. refine (fun x => x). }
    { apply typ1_iso. apply caseElse. }
    Defined.



    Global Instance TypInstance0_Ok_app F T f t (func : IsoFunctor F) (funcOk : IsoFunctorOk func)
           (fok : @TypInstance1_Ok F f) (tok : @TypInstance0_Ok T t)
    : TypInstance0_Ok (TypInstance0_app f t).
    Proof.
      constructor.
      { simpl; intros.
        Typeclasses eauto := debug.
        erewrite typ1_match_typ1; eauto.
        erewrite typ0_match_typ0; eauto with typeclass_instances. 
        generalize dependent (caseTyp tt).
        clear caseElse caseTyp.
        generalize dependent (R (typ1 typ0)).
        Arguments into {_ _} _ _ : rename.
        Arguments outof {_ _} _ _ : rename.
        unfold sinto. simpl.
        intros.
        repeat match goal with
                 | |- context [ into (@siso _ _ ?E ?X) ?Y ] => 
                   change (into (@siso _ _ E X) Y) with (sinto (iso := E) X Y)
               end.
        
        generalize (@sinto_app _ _ _ (typ1_isoOk ts typ0) (fun _ => T0 (F T)) T0 _ _ _ _); intro.
        generalize (@sinto_app _ _ _ (typ0_isoOk ts) (fun _ => T0 (F T)) (fun x => T0 (F x)) _ (IsoFunctor_compose _ _) _ _); intro.
        repeat match goal with
                 | |- context [ into (@siso _ _ ?E ?X) ?Y ] => 
                   change (into (@siso _ _ E X) Y) with (sinto (iso := E) X Y)
               end.
        unfold sinto in H0; rewrite H0.
        repeat match goal with
                 | |- context [ into (@siso _ _ ?E ?X) ?Y ] => 
                   change (into (@siso _ _ E X) Y) with (sinto (iso := E) X Y)
               end.
        f_equal.
        rewrite H1.
        repeat rewrite soutof_const. reflexivity. }
      { simpl; intros.
        unfold TypInstance0_app.

 constructor.
        { admit. }
        { 

        
        Print sinto.
        


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
