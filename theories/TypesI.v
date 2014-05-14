Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.Iso.
Require Import MirrorCore.IsoTac.

Set Implicit Arguments.
Set Strict Implicit.

Class RType (typ : Type) (typD : list Type -> typ -> Type) : Type :=
{ type_cast : forall env (a b : typ),
               option (forall F, F (typD env a) -> F (typD env b))
  (** It would be a little bit more modular to avoid
   ** syntactic equality in favor of semantic equality
   ** which is supported by [type_cast]
   **)
; type_eqb :> RelDec (@eq typ)
  (** This function gives the appropriate equivalence
   ** relation defined on this type.
   ** ----- Currently Unused -------
   **)
; typeFor : forall ts (t : typ), type (typD ts t)
}.

Class RTypeOk typ typD (RType_typ : @RType typ typD) : Type :=
{ (** typ_eqb **)
  type_eqb_ok :> RelDec_Correct type_eqb
  (** typ_cast induces an equivalence relation **)
; type_cast_refl : forall ts t,
                    exists f, type_cast ts t t = Some f /\
                              (forall F x, f F x = x)
; type_cast_sym : forall ts a b f,
    type_cast ts a b = Some f ->
    exists g,
      type_cast ts b a = Some g /\
      (forall F x, f F (g F x) = x)
; type_cast_trans : forall ts a b c f g,
    type_cast ts a b = Some f ->
    type_cast ts b c = Some g ->
    exists h,
      type_cast ts a c = Some h /\
      (forall F x, g F (f F x) = h F x)
}.

Class RTypeEq (typ : Type) (typD : list Type -> typ -> Type) : Type :=
{ eqb : forall ts (t : typ), (forall a b : typD ts t, option bool) }.

Class RTypeEqOk typ typD (RType_typ : @RType typ typD) (RTE : RTypeEq typD) : Type :=
{ eqb_ok : forall ts t a b,
             match eqb ts t a b with
               | None => True
               | Some true => equal (type := typeFor _ t) a b
               | Some false => ~equal (type := typeFor _ t) a b
             end
}.

(** TODO: The big question here is whether it is easier to reason about
 ** [match] or something that produces an option (with the appropriate cast?)
 **)
Section typed.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.

(* You can't write the generic version of this due to universe issues
  Class TypInstance (n : nat) (F : quant Type n) : Type :=
  { ctor     : quant typ n
  ; ctor_iso : @parametric typ n nil (fun ls => let ls := rev ls in
        match qapply n ls ctor , qapply n (map typD ls) F with
          | None , None => unit
          | Some t , Some t' => Iso t' (typD t)
          | _ , _ => Empty_set
        end)
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
  ; typ2_match : forall ts (t : typ) (R : typ -> Type -> Type)
      (caseTyp : forall t1 t2, R (typ2 t1 t2) (F (typD ts t1) (typD ts t2)))
      (caseElse : forall t : typ, R t (typD ts t)),
      R t (typD ts t)
  ; typ2_matchW : forall ts (t : typ) (R : Type -> Type)
      (caseTyp : forall t1 t2, R (F (typD ts t1) (typD ts t2)))
      (caseElse : unit -> R (typD ts t)),
      R (typD ts t)
  }.

  Class TypInstance2_Ok F (ti : TypInstance2 F) : Type :=
  { typ2_match_typ2 : forall ts R caseTyp caseElse t u,
      (typ2_match ts (typ2 t u) R caseTyp caseElse) = sinto (iso := typ2_iso ts t u) _ (caseTyp t u)
  ; typ2_matchW_typ2 : forall ts R t u caseTyp caseElse,
      (typ2_matchW ts (typ2 t u) R caseTyp caseElse) = sinto (iso := typ2_iso ts t u) _ (caseTyp t u)
  ; typ2_matchW_case : forall ts t,
      (exists l r (pf : Equiv (typD ts t) (F (typD ts l) (typD ts r))),
         EquivOk pf /\
         forall R caseType caseElse,
           typ2_matchW ts t R caseType caseElse =
           soutof (iso := pf) (fun X => R X) (caseType l r)) \/
      (forall R caseType caseElse,
         typ2_matchW ts t R caseType caseElse = caseElse tt)
  ; typ2_isoOk : forall ts t u, EquivOk (typ2_iso ts t u)
  ; typ2_match_cast_type : forall ts ta tb cast,
                             type_cast ts ta tb = Some cast ->
                             forall R,
                               typ2_matchW ts tb R =
                               cast (fun T => _ -> (unit -> R T) -> R T)
                                    (typ2_matchW ts ta R)
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
      fun F' => {| into := fun x =>
                             sinto (iso := eFT) F' (sinto (iso := eAB) (fun x => F' (F x)) x)
                 ; outof := fun x =>
                              soutof (iso := eAB) (fun x => F' (F x)) (soutof (iso := eFT) F' x) |}.

    Variable eokAB : EquivOk eAB.
    Variable eokFT : EquivOk eFT.
    Variable iF : IsoFunctor F.
    Variable iokF : IsoFunctorOk iF.

    Theorem EquivOk_compose : EquivOk Equiv_compose.
    Proof.
      Set Printing Implicit.
      constructor.
      { red; simpl; intros.
        unfold Equiv_compose, sinto, soutof, siso.
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
    ; typ0_iso := fun ts => fun F => {| into := _ ; outof := _ |}
    ; typ0_match := fun ts R caseTyp caseElse t =>
        typ2_match ts t R
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
                 t1') caseElse

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
