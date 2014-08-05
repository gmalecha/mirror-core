Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.

  (** NOTE: Fewer parameters is better, but pulling [typ] to the top
   ** means that I can modularize the expression langauge and avoid
   ** type parameters in a lot of places
   **)
  Class RType : Type :=
  { (** NOTE: This must be decidable if [exprD] will respect it.
     **)
    typD : list Type -> typ -> Type
(*
    (** NOTE: weakening is not implementable unless types are strongly typed **)
  ; type_weaken : forall ts t, typD nil t -> typD ts t
*)
  ; tyAcc : typ -> typ -> Prop
    (** NOTE: Everything below here is fixed! **)
  ; Rty : list Type -> typ -> typ -> Prop := fun _ => @eq typ
  ; type_cast : forall env (a b : typ), option (Rty env a b)
    (* NOTE: I can't make this dependent b/c it exposes the
     * underlying syntactic types, which do not have to be equal.
     *
     * The solution is to require that the function respects [Rty].
     *)
  ; Relim : forall {ts} (F : Type -> Type) {to from}
                   (pf : Rty ts to from),
              F (typD ts from) ->
              F (typD ts to) :=
      fun ts F to from pf =>
        match pf in _ = t return F (typD ts t) -> F (typD ts to) with
          | eq_refl => fun x => x
        end
  ; Rrefl : forall ts x, Rty ts x x :=
      fun _ => @eq_refl _
  ; Rsym : forall {ts x y}, Rty ts y x -> Rty ts x y :=
      fun _ x y pf => eq_sym pf
  ; Rtrans : forall {ts x y z}, Rty ts x y -> Rty ts y z -> Rty ts x z :=
      fun _ => @eq_trans _
  }.

  Variable RType_typ : RType.

  Class RTypeOk  : Type :=
  { Relim_refl
    : forall ts t F (val : F (typD ts t)),
        Relim F (Rrefl ts t) val = val
  ; wf_tyAcc : well_founded tyAcc
  ; Relim_sym
    : forall ts t u (pf : Rty ts t u) F (val : F (typD ts t)),
        Relim F (Rsym pf) val =
        Relim (fun T => F T -> F _) pf (fun x => x) val
  ; Relim_trans
    : forall ts t u v (pf1 : Rty ts t u) (pf2 : Rty ts u v) F
             (val : F (typD ts v)),
        Relim F (Rtrans pf1 pf2) val =
        Relim F pf1 (Relim F pf2 val)
  ; type_cast_refl : forall env x, type_cast env x x = Some (Rrefl env x)
  ; type_cast_total : forall env x y,
                        type_cast env x y = None -> ~Rty env x y
  }.

  Global Instance RelDec_Rty ts : RelDec (Rty ts) :=
  { rel_dec := fun l r => match type_cast ts l r with
                            | None => false
                            | Some _ => true
                          end }.

  Global Instance RelDec_Correct_Rty {RTO : RTypeOk} ts
  : @RelDec_Correct _ (Rty ts) _.
  Proof.
    constructor. unfold rel_dec; simpl.
    intros. generalize (@type_cast_total _ ts x y).
    destruct (type_cast ts x y); intros.
    split; auto. intuition congruence.
  Qed.

  Section Typ0.
    Variable F : Type.

    Class Typ0 : Type :=
    { typ0 : typ
    ; typ0_cast : forall ts, typD ts typ0 = F
    ; typ0_match : forall (T : Type -> Type) ts t,
                     T F ->
                     T (typD ts t) ->
                     T (typD ts t)
    }.

    Class Typ0Ok (TI : Typ0) : Type :=
    { typ0_match_zeta
      : forall T ts tr fa,
          typ0_match T ts typ0 tr fa =
          match eq_sym (typ0_cast ts) in _ = t return T t with
            | eq_refl => tr
          end
    ; typ0_match_case
      : forall ts x,
          (exists (pf : Rty ts x typ0),
             forall T tr fa,
               typ0_match T ts x tr fa =
               Relim T pf
                     match eq_sym (typ0_cast ts) in _ = t return T t with
                       | eq_refl => tr
                     end) \/
          (forall T tr fa, typ0_match T ts x tr fa = fa)
    ; typ0_match_Proper
      : forall T ts t t' (pf : Rty ts t' t) tr fa,
          typ0_match T ts t tr fa =
          Relim T (Rsym pf) (typ0_match T ts t' tr (Relim T pf fa))
    }.
  End Typ0.

  Section Typ1.
    Variable F : Type -> Type.

    Class Typ1 : Type :=
    { typ1 : typ -> typ
    ; typ1_cast : forall ts a, typD ts (typ1 a) = F (typD ts a)
    ; typ1_match : forall (T : Type -> Type) ts t,
                     (forall a, T (F (typD ts a))) ->
                     T (typD ts t) ->
                     T (typD ts t)
    }.

    Class Typ1Ok (TI : Typ1) : Type :=
    { typ1_match_zeta
      : forall T ts a tr fa,
          typ1_match T ts (typ1 a) tr fa =
          match eq_sym (typ1_cast ts a) in _ = t return T t with
            | eq_refl => tr a
          end
    ; tyAcc_typ1 : forall a, tyAcc a (typ1 a)
    ; typ1_inj
      : forall ts a c,
          Rty ts (typ1 a) (typ1 c) ->
          Rty ts a c
    ; typ1_match_case
      : forall ts x,
          (exists d (pf : Rty ts x (typ1 d)),
             forall T tr fa,
               typ1_match T ts x tr fa =
               Relim T pf
                     (match eq_sym (typ1_cast ts d) in _ = t return T t with
                        | eq_refl => tr d
                      end)) \/
          (forall T tr fa, typ1_match T ts x tr fa = fa)
    ; typ1_match_Proper
      : forall T ts t t' (pf : Rty ts t' t) tr fa,
          typ1_match T ts t tr fa =
          Relim T (Rsym pf) (typ1_match T ts t' tr (Relim T pf fa))
    }.
  End Typ1.

  Section Typ2.
    Variable F : Type -> Type -> Type.

    Class Typ2 : Type :=
    { typ2 : typ -> typ -> typ
    ; typ2_cast : forall ts a b, typD ts (typ2 a b) = F (typD ts a) (typD ts b)
    ; typ2_match : forall (T : Type -> Type) ts t,
                     (forall a b, T (F (typD ts a) (typD ts b))) ->
                     T (typD ts t) ->
                     T (typD ts t)
    }.

    Class Typ2Ok (TI : Typ2) : Type :=
    { typ2_match_zeta
      : forall T ts a b tr fa,
          typ2_match T ts (typ2 a b) tr fa =
          match eq_sym (typ2_cast ts a b) in _ = t return T t with
            | eq_refl => tr a b
          end
    ; tyAcc_typ2L : forall a b, tyAcc a (typ2 a b)
    ; tyAcc_typ2R : forall a b, tyAcc a (typ2 b a)
    ; typ2_inj
      : forall ts a b c d,
          Rty ts (typ2 a b) (typ2 c d) ->
          Rty ts a c /\ Rty ts b d
    ; typ2_match_case
      : forall ts x,
          (exists d r (pf : Rty ts x (typ2 d r)),
             forall T tr fa,
               typ2_match T ts x tr fa =
               Relim T pf
                     (match eq_sym (typ2_cast ts d r) in _ = t return T t with
                        | eq_refl => tr d r
                      end)) \/
          (forall T tr fa, typ2_match T ts x tr fa = fa)
    ; typ2_match_Proper
      : forall T ts t t' (pf : Rty ts t' t) tr fa,
          typ2_match T ts t tr fa =
          Relim T (Rsym pf) (typ2_match T ts t' tr (Relim T pf fa))
    }.
  End Typ2.

  Section apps.
    Variables (F : Type -> Type -> Type) (G : Type -> Type) (X : Type).
    Context {T2 : Typ2 F} {T1 : Typ1 G} {T0 : Typ0 X}.

    Let typ0 := @typ0 _ T0.
    Let typ1 := @typ1 _ T1.
    Let typ2 := @typ2 _ T2.

    Definition Typ2_App : Typ1 (F X) :=
      @Build_Typ1 (F X)
                  (typ2 typ0)
                  (fun ts a =>
                     match eq_sym (typ2_cast (Typ2 := T2) ts typ0 a) in _ = T
                           return T = F X (typD ts a)
                     with
                       | eq_refl =>
                         match eq_sym (typ0_cast (Typ0 := T0) ts) in _ = T
                               return F T (typD ts a) = F X (typD ts a)
                         with
                           | eq_refl => eq_refl
                         end
                     end)
                  (fun T ts t0 tr fa =>
                     typ2_match (Typ2 := T2)
                                (fun t => T t -> T t)
                                ts t0
                                (fun a b fa' =>
                                   typ0_match (Typ0 := T0)
                                              (fun t => T (F (typD ts a) (typD ts b)) -> T (F t (typD ts b)))
                                              ts a
                                              (fun _ => tr b)
                                              (fun x => x) fa')
                                (fun _ => fa) fa).

    Context {Typ2Ok_T2 : Typ2Ok T2}.
    Context {Typ1Ok_T1 : Typ1Ok T1}.
    Context {Typ0Ok_T0 : Typ0Ok T0}.

    Theorem Typ1Ok_App : Typ1Ok Typ2_App.
    Proof.
      constructor.
      { simpl. intros.
        rewrite (typ2_match_zeta) by assumption.
        rewrite (typ0_match_zeta) by assumption.
        generalize (tr a). clear.
        match goal with
          | |- forall x,
                 match eq_sym ?X with _ => _ end _ =
                 match _ match eq_sym ?Y with _ => _ end with _ => _ end =>
            change Y with X ; generalize X
        end.
        match goal with
          | |- forall e x,
                 match _ with eq_refl => match eq_sym ?X with _ => _ end end _ =
                 match _ match _ with eq_refl => match eq_sym ?Y with _ => _ end end with _ => _ end =>
            change Y with X ; generalize X
        end.
        destruct e.
        simpl in *.
        unfold typ0.
        destruct e. reflexivity. }
      { unfold typed.typ1; simpl.
        intros. eapply tyAcc_typ2R; eauto. }
      { intros. unfold typed.typ1 in H. simpl in H.
        eapply typ2_inj in H; [ | assumption ].
        destruct H; assumption. }
      { intros.
        destruct (typ2_match_case ts x).
        { Require Import ExtLib.Tactics.
          forward_reason.
          destruct (typ0_match_case ts x0).
          { forward_reason.
            simpl.
            left. exists x1.
            exists (match eq_sym x2 in _ = T
                          return Rty ts T (typ2 typ0 x1)
                    with
                      | eq_refl => match eq_sym x3 in _ = T
                                         return Rty ts (typ2 T x1) (typ2 typ0 x1)
                                   with
                                     | eq_refl => eq_refl
                                   end
                    end).
            intros. rewrite H. rewrite H0.
            clear.
            unfold Relim.
            Require Import ExtLib.Data.Eq.
            autorewrite with eq_rw.
            generalize (eq_sym x2).
            destruct e.
            generalize (eq_sym x3).
            destruct e. simpl.
            unfold typ0.
            generalize (tr x1).
            match goal with
              | |- forall x,
                     match ?X with eq_refl => match eq_sym ?Y with _ => _ end end =
                     match _ match ?A with eq_refl => match eq_sym ?B with _ => _ end end with _ => _ end =>
                change A with X ; change B with Y ;
                generalize X ; generalize Y
            end.
            clear. destruct e. simpl.
            generalize (F (typD ts (typed.typ0 (F:=X0))) (typD ts x1)).
            intros. subst. reflexivity. }
          { right. intros.
            simpl. rewrite H. rewrite H0.
            unfold Relim.
            rewrite eq_Arr_eq.
            rewrite eq_Const_eq.
            clear. revert x2.
            match goal with
              | |- forall y,
                     match _ with eq_refl => match ?X with _ => _ end end _ = _ =>
                generalize X
            end.
            generalize (typed.typ2 x0 x1).
            destruct x2. simpl.
            rewrite eq_Arr_eq.
            rewrite match_eq_sym_eq. reflexivity. } }
        { right. simpl. intros.
          rewrite H. reflexivity. } }
      { simpl.
        intros. erewrite typ2_match_Proper; eauto.
        instantiate (1 := pf).
        unfold Relim.
        destruct pf. simpl.
        reflexivity. }
    Qed.

    Definition Typ1_App : Typ0 (G X) :=
      @Build_Typ0 (G X)
                  (typ1 typ0)
                  (fun ts =>
                     match eq_sym (typ1_cast (Typ1 := T1) ts typ0) in _ = T
                           return T = G X
                     with
                       | eq_refl =>
                         match eq_sym (typ0_cast (Typ0 := T0) ts) in _ = T
                               return G T = G X
                         with
                           | eq_refl => eq_refl
                         end
                     end)
                  (fun T ts t0 tr fa =>
                     typ1_match (Typ1 := T1)
                                (fun t => T t -> T t)
                                ts t0
                                (fun a fa' =>
                                   typ0_match (Typ0 := T0)
                                              (fun t => T (G (typD ts a)) -> T (G t))
                                              ts a
                                              (fun _ => tr)
                                              (fun x => x) fa')
                                (fun _ => fa) fa).

    Theorem Typ0Ok_App : Typ0Ok Typ1_App.
    Proof.
      constructor.
      { simpl. intros.
        rewrite (typ1_match_zeta) by assumption.
        rewrite (typ0_match_zeta) by assumption.
        revert tr. clear.
        match goal with
          | |- forall x,
                 match eq_sym ?X with _ => _ end _ =
                 match _ match eq_sym ?Y with _ => _ end with _ => _ end =>
            change Y with X ; generalize X
        end.
        match goal with
          | |- forall e x,
                 match _ with eq_refl => match eq_sym ?X with _ => _ end end _ =
                 match _ match _ with eq_refl => match eq_sym ?Y with _ => _ end end with _ => _ end =>
            change Y with X ; generalize X
        end.
        destruct e.
        simpl in *.
        unfold typ0.
        destruct e. reflexivity. }
      { intros. simpl.
        destruct (typ1_match_case ts x).
        { forward_reason.
          destruct (typ0_match_case ts x0).
          { forward_reason.
            left.
            red in x1. red in x2. subst.
            exists eq_refl. simpl. intros.
            rewrite H. unfold Relim.
            rewrite eq_Arr_eq.
            rewrite H0. simpl.
            autorewrite with eq_rw.
            unfold typ0.
            generalize ((typ1_cast ts (typed.typ0 (F:=X)))).
            generalize (typ0_cast ts).
            generalize (typed.typ0 (F:=X)).
            intros. subst.
            simpl. clear.
            generalize dependent (G (typD ts t)).
            intros; subst. reflexivity. }
          { right. intros.
            rewrite H.
            unfold Relim.
            autorewrite with eq_rw.
            red in x1. subst. simpl in *.
            rewrite H0.
            generalize (typ1_cast ts x0).
            clear. destruct e. reflexivity. } }
        { right. intros. rewrite H. reflexivity. } }
      { simpl; intros.
        erewrite typ1_match_Proper; eauto.
        instantiate (1 := pf).
        unfold Relim.
        destruct pf. simpl.
        f_equal. }
    Qed.

  End apps.

End typed.

Arguments RTypeOk {typ _} : rename.
