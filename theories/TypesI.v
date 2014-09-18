Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Tactics.

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
    typD : typ -> Type
  ; tyAcc : typ -> typ -> Prop
    (** NOTE: Everything below here is fixed! **)
  ; Rty : typ -> typ -> Prop := @eq typ
  ; type_cast : forall (a b : typ), option (Rty a b)
    (* NOTE: I can't make this dependent b/c it exposes the
     * underlying syntactic types, which do not have to be equal.
     *
     * The solution is to require that the function respects [Rty].
     *)
  ; Relim : forall (F : Type -> Type) {to from}
                   (pf : Rty to from),
              F (typD from) ->
              F (typD to) :=
      fun F to from pf =>
        match pf in _ = t return F (typD t) -> F (typD to) with
          | eq_refl => fun x => x
        end
  ; Rrefl : forall x, Rty x x :=
      @eq_refl _
  ; Rsym : forall {x y}, Rty y x -> Rty x y :=
      fun x y pf => eq_sym pf
  ; Rtrans : forall {x y z}, Rty x y -> Rty y z -> Rty x z :=
      @eq_trans _
  }.

  Variable RType_typ : RType.

  Class RTypeOk  : Type :=
  { Relim_refl
    : forall t F (val : F (typD t)),
        Relim F (Rrefl t) val = val
  ; wf_tyAcc : well_founded tyAcc
  ; Relim_sym
    : forall t u (pf : Rty t u) F (val : F (typD t)),
        Relim F (Rsym pf) val =
        Relim (fun T => F T -> F _) pf (fun x => x) val
  ; Relim_trans
    : forall t u v (pf1 : Rty t u) (pf2 : Rty u v) F
             (val : F (typD v)),
        Relim F (Rtrans pf1 pf2) val =
        Relim F pf1 (Relim F pf2 val)
  ; type_cast_refl : forall x, type_cast x x = Some (Rrefl x)
  ; type_cast_total : forall x y,
                        type_cast x y = None -> ~Rty x y
  }.

  Definition makeRTypeOk
             (wf : well_founded tyAcc)
             (tc : forall (x : typ), type_cast x x = Some (Rrefl x))
             (tc' : forall (x y : typ),
                      type_cast x y = None -> ~ Rty x y)
  : RTypeOk.
  Proof.
    constructor; simpl.
    { reflexivity. }
    { assumption. }
    { destruct pf. reflexivity. }
    { destruct pf1; destruct pf2; reflexivity. }
    { assumption. }
    { assumption. }
  Qed.

  Global Instance RelDec_Rty : RelDec Rty :=
  { rel_dec := fun l r => match type_cast l r with
                            | None => false
                            | Some _ => true
                          end }.

  Global Instance RelDec_Correct_Rty {RTO : RTypeOk}
  : @RelDec_Correct _ Rty _.
  Proof.
    constructor. unfold rel_dec; simpl.
    intros. generalize (@type_cast_total _ x y).
    destruct (type_cast x y); intros.
    split; auto. intuition congruence.
  Qed.

  Section Typ0.
    Variable F : Type.

    Class Typ0 : Type :=
    { typ0 : typ
    ; typ0_cast : typD typ0 = F
    ; typ0_match : forall (T : Type -> Type) t,
                     T F ->
                     T (typD t) ->
                     T (typD t)
    }.

    Class Typ0Ok (TI : Typ0) : Type :=
    { typ0_match_zeta
      : forall T tr fa,
          typ0_match T typ0 tr fa =
          match eq_sym typ0_cast in _ = t return T t with
            | eq_refl => tr
          end
    ; typ0_match_case
      : forall x,
          (exists (pf : Rty x typ0),
             forall T tr fa,
               typ0_match T x tr fa =
               Relim T pf
                     match eq_sym typ0_cast in _ = t return T t with
                       | eq_refl => tr
                     end) \/
          (forall T tr fa, typ0_match T x tr fa = fa)
    ; typ0_match_Proper
      : forall T t t' (pf : Rty t' t) tr fa,
          typ0_match T t tr fa =
          Relim T (Rsym pf) (typ0_match T t' tr (Relim T pf fa))
    }.
  End Typ0.

  Section Typ1.
    Variable F : Type -> Type.

    Class Typ1 : Type :=
    { typ1 : typ -> typ
    ; typ1_cast : forall a, typD (typ1 a) = F (typD a)
    ; typ1_match : forall (T : Type -> Type) t,
                     (forall a, T (F (typD a))) ->
                     T (typD t) ->
                     T (typD t)
    }.

    Class Typ1Ok (TI : Typ1) : Type :=
    { typ1_match_zeta
      : forall T a tr fa,
          typ1_match T (typ1 a) tr fa =
          match eq_sym (typ1_cast a) in _ = t return T t with
            | eq_refl => tr a
          end
    ; tyAcc_typ1 : forall a, tyAcc a (typ1 a)
    ; typ1_inj
      : forall a c,
          Rty (typ1 a) (typ1 c) ->
          Rty a c
    ; typ1_match_case
      : forall x,
          (exists d (pf : Rty x (typ1 d)),
             forall T tr fa,
               typ1_match T x tr fa =
               Relim T pf
                     (match eq_sym (typ1_cast d) in _ = t return T t with
                        | eq_refl => tr d
                      end)) \/
          (forall T tr fa, typ1_match T x tr fa = fa)
    ; typ1_match_Proper
      : forall T t t' (pf : Rty t' t) tr fa,
          typ1_match T t tr fa =
          Relim T (Rsym pf) (typ1_match T t' tr (Relim T pf fa))
    }.
  End Typ1.

  Section Typ2.
    Variable F : Type -> Type -> Type.

    Class Typ2 : Type :=
    { typ2 : typ -> typ -> typ
    ; typ2_cast : forall a b, typD (typ2 a b) = F (typD a) (typD b)
    ; typ2_match : forall (T : Type -> Type) t,
                     (forall a b, T (F (typD a) (typD b))) ->
                     T (typD t) ->
                     T (typD t)
    }.

    Class Typ2Ok (TI : Typ2) : Type :=
    { typ2_match_zeta
      : forall T a b tr fa,
          typ2_match T (typ2 a b) tr fa =
          match eq_sym (typ2_cast a b) in _ = t return T t with
            | eq_refl => tr a b
          end
    ; tyAcc_typ2L : forall a b, tyAcc a (typ2 a b)
    ; tyAcc_typ2R : forall a b, tyAcc a (typ2 b a)
    ; typ2_inj
      : forall a b c d,
          Rty (typ2 a b) (typ2 c d) ->
          Rty a c /\ Rty b d
    ; typ2_match_case
      : forall x,
          (exists d r (pf : Rty x (typ2 d r)),
             forall T tr fa,
               typ2_match T x tr fa =
               Relim T pf
                     (match eq_sym (typ2_cast d r) in _ = t return T t with
                        | eq_refl => tr d r
                      end)) \/
          (forall T tr fa, typ2_match T x tr fa = fa)
    ; typ2_match_Proper
      : forall T t t' (pf : Rty t' t) tr fa,
          typ2_match T t tr fa =
          Relim T (Rsym pf) (typ2_match T t' tr (Relim T pf fa))
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
                  (fun a =>
                     match eq_sym (typ2_cast (Typ2 := T2) typ0 a) in _ = T
                           return T = F X (typD a)
                     with
                       | eq_refl =>
                         match eq_sym (typ0_cast (Typ0 := T0)) in _ = T
                               return F T (typD a) = F X (typD a)
                         with
                           | eq_refl => eq_refl
                         end
                     end)
                  (fun T t0 tr fa =>
                     typ2_match (Typ2 := T2)
                                (fun t => T t -> T t)
                                t0
                                (fun a b fa' =>
                                   typ0_match (Typ0 := T0)
                                              (fun t => T (F (typD a) (typD b)) -> T (F t (typD b)))
                                              a
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
        destruct (typ2_match_case x).
        { forward_reason.
          destruct (typ0_match_case x0).
          { forward_reason.
            simpl.
            left. exists x1.
            exists (match eq_sym x2 in _ = T
                          return Rty T (typ2 typ0 x1)
                    with
                      | eq_refl => match eq_sym x3 in _ = T
                                         return Rty (typ2 T x1) (typ2 typ0 x1)
                                   with
                                     | eq_refl => eq_refl
                                   end
                    end).
            intros. rewrite H. rewrite H0.
            clear.
            unfold Relim.

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
            generalize (F (typD (typed.typ0 (F:=X0))) (typD x1)).
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
                  (match eq_sym (typ1_cast (Typ1 := T1) typ0) in _ = T
                         return T = G X
                   with
                     | eq_refl =>
                       match eq_sym (typ0_cast (Typ0 := T0)) in _ = T
                             return G T = G X
                       with
                         | eq_refl => eq_refl
                       end
                   end)
                  (fun T t0 tr fa =>
                     typ1_match (Typ1 := T1)
                                (fun t => T t -> T t)
                                t0
                                (fun a fa' =>
                                   typ0_match (Typ0 := T0)
                                              (fun t => T (G (typD a)) -> T (G t))
                                              a
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
        destruct (typ1_match_case x).
        { forward_reason.
          destruct (typ0_match_case x0).
          { forward_reason.
            left.
            red in x1. red in x2. subst.
            exists eq_refl. simpl. intros.
            rewrite H. unfold Relim.
            rewrite eq_Arr_eq.
            rewrite H0. simpl.
            autorewrite with eq_rw.
            unfold typ0.
            generalize ((typ1_cast (typed.typ0 (F:=X)))).
            generalize (typ0_cast (F:=X)).
            generalize (typed.typ0 (F:=X)).
            intros. subst.
            simpl. clear.
            generalize dependent (G (typD t)).
            intros; subst. reflexivity. }
          { right. intros.
            rewrite H.
            unfold Relim.
            autorewrite with eq_rw.
            red in x1. subst. simpl in *.
            rewrite H0.
            generalize (typ1_cast x0).
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

Arguments typD {typ _} _ : rename.
Arguments Rty {typ _} _ _ : rename.
Arguments RTypeOk {typ _} : rename.
