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
                     T (typD ts typ0) ->
                     T (typD ts t) ->
                     T (typD ts t)
    }.

    Class Typ0Ok (TI : Typ0) : Type :=
    { typ0_match_zeta
      : forall T ts tr fa,
          typ0_match T ts typ0 tr fa = tr
    ; typ0_match_case
      : forall ts x,
          (exists (pf : Rty ts x typ0),
             forall T tr fa,
               typ0_match T ts x tr fa =
               Relim T pf tr) \/
          (forall T tr fa, typ0_match T ts x tr fa = fa)
    ; typ0_match_Proper
      : forall T ts t t' (pf : Rty ts t' t) tr fa,
          typ0_match T ts t tr fa =
          Relim T (Rsym pf) (typ0_match T ts t' tr (Relim T pf fa))
    }.
  End Typ0.

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

End typed.

Arguments RTypeOk {typ _} : rename.
