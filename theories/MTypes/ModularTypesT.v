Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.

Require Import MirrorCore.Util.PolyAcc.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.TypeView.

Universes Ukind.
Universes Usmall Ularge.

Lemma dec_refl
  : forall T (dec : forall a b : T, {a = b} + {a <> b}) (a : T),
    dec a a = left eq_refl.
Proof using.
  intros. destruct (dec a a).
  - uip_all. reflexivity.
  - exfalso; tauto.
    Unshelve. assumption.
Qed.

Module Type TypeLang.
  Parameter kind : Type.
  Parameter Kstar : kind.
  Parameter kind_eq_dec : forall a b : kind, {a = b} + {a <> b}.
  Parameter kindD : kind -> Type@{Ukind}.

  Parameter type : (kind -> Type) -> kind -> Type.

  Parameter tyVar : forall tsym k (p : positive), type tsym k.

  Section with_symbols.
    Variable symbol : kind -> Type.

    Class TSym : Type :=
    { symbolD : forall {k}, symbol k -> kindD k
    ; symbol_dec : forall {k} (a b : symbol k), {a = b} + {a <> b}
    }.

    Parameter RType_type : TSym -> RType (type symbol Kstar).
    Parameter RTypeOk_type : forall ts : TSym, @RTypeOk _ (RType_type ts).

    Parameter type_eq_dec : TSym -> forall {k} (a b : type symbol k), {a = b} + {a <> b}.

  End with_symbols.

  Arguments symbolD {_ _ _} _.
  Arguments symbol_dec {_ _ _} _ _.

End TypeLang.


Module TypeLang_mtyp <: TypeLang.
  Definition kind := nat.
  Definition Kstar := 0.
  Definition kind_eq_dec (a b : kind) : {a = b} + {a <> b}.
   decide equality.
  Defined.

  Fixpoint kindD (n : nat) : Type@{Ukind} :=
    match n with
    | 0 => Type@{Usmall}
    | S n => Type@{Usmall} -> kindD n
    end.

  Fixpoint applyn' {n} (vs : vector Type@{Usmall} n)
  : kindD n -> Type@{Usmall} :=
    match vs in vector _ n return kindD n -> Type@{Usmall} with
    | Vnil _ => fun T => T
    | Vcons v vs => fun F => applyn' vs (F v)
    end.
  Definition applyn {n} (f : kindD n) (vs : vector Type@{Usmall} n)
  : Type@{Usmall} :=
    applyn' vs f.

  Section with_symbols.

    Variable symbol : kind -> Type.

    Class TSym : Type :=
    { symbolD : forall {k}, symbol k -> kindD k
    ; symbol_dec : forall {k} (a b : symbol k), {a = b} + {a <> b}
    }.

    Unset Elimination Schemes.

    Inductive type' : kind -> Type :=
    | tyArr : type' 0 -> type' 0 -> type' 0
    | tyBase0 : symbol Kstar -> type' 0
    | tyBase1 : symbol 1 -> type' 0 -> type' 0
    | tyBase2 : symbol 2 -> type' 0 -> type' 0 -> type' 0
    | tyApp : forall {n}, symbol (3 + n) -> vector (type' 0) (3 + n) -> type' 0
    | tyProp : type' 0
    | tyVar' : forall k, positive -> type' k. (** Reserved for unification, do not use **)

    Definition tyVar := tyVar'.

    Definition type := type'.

    Section type_ind.
      Variable P : type 0 -> Prop.
      Hypotheses  (Harr : forall {a b}, P a -> P b -> P (tyArr a b))
                  (Hbase0 : forall s, P (tyBase0 s))
                  (Hbase1 : forall s {a}, P a -> P (tyBase1 s a))
                  (Hbase2 : forall s {a b}, P a -> P b -> P (tyBase2 s a b))
                  (Happ : forall {n} s ms, ForallV P ms -> P (@tyApp n s ms))
                  (Hprop : P tyProp)
                  (Hvar : forall p, P (tyVar' Kstar p)).
      Fixpoint type_ind (x : type 0) : P x :=
        match x as x in type' 0 return P x with
        | tyArr a b => Harr _ _ (type_ind a) (type_ind b)
        | tyBase0 s => Hbase0 s
        | tyBase1 s a => Hbase1 s _ (type_ind a)
        | tyBase2 s a b => Hbase2 s _ _ (type_ind a) (type_ind b)
        | tyApp s ms =>
          Happ _ s ms ((fix all {n} (ms : vector (type 0) n) : ForallV P ms :=
                          match ms with
                          | Vnil _ => ForallV_nil _
                          | Vcons m ms => ForallV_cons _(type_ind m) (all ms)
                          end) _ ms)
        | tyProp => Hprop
        | tyVar' 0 p => Hvar p
        end.
    End type_ind.

    Variable ts : TSym.

    Fixpoint default_type_for_kind n : kindD n :=
      match n as n return kindD n with
      | 0 => Empty_set
      | S b => fun _ => default_type_for_kind b
      end.


    Fixpoint typeD {k} (t : type k) : kindD k :=
      match t in type' k return kindD k with
      | tyArr a b => typeD a -> typeD b
      | tyBase0 s => symbolD s
      | tyBase1 s m => symbolD s (typeD m)
      | tyBase2 s m1 m2 => symbolD s (typeD m1) (typeD m2)
      | tyApp s ms => applyn (symbolD s) (vector_map typeD ms)
      | tyProp => Prop
      | tyVar' n _ => default_type_for_kind n
      end.

    Inductive mtyp_acc (a : type Kstar) : type Kstar -> Prop :=
    | tyAcc_tyArrL   : forall b, mtyp_acc a (tyArr a b)
    | tyAcc_tyArrR   : forall b, mtyp_acc a (tyArr b a)
    | tyAcc_tyBase1  : forall s, mtyp_acc a (tyBase1 s a)
    | tyAcc_tyBase2L : forall s b, mtyp_acc a (tyBase2 s a b)
    | tyAcc_tyBase2R : forall s b, mtyp_acc a (tyBase2 s b a)
    | tyAcc_tyApp    : forall n s ms, vector_In a ms -> mtyp_acc a (@tyApp n s ms).


    Theorem wf_mtyp_acc : well_founded mtyp_acc.
    Proof.
      red. eapply type_ind; constructor; inversion 1; subst; auto.
      - apply inj_pair2 in H4.
        subst. eapply ForallV_vector_In; eauto.
    Defined.

    Fixpoint type_eq_dec {k} (a b : type k) : {a = b} + {a <> b}.
(*
      refine
        match a as a in type' 0, b as b in type' 0 return {a = b} + {a <> b} with
        | tyArr l r , tyArr l' r' =>
          match type_eq_dec l l'
                , type_eq_dec r r'
          with
          | left pf , left pf' => left match pf , pf' with
                                      | eq_refl , eq_refl => eq_refl
                                      end
          | _ , _ => right _
          end
        | tyBase0 s , tyBase0 s' =>
          match symbol_dec s s' with
          | left pf => left match pf with eq_refl => eq_refl end
          | _ => right _
          end
        | tyBase1 s m , tyBase1 s' m' =>
          match symbol_dec s s'
                , type_eq_dec m m'
          with
          | left pf , left pf' => left match pf , pf' with
                                      | eq_refl , eq_refl => eq_refl
                                      end
          | _ , _ => right _
          end
        | tyBase2 s m m2 , tyBase2 s' m' m2' =>
          match symbol_dec s s'
                , type_eq_dec m m'
                , type_eq_dec m2 m2'
          with
          | left pf , left pf' , left pf'' =>
            left match pf , pf' , pf'' with
                 | eq_refl , eq_refl , eq_refl => eq_refl
                 end
          | _ , _ , _ => right _
          end
        | @tyApp n s ms , @tyApp n' s' ms' =>
          match PeanoNat.Nat.eq_dec n' n with
          | left pf =>
            match symbol_dec s match pf with eq_refl => s' end
                  , vector_dec type_eq_dec ms match pf with eq_refl => ms' end
            with
            | left pf , left pf' => left _
            | _ , _ => right _
            end
          | right _ => right _
          end
        | tyProp , tyProp => left eq_refl
        | tyVar a , tyVar b =>
          match Pos.eq_dec a b with
          | left pf => left (f_equal _ pf)
          | right _ => right _
          end
        | _ , _ => right _
        end;
        try solve [ clear ; intro pf; inversion pf
                  | intro pf ; inversion pf; auto ].
      { subst; reflexivity. }
      { clear - n0. intro. inv_all.
        specialize (H pf). destruct H. auto. }
      { clear - n0. intro; inv_all.
        specialize (H pf). destruct H; auto. }
*)
    Admitted.

    Definition mtyp_cast (a b : type Kstar) : option (a = b) :=
      match type_eq_dec a b with
      | left pf => Some pf
      | _ => None
      end.

    Instance RType_type : RType (type Kstar) :=
    { typD := typeD
    ; type_cast := mtyp_cast
    ; tyAcc := mtyp_acc }.

    Instance RTypeOk_type : RTypeOk.
    refine
      {| Relim_refl := fun _ _ _ => eq_refl
       ; wf_tyAcc := wf_mtyp_acc
       ; Relim_sym := ltac:(destruct pf; reflexivity)
       ; Relim_trans := ltac:(destruct pf1; destruct pf2; reflexivity)
       ; type_cast_refl := _
       ; EquivDec_typ := type_eq_dec
       |}.
    simpl. unfold mtyp_cast. intros. rewrite dec_refl. reflexivity.
    Defined.
  End with_symbols.

  Arguments tyBase0 {_} _.
  Arguments tyBase1 {_} _ _.
  Arguments tyBase2 {_} _ _ _.
  Arguments tyApp {_ _} _ _.
  Arguments tyArr {_} _ _.
  Arguments tyProp {_}.
  Arguments tyVar {_} _ _.
  Arguments tyVar' {_} _ _.

End TypeLang_mtyp.


Module TypeLang_mtypF <: TypeLang.
  Inductive kind' :=
  | Kstar' : kind'
  | Karr : kind' -> kind' -> kind'.
  Definition Kstar := Kstar'.
  Definition kind := kind'.

  Definition kind_eq_dec : forall a b : kind, {a = b} + {a <> b}.
    decide equality.
  Defined.

  Fixpoint kindD (k : kind) : Type@{Ukind} :=
    match k with
    | Kstar' => Type@{Usmall}
    | Karr a b => kindD a -> kindD b
    end.

  Section with_symbols.

    Variable symbol : kind -> Type.

    Class TSym : Type :=
    { symbolD : forall {k}, symbol k -> kindD k
    ; symbol_dec : forall {k} (a b : symbol k), {a = b} + {a <> b}
    }.


    Unset Elimination Schemes.

    Inductive mtyp : kind -> Type :=
    | tyArr : mtyp Kstar -> mtyp Kstar -> mtyp Kstar
    | tyApp : forall {d c}, mtyp (Karr d c) -> mtyp d -> mtyp c
    | tyInj : forall n, symbol n -> mtyp n
    | tyProp : mtyp Kstar
    | tyVar' : forall n, positive -> mtyp n. (** Reserved for unification, do not use **)

    Definition type := mtyp.
    Definition tyVar := tyVar'.

    Section mtyp_ind.
      Variable P : forall {n}, mtyp n -> Prop.
      Hypotheses  (Harr : forall {a b : mtyp Kstar'}, P _ a -> P _ b -> P _ (tyArr a b))
                  (Happ : forall k n {a : mtyp (Karr k n)} {b : mtyp k}, P _ a -> P _ b -> P _ (tyApp a b))
                  (*(Hinj0 : forall s, P _ (tyInj0 s))
                (Hinj1 : forall s, P _ (tyInj1 s))
                (Hinj2 : forall s, P _ (tyInj2 s))
                (Hinj : forall {n} s, P (3+n) (tyInjN s))
                   *)
                  (Hinj : forall n s, P n (tyInj _ s))
                  (Hprop : P _ tyProp)
                  (Hvar : forall n p, P n (tyVar _ p)).
      Fixpoint mtyp_ind {n} (x : mtyp n) : P n x :=
        match x as x in mtyp n return P n x with
        | tyArr a b => Harr _ _ (mtyp_ind a) (mtyp_ind b)
        (*
      | tyInj0 s => Hinj0 s
      | tyInj1 s => Hinj1 s
      | tyInj2 s => Hinj2 s
      | @tyInjN n s => Hinj n s *)
        | tyInj _ s => Hinj _ s
        | tyApp s ms =>
          Happ _ _ _ _ (mtyp_ind s) (mtyp_ind ms)
        | tyProp => Hprop
        | tyVar' n p => Hvar n p
        end.
    End mtyp_ind.

    Set Elimination Schemes.

    (** Better to match on vector? *)

    Fixpoint default_type_for_kind n : kindD n :=
      match n as n return kindD n with
      | Kstar' => Empty_set
      | Karr a b => fun _ => default_type_for_kind b
      end.

    Variable ts : TSym.

    Fixpoint typeD {n} (t : mtyp n) : kindD n :=
      match t in mtyp n return kindD n with
      | tyArr a b => typeD a -> typeD b
      | tyInj _ s => symbolD s
      | tyApp s ms => (typeD s) (typeD ms)
      | tyProp => Prop
      | tyVar' n _ => default_type_for_kind n
      end.

    Inductive mtypC : Set :=
    | CArr | CApp | CInj | CProp | CVar.

    Definition ctor {n} (a : mtyp n) : mtypC :=
      match a with
      | tyArr _ _ => CArr
      | tyApp _ _ => CApp
      | tyInj _ _ => CInj
      | tyProp => CProp
      | tyVar' _ _ => CVar
      end.

    Definition mtyp_diff_ctor n a : forall (b : mtyp n), ctor a <> ctor b -> a <> b.
      intros.
      intro. apply H. f_equal. assumption.
    Defined.

    Lemma tyArr_Inj : forall a b c d, tyArr a b = tyArr c d -> a = c /\ b = d.
    Proof.
      intros.
      refine match H in _ = X
                   return match X with
                          | tyArr c d => a = c /\ b = d
                          | _ => True
                          end
             with
             | eq_refl => conj eq_refl eq_refl
             end.
    Defined.

    Lemma tyApp_Inj : forall k n a b c d, @tyApp k n a b = tyApp c d -> a = c /\ b = d.
    Proof.
      intros.
      refine (match H in _ = X
                    return match X in mtyp n' return _ with
                           | @tyApp k' n' c d => fun a b =>
                                                  forall pf : k' = k,
                                                    a = match pf in _ = X return mtyp (Karr X _) with
                                                        | eq_refl => c
                                                        end /\
                                                    b = match pf in _ = X return mtyp X with
                                                        | eq_refl => d
                                                        end
                           | _ => fun _ _ => True
                           end a b
              with
              | eq_refl => _
              end eq_refl).
      intros. destruct (uip_trans kind_eq_dec _ _ eq_refl pf).
      constructor; reflexivity.
    Defined.

    Lemma tyInj_Inj : forall n s s', tyInj n s = tyInj n s' -> s = s'.
    Proof.
      intros.
      refine (match H in _ = X
                    return match X in mtyp n' return _ with
                           | tyInj c s' => fun s => s = s'
                           | _ => fun _ => True
                           end s
              with
              | eq_refl => eq_refl
              end).
    Defined.

    Lemma tyVar_Inj : forall n s s', tyVar n s = tyVar n s' -> s = s'.
    Proof.
      intros.
      refine (match H in _ = X
                    return match X in mtyp n' return _ with
                           | tyVar' c s' => fun s => s = s'
                           | _ => fun _ => True
                           end s
              with
              | eq_refl => eq_refl
              end).
    Defined.

    (** Suppose that we could implement this... *)
    Fixpoint type_eq_dec {n} (a : mtyp n) : forall b, {a = b} + {a <> b}.
      refine
        match a as a in mtyp n
              return forall b : mtyp n, {a = b} + {a <> b}
        with
        | tyArr l r => fun b =>
          match b as b in mtyp n'
                return {match n' as n' return mtyp n' -> Prop with
                        | Kstar' => fun b => tyArr l r = b
                        | _ => fun _ => False
                        end b} + {match n' as n' return mtyp n' -> Prop with
                                  | Kstar' => fun b => not (eq (tyArr l r) b)
                                  | _ => fun _ => True
                                  end b}
          with
          | tyArr l' r' =>
            match type_eq_dec _ l l'
                , type_eq_dec _ r r'
            with
            | left pf , left pf' => left match pf , pf' with
                                        | eq_refl , eq_refl => eq_refl
                                        end
            | _ , _ => right _
            end
          | _ => right _
          end
        | @tyApp k n l r => fun b =>
          match b as b in mtyp n'
                return forall (l : mtyp (Karr k n')) (r : mtyp k),
              (forall l', {l = l'} + {l <> l'}) ->
              (forall r', {r = r'} + {r <> r'}) ->
              {tyApp l r = b} + {tyApp l r <> b}
          with
          | @tyApp k' n' l' r' =>
            match kind_eq_dec k' k with
            | left pfk => match pfk in _ = X
                               return _
                         with
                         | eq_refl => fun l r recl recr =>
                                       match recl l' , recr r' with
                                       | left pf , left pf' => left match pf , pf' with
                                                                   | eq_refl , eq_refl => eq_refl
                                                                   end
                                       | _ , _ => right _
                                       end
                         end
            | _ => fun _ _ _ _ => right _
            end
          | _ => fun _ _ _ _ => right _
          end l r (fun x => @type_eq_dec _ l x) (fun x => @type_eq_dec _ r x)

        | tyInj _ s => fun b =>
          match b as b in mtyp n
                return forall s : symbol n, {tyInj n s = b} + {tyInj n s <> b}
          with
          | tyInj _ s' => fun s =>
                           match symbol_dec s s' with
                           | left pf => left match pf with
                                            | eq_refl => eq_refl
                                            end
                           | right _ => right _
                           end
          | _ => fun _ => right _
          end s
        | tyProp => fun b =>
          match b as b in mtyp n' return {match n' as n' return mtyp n' -> Prop with
                                          | Kstar' => fun b => tyProp = b
                                          | _ => fun _ => False
                                          end b} + {match n' as n' return mtyp n' -> Prop with
                                                    | Kstar' => fun b => not (tyProp = b)
                                                    | _ => fun _ => True
                                                    end b} with
          | tyProp => left eq_refl
          | _ => right _
          end
        | tyVar' _ p => fun b =>
          match b as b in mtyp n' return {tyVar' n' p = b} + {tyVar n' p <> b} with
          | tyVar' _ p' =>
            match Pos.eq_dec p p' with
            | left pf => left match pf with
                             | eq_refl => eq_refl
                             end
            | right _ => right _
            end
          | _ => right _
          end
        end.
      all: try solve [ eapply mtyp_diff_ctor; simpl; clear; congruence
                     | destruct k0 ; [ eapply mtyp_diff_ctor; simpl; clear; congruence | trivial ]
                     | destruct k ; [ eapply mtyp_diff_ctor; simpl; clear; congruence | trivial ]
                     | intro X; apply tyApp_Inj in X; tauto
                     | intro X; apply tyArr_Inj in X; tauto
                     | intro X; apply tyVar_Inj in X; tauto
                     | intro X; apply tyInj_Inj in X; tauto ].
      intro. apply n1. injection H. intros. symmetry. assumption.
    Defined.

    Definition mtyp_cast {n} (a b : mtyp n) : option (a = b) :=
      match type_eq_dec a b with
      | left pf => Some pf
      | right _ => None
      end.

    Instance RelDec_eq_mtyp {n} : RelDec (@eq (mtyp n)) :=
    { rel_dec := fun a b => if type_eq_dec a b then true else false }.
    Instance RelDec_Correct_eq_mtyp {n} : RelDec_Correct (@RelDec_eq_mtyp n).
    Proof. constructor. unfold rel_dec. simpl.
           intros. destruct (type_eq_dec x y); try tauto.
           split; intros; congruence.
    Defined.

    Inductive mtyp_acc : forall a b (x : mtyp a) (y : mtyp b), Prop :=
    | tyAcc_tyArrL   : forall x y, mtyp_acc _ _ x (tyArr x y)
    | tyAcc_tyArrR   : forall x y, mtyp_acc _ _ y (tyArr x y)
    | tyAcc_tyAppL   : forall k n (x : mtyp (Karr k n)) y, mtyp_acc _ _ x (tyApp x y)
    | tyAcc_tyAppR   : forall k n (x : mtyp (Karr k n)) y, mtyp_acc _ _ y (tyApp x y)
    .


    Theorem Pwf_mtyp_acc : @Pwell_founded _ _ mtyp_acc.
    Proof.
      red. induction x; try solve [ simpl; intros; constructor; inversion 1; auto ].
      constructor. inversion 1.
      { subst.
        eapply inj_pair2 in H6.
        eapply inj_pair2 in H6.
        subst. auto. }
      { subst.
        eapply inj_pair2 in H3.
        eapply inj_pair2 in H5.
        eapply inj_pair2 in H5.
        eapply inj_pair2 in H6.
        subst.  auto. admit. }
      Unshelve.
      all: apply kind_eq_dec.
    Admitted.


    Instance RType_type : RType (mtyp Kstar) :=
    { typD := typeD
    ; type_cast := mtyp_cast
    ; tyAcc := (PleftTrans _ _ (@mtyp_acc)) Kstar Kstar }.

    Local Instance EqDec_symbol : forall n, EqDec (symbol n) (@eq (symbol n)).
    Proof.
      red. intros.
      destruct (symbol_dec x y); (left + right); assumption.
    Defined.

    Local Instance EqDec_mtyp {n} : EqDec (mtyp n) (@eq (mtyp n)).
    Proof.
      red. intros.
      eapply type_eq_dec.
    Defined.

    Lemma symbol_dec_refl
      : forall n (a : symbol n), symbol_dec a a = left eq_refl.
    Proof using.
      intro. apply dec_refl.
    Qed.

    Theorem mtyp_cast_refl : forall n (a : mtyp n),
        mtyp_cast a a = Some eq_refl.
    Proof.
      unfold mtyp_cast; intros.
      rewrite dec_refl. reflexivity.
    Defined.

    Instance RTypeOk_type : RTypeOk.
    Proof.
      constructor.
      - reflexivity.
      - simpl. eapply Pwell_founded_well_founded.
        eapply Pwell_founded_PleftTrans. eapply Pwf_mtyp_acc.
      - destruct pf; reflexivity.
      - destruct pf1; destruct pf2; reflexivity.
      - apply mtyp_cast_refl.
      - eauto with typeclass_instances.
    Qed.

    Section elim_mtyp0.
      Variable P : mtyp Kstar -> Type.
      Variables (Harr : forall a b, P (tyArr a b))
                (Happ : forall d (a : mtyp (Karr d Kstar)) b, P (tyApp a b))
                (Hprop : P tyProp)
                (Hinj : forall s : symbol Kstar, P (tyInj Kstar s))
                (Hvar : forall p, P (tyVar Kstar p)).
      Definition elim_mtyp0 (m : mtyp Kstar) : P m.
        refine
          match m as m in mtyp Kstar' return P m with
          | tyArr a b => Harr a b
          | @tyApp _ n a b => _
          | tyProp => Hprop
          | @tyInj n s => _
          | @tyVar' n p => _
          end; destruct n; try solve [ exact idProp ]; eauto.
      Defined.
    End elim_mtyp0.

    Section elim_mtyp1.
      Variable d c : kind.
      Variable P : mtyp (Karr d c) -> Type.
      Variables (Happ : forall d' (a : mtyp (Karr d' (Karr d c))) b, P (tyApp a b))
                (Hinj : forall s : symbol (Karr d c), P (tyInj _ s))
                (Hvar : forall p, P (tyVar (Karr d c) p)).
      Definition elim_mtyp1 (m : mtyp (Karr d c)) : P m.
        refine
          (match m as m in mtyp (Karr d' c')
                 return forall (pf : d' = d) (pfc : c' = c),
               P match pf , pfc with
                 | eq_refl , eq_refl => m
                 end
           with
           | tyArr a b => idProp
           | @tyApp _ n a b => _
           | tyProp => idProp
           | @tyInj n s => _
           | @tyVar' n p => _
           end eq_refl eq_refl); destruct n; try apply idProp; intros; subst.
        { apply Happ. }
        { apply Hinj. }
        { apply Hvar. }
      Defined.
    End elim_mtyp1.

    Section elim_mtyp2.
      Variables a b c : kind.
      Variable P : mtyp (Karr a (Karr b c)) -> Type.
      Variables (Happ : forall d (a : mtyp (Karr d (Karr a (Karr b c)))) b, P (tyApp a b))
                (Hinj : forall s : symbol (Karr a (Karr b c)), P (tyInj _ s))
                (Hvar : forall p, P (tyVar (Karr a (Karr b c)) p)).
      Definition elim_mtyp2 (m : mtyp (Karr a (Karr b c))) : P m.
        refine
          (match m as m in mtyp (Karr a' (Karr b' c'))
                 return forall (pf : a' = a) (pf' : b' = b) (pf'' : c' = c),
               P match pf , pf' , pf'' with
                 | eq_refl , eq_refl , eq_refl => m
                 end
           with
           | tyArr a b => idProp
           | @tyApp _ n a b => _
           | tyProp => idProp
           | @tyInj n s => _
           | @tyVar' n p => _
           end eq_refl eq_refl eq_refl);
          try (destruct n; try apply idProp; destruct n2; try apply idProp);
          intros; subst.
        { apply Happ. }
        { apply Hinj. }
        { apply Hvar. }
      Defined.
    End elim_mtyp2.

    Global Instance Typ0_Prop : Typ0 _ Prop :=
    { typ0 := tyProp
    ; typ0_cast := eq_refl
    ; typ0_match := fun (T : kindD Kstar -> Type) (m : mtyp Kstar) tr =>
      match m as t' in mtyp n'
            return match n' as n' return (kindD Kstar -> Type) -> mtyp n' -> Type with
                   | Kstar' => fun T t' => T (typeD t')
                   | _ => fun _ _ => unit
                   end T t' ->
                   match n' as n' return (kindD Kstar -> Type) -> mtyp n' -> Type with
                   | Kstar' => fun T t' => T (typeD t')
                   | _ => fun _ _ => unit
                   end T t'
      with
      | tyProp => fun _ => tr
      | _ => fun fa => fa
      end  }.

    Global Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop.
    Proof using.
      constructor.
      { reflexivity. }
      { refine (@elim_mtyp0 _ _ _ _ _ _); simpl; try (right; reflexivity).
        left; exists eq_refl; reflexivity. }
      { destruct pf; reflexivity. }
    Qed.

    Instance Typ0_sym (s : symbol Kstar) : Typ0 _ (symbolD s) :=
    { typ0 := tyInj Kstar s
    ; typ0_cast := eq_refl
    ; typ0_match := fun T (t : mtyp _) tr =>
      match t as t' in mtyp n'
            return match n' as n' return mtyp n' -> Type with
                   | Kstar' => fun t' => T (typeD t')
                   | _ => fun _ => unit
                   end t' ->
                   match n' as n' return mtyp n' -> Type with
                   | Kstar' => fun t' => T (typeD t')
                   | _ => fun _ => unit
                   end t'
      with
      | @tyInj Kstar' s' =>
        match symbol_dec s s' with
        | left pf => fun _ => match pf with
                          | eq_refl => tr
                          end
        | right _ => fun fa => fa
        end
      | _ => fun fa => fa
      end }.

    Instance Typ0Ok_sym (s : symbol Kstar) : Typ0Ok (Typ0_sym s).
    Proof using.
      constructor.
      { simpl. intros.
        destruct (symbol_dec s s) eqn:?; try reflexivity.
        - uip_all. reflexivity.
        - exfalso; clear - n. congruence. }
      { refine (@elim_mtyp0 _ _ _ _ _ _); simpl;
          try solve [ right; reflexivity ].
        intros. destruct (symbol_dec s s0); try solve [ right ; eauto ].
        left. subst. exists eq_refl. reflexivity. }
      { destruct pf. reflexivity. }
    Qed.

    Instance Typ1_sym (s : symbol (Karr Kstar Kstar)) : Typ1 _ (symbolD s) :=
    { typ1 := tyApp (@tyInj _ s)
    ; typ1_cast := fun _ => eq_refl
    ; typ1_match := fun T (t : mtyp _) tr =>
      match t as t in mtyp n'
            return match n' as n' return mtyp n' -> Type with
                   | Kstar' => fun t => T (typeD t)
                   | _ => fun _ => unit
                   end t ->
                   match n' as n' return mtyp n' -> Type with
                   | Kstar' => fun t => T (typeD t)
                   | _ => fun _ => unit
                   end t
      with
      | @tyApp Kstar' Kstar' f x =>
        match f as f in mtyp n'
              return match n' as n' return mtyp n' -> Type with
                     | Karr Kstar' Kstar' => fun f => T (typeD (tyApp f x))
                     | _ => fun _ => unit
                     end f ->
                     match n' as n' return mtyp n' -> Type with
                     | Karr Kstar' Kstar' => fun f => T (typeD (tyApp f x))
                     | _ => fun _ => unit
                     end f
        with
        | tyInj (Karr Kstar' Kstar') s' =>
          match symbol_dec s s' with
          | left pf => fun _ => match pf with
                            | eq_refl => tr x
                            end
          | right _ => fun fa => fa
          end
        | _ => fun fa => fa
        end
      | _ => fun fa => fa
      end }.

    Instance Typ1Ok_sym (s : symbol _) : Typ1Ok (Typ1_sym s).
    Proof using.
      constructor.
      { simpl. intros.
        rewrite dec_refl. reflexivity. }
      { intros. simpl. eapply Pstep. constructor. }
      { compute. inversion 1.
        eapply inj_pair2 in H1. assumption. }
      { refine (@elim_mtyp0 _ _ _ _ _ _); try solve [ right ; reflexivity ].
        intro. refine (@elim_mtyp1 _ _ _ _ _ _); try solve [ right; destruct d; reflexivity ].
        simpl. intros. destruct d; try solve [ right; reflexivity ].
        simpl.
        destruct (symbol_dec s s0); try solve [ right ; reflexivity ].
        subst. left. eexists. exists eq_refl. reflexivity. }
      { destruct pf. reflexivity. }
      Unshelve.
      apply kind_eq_dec.
    Qed.

    Instance Typ2_sym (s : symbol (Karr Kstar (Karr Kstar Kstar))) : Typ2 _ (symbolD s) :=
    { typ2 := fun x y => tyApp (tyApp (tyInj _ s) x) y
    ; typ2_cast := fun _ _ => eq_refl
    ; typ2_match := fun T (t : mtyp _) tr =>
        match t as t in mtyp n'
              return match n' as n' return mtyp n' -> Type with
                     | Kstar' => fun t => T (typeD t)
                     | _ => fun _ => unit
                     end t ->
                     match n' as n' return mtyp n' -> Type with
                     | Kstar' => fun t => T (typeD t)
                     | _ => fun _ => unit
                     end t
        with
        | @tyApp Kstar' Kstar' f x =>
          match f as f in mtyp n'
                return match n' as n' return mtyp n' -> Type with
                       | Karr Kstar' Kstar' => fun f => T (typeD (tyApp f x))
                       | _ => fun _ => unit
                       end f ->
                       match n' as n' return mtyp n' -> Type with
                       | Karr Kstar' Kstar' => fun f => T (typeD (tyApp f x))
                       | _ => fun _ => unit
                       end f
          with
          | @tyApp Kstar' (Karr Kstar' Kstar') f y =>
            match f as f in mtyp n'
                  return match n' as n' return mtyp n' -> Type with
                         | Karr Kstar' (Karr Kstar' Kstar') =>
                           fun f => T (typeD (tyApp (tyApp f y) x))
                         | _ => fun _ => unit
                         end f ->
                         match n' as n' return mtyp n' -> Type with
                         | Karr Kstar' (Karr Kstar' Kstar') =>
                           fun f => T (typeD (tyApp (tyApp f y) x))
                         | _ => fun _ => unit
                         end f
            with
            | @tyInj (Karr Kstar' (Karr Kstar' Kstar')) s' =>
              match symbol_dec s s' with
              | left pf => fun _ => match pf with
                                | eq_refl => tr y x
                                end
              | right _ => fun fa => fa
              end
            | _ => fun fa => fa
            end
          | _ => fun fa => fa
          end
        | _ => fun fa => fa
        end }.

    Instance Typ2Ok_sym (s : symbol (Karr Kstar (Karr Kstar Kstar))) : Typ2Ok (Typ2_sym s).
    Proof using.
      constructor.
      { simpl; intros. rewrite dec_refl. reflexivity. }
      { intros. simpl. eapply Ptrans; [ | eapply Pstep; econstructor ].
        econstructor. }
      { constructor. constructor. }
      { compute. inversion 1.
        eapply inj_pair2 in H1. eapply inj_pair2 in H2. tauto. }
      { refine (@elim_mtyp0 _ _ _ _ _ _); try solve [ right; reflexivity ].
        intro. refine (@elim_mtyp1 _ _ _ _ _ _); try solve [ right; destruct d; reflexivity ].
        intro. refine (@elim_mtyp2 _ _ _ _ _ _ _); try solve [ right; destruct d; destruct d'; reflexivity ].
        destruct d; destruct d'; simpl; try solve [right ; reflexivity ].
        intros. destruct (symbol_dec s s0); try solve [ right ; eauto ].
        subst. left. do 2 eexists. exists eq_refl. reflexivity. }
      { destruct pf. reflexivity. }
      Unshelve.
      all: apply kind_eq_dec.
    Qed.

    Instance Typ2_Fun : Typ2 _ RFun :=
    { typ2 := tyArr
    ; typ2_cast := fun _ _ => eq_refl
    ; typ2_match := fun T (x : mtyp _) tr =>
        match x as x in mtyp n'
              return match n' as n' return mtyp n' -> Type with
                     | Kstar' => fun x => T (typeD x)
                     | _ => fun _ => unit
                     end x ->
                     match n' as n' return mtyp n' -> Type with
                     | Kstar' => fun x => T (typeD x)
                     | _ => fun _ => unit
                     end x
        with
        | tyArr l r => fun _ => tr l r
        | _ => fun fa => fa
        end }.

    Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun.
    Proof using.
      constructor.
      { reflexivity. }
      { constructor. constructor. }
      { constructor. constructor. }
      { inversion 1. split; reflexivity. }
      { refine (@elim_mtyp0 _ _ _ _ _ _); try solve [ right ; eauto ].
        simpl. left; do 2 eexists; exists eq_refl; reflexivity. }
      { destruct pf. reflexivity. }
    Qed.

  End with_symbols.

  Arguments tyInj {_} _ _.
  Arguments tyApp {_ _ _} _ _.
  Arguments tyArr {_} _ _.
  Arguments tyProp {_}.
  Arguments tyVar' {_} _ _.
  Arguments tyVar {_} _ _.

End TypeLang_mtypF.
