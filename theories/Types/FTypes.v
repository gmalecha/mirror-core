(* Representation of first-order types *)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.SigT.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Eq.

Require Import MirrorCore.Util.PolyAcc.
Require Import MirrorCore.Util.PositivePolyMap.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Views.TypeView.

Require Import MirrorCore.Types.ModularTypesT.

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

    Variable symbol : kind -> Set.

    Unset Elimination Schemes.

    Inductive type' : kind -> Set :=
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

    Section type0_case.
      Variable P : type 0 -> Prop.
      Hypotheses  (Harr : forall {a b}, P (tyArr a b))
                  (Hbase0 : forall s, P (tyBase0 s))
                  (Hbase1 : forall s {a}, P (tyBase1 s a))
                  (Hbase2 : forall s {a b}, P (tyBase2 s a b))
                  (Happ : forall {n} s ms, P (@tyApp n s ms))
                  (Hprop : P tyProp)
                  (Hvar : forall p, P (tyVar' Kstar p)).
      Fixpoint type0_case (x : type 0) : P x :=
        match x as x in type' 0 return P x with
        | tyArr a b => Harr _ _
        | tyBase0 s => Hbase0 s
        | tyBase1 s a => Hbase1 s _
        | tyBase2 s a b => Hbase2 s _ _
        | tyApp s ms =>
          Happ _ s ms
        | tyProp => Hprop
        | tyVar' 0 p => Hvar p
        end.
    End type0_case.

    Variable ts : TSym kindD symbol.

    Fixpoint default_type_for_kind n : kindD n :=
      match n as n return kindD n with
      | 0 => Empty_set
      | S b => fun _ => default_type_for_kind b
      end.


    Fixpoint typeD {k} (t : type k) : kindD k :=
      match t in type' k return kindD k with
      | tyArr a b => typeD a -> typeD b
      | tyBase0 s => symbolD kindD s
      | tyBase1 s m => symbolD kindD s (typeD m)
      | tyBase2 s m1 m2 => symbolD kindD s (typeD m1) (typeD m2)
      | tyApp s ms => applyn (symbolD kindD s) (vector_map typeD ms)
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

    Lemma Injective_tyArr : forall a b c d, tyArr a b = tyArr c d -> a = c /\ b = d.
    Proof.
      inversion 1; auto.
    Defined.

    Lemma Injective_tyBase0 : forall a b, tyBase0 a = tyBase0 b -> a = b.
    Proof.
      inversion 1; auto.
    Defined.

    Lemma Injective_tyBase1 : forall a b c d, tyBase1 a b = tyBase1 c d -> a = c /\ b = d.
    Proof.
      inversion 1; auto.
    Defined.

    Lemma Injective_tyBase2 : forall a b c d e f, tyBase2 a b c = tyBase2 d e f -> a = d /\ b = e /\ c = f.
    Proof.
      inversion 1; auto.
    Defined.

    Lemma Injective_tyApp : forall n a b c d, @tyApp n a b = @tyApp n c d -> a = c /\ b = d.
    Proof.
      intros.
      refine
        (match H in _ = Z
               return match Z return Prop with
                      | @tyApp N C D => forall pf : N = n,
                          a = match pf with
                              | eq_refl => C
                              end /\ b = match pf with
                                        | eq_refl => D
                                        end
                      | _ => True
                      end
         with
         | eq_refl => _
         end eq_refl).
      intros. rewrite (UIP_refl pf). tauto.
    Defined.

    Fixpoint type_eq_dec {k} (a : type k) : forall b, {a = b} + {a <> b}.
    refine
      match a as a in type' k
            return forall b : type k, {a = b} + {a <> b}
      with
      | tyArr l r => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyArr l r = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyArr l r <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | tyArr l' r' =>
          match type_eq_dec _ l l' , type_eq_dec _ r r' with
          | left pf , left pf' => left match pf , pf' with
                                      | eq_refl , eq_refl => eq_refl
                                      end
          | _ , _ => right _
          end
        | _ => right _
        end
      | tyBase0 l => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyBase0 l = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyBase0 l <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | tyBase0 l' =>
          match symbol_dec _ l l' with
          | left pf => left _
          | _ => right _
          end
        | _ => right _
        end
      | tyBase1 l r => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyBase1 l r = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyBase1 l r <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | tyBase1 l' r' =>
          match symbol_dec _ l l' , type_eq_dec _ r r' with
          | left pf , left pf' => left _
          | _ , _ => right _
          end
        | _ => right _
        end
      | tyBase2 l r x => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyBase2 l r x = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyBase2 l r x <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | tyBase2 l' r' x' =>
          match symbol_dec _ l l' , type_eq_dec _ r r' , type_eq_dec _ x x' with
          | left pf , left pf' , left pf'' => left _
          | _ , _ , _ => right _
          end
        | _ => right _
        end
      | @tyApp n s xs => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyApp s xs = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyApp s xs <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | @tyApp n' s' xs' =>
          match kind_eq_dec n n' with
          | left pf =>
            match pf in _ = N
                  return forall (s' : symbol (3+N)) (xs' : vector _ (3+N)),
                           {@tyApp n s xs = @tyApp N s' xs'} +
                           {@tyApp n s xs <> @tyApp N s' xs'}
            with
            | eq_refl => fun s' xs' =>
              match symbol_dec _ s s' , vector_dec (@type_eq_dec Kstar) xs xs' with
              | left pf , left pf' => left _
              | _ , _ => right _
              end
            end s' xs'
          | right _ => right _
          end
        | _ => right _
        end
      | tyProp => fun b =>
        match b as b in type' z
              return {match z as z return type' z -> Prop with
                      | 0 => fun b => tyProp = b
                      | _ => fun _ => False
                      end b} + {match z as z return type' z -> Prop with
                                | 0 => fun b => tyProp <> b
                                | _ => fun _ => True
                                end%type b}
        with
        | tyProp => left _
        | _ => right _
        end
      | tyVar' _ n => fun b =>
        match b as b in type' z
              return {tyVar' _ n = b} + {tyVar' _ n <> b}
        with
        | tyVar' _ n' =>
          match Pos.eq_dec n n' with
          | left pf => left _
          | _ => right _
          end
        | _ => right _
        end
      end.
    all: try solve [ subst ; reflexivity
                   | clear ; intro pf; inversion pf
                   | intro pf ; inversion pf; auto
                   | destruct k0; auto; inversion 1 ].
    { intro. apply Injective_tyApp in H. tauto. }
    { intro. apply Injective_tyApp in H. tauto. }
    Defined.

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

    Lemma if_as_and : forall a b : bool, (if a then b else false) = true <-> (a = true /\ b = true).
    Proof. destruct a; destruct b; tauto. Defined.

    Section vector_bdec.
      Context {T : Type}.
      Variable bdec : T -> T -> bool.
      Fixpoint vector_bdec {n} (v1 : vector T n) : vector T n -> bool :=
        match v1 in vector _ n return vector T n -> bool with
        | Vnil _ => fun _ => true
        | Vcons v vs => fun v' =>
          match v' in vector _ (S n) return (vector T n -> bool) -> bool with
          | Vcons v' vs' => fun rec => if bdec v v' then rec vs' else false
          end (fun vs' => vector_bdec vs vs')
        end.

      Hypothesis bdec_ok : forall a b, bdec a b = true <-> a = b.
      Theorem vector_bdec_ok : forall n a b, @vector_bdec n a b = true <-> a = b.
      Proof.
        induction a; simpl.
        { split; auto. rewrite (vector_eta b). reflexivity. }
        { intro. rewrite (vector_eta b).
          rewrite if_as_and. rewrite bdec_ok. rewrite IHa.
          split.
          { destruct 1; subst; auto. }
          { intros.
            refine
              match eq_sym H in _ = X
                    return vector_hd X = vector_hd b /\ vector_tl X = vector_tl b
              with
              | eq_refl => conj eq_refl eq_refl
              end. } }
      Defined.
    End vector_bdec.

    Fixpoint type_bdec {k} (a : type k) {struct a} : type k -> bool :=
      match a in type' k
            return type' k -> bool
      with
      | tyArr l r => fun b => match b with
                          | tyArr l' r' => if type_bdec l l' then type_bdec r r' else false
                          | _ => false
                          end
      | tyBase0 s => fun b => match b with
                          | tyBase0 s' => if symbol_dec kindD s s' then true else false
                          | _ => false
                          end
      | tyBase1 s x => fun b =>
        match b with
        | tyBase1 s' x' => if symbol_dec kindD s s' then type_bdec x x' else false
        | _ => false
        end
      | tyBase2 s x y => fun b =>
        match b with
        | tyBase2 s' x' y' =>
          if symbol_dec kindD s s' then
            if type_bdec x x' then type_bdec y y' else false
          else false
        | _ => false
        end
      | @tyApp n s xs => fun b =>
        match b with
        | @tyApp n' s' xs' =>
          match PeanoNat.Nat.eq_dec n n' with
          | left pf =>
            match pf in _ = X return symbol (3+X) -> vector (type 0) (3+X) -> bool with
            | eq_refl => fun s' xs' =>
              if symbol_dec kindD s s' then vector_bdec (@type_bdec 0) xs xs' else false
            end s' xs'
          | right _ => false
          end
        | _ => false
        end
      | tyProp => fun b => match b with
                       | tyProp => true
                       | _ => false
                       end
      | @tyVar' k v => fun b => match b with
                            | @tyVar' _ v' => v ?[ eq ] v'
                            | _ => false
                            end
      end.

    (** TODO(gmalecha): this proof can be cleaned up. *)
    Theorem type_bdec_ok : forall k a b, @type_bdec k a b = true <-> a = b.
    Proof.
      refine
        (fix rec k (a : type k) {struct a} : forall b, type_bdec a b = true <-> a = b :=
           match a as a in type' k
                 return forall b, type_bdec a b = true <-> a = b
           with
           | tyArr l r => _
           | _ => _
           end); simpl.
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ].
        { rewrite if_as_and. do 2 rewrite rec; clear rec.
          split.
          { destruct 1; subst; reflexivity. }
          { apply Injective_tyArr. } } }
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ].
        { destruct (symbol_dec kindD s s0); subst; split; try tauto.
          { inversion 1. }
          { inversion 1. auto. } } }
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ].
        destruct (symbol_dec kindD s s0).
        { rewrite rec; clear rec; split; subst; auto.
          intro; subst; auto.
          intro. eapply Injective_tyBase1 in H. tauto. }
        { split; try congruence.
          intro. apply Injective_tyBase1 in H. tauto. } }
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ].
        destruct (symbol_dec kindD s s0); subst.
        { rewrite if_as_and. do 2 rewrite rec; clear rec.
          split.
          { destruct 1; subst; reflexivity. }
          { intro. apply Injective_tyBase2 in H. tauto. } }
        { split; try congruence.
          intro. apply Injective_tyBase2 in H. tauto. } }
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ].
        destruct (PeanoNat.Nat.eq_dec n n0); subst.
        { lazymatch goal with
          | |- context [ if ?X then _ else _ ] => destruct X
          end; subst.
          { rewrite vector_bdec_ok; eauto.
            split; intros; subst; auto.
            apply Injective_tyApp in H. tauto. }
          { split. inversion 1. intros.
            apply Injective_tyApp in H; tauto. } }
        { split; inversion 1; tauto. } }
      { induction b using type0_case; simpl;
          try solve [ split; try congruence; inversion 1 ]. }
      { destruct b; try solve [ split; try congruence; inversion 1 ].
        rewrite rel_dec_correct.
        split; intro; subst; auto.
        inversion H; auto. }
    Defined.

    Global Instance RelDec_eq_mtyp k : RelDec (@eq (type' k)) :=
    { rel_dec := @type_bdec k }.

    Global Instance RelDecOk_eq_mtyp k : RelDec_Correct (RelDec_eq_mtyp k).
    Proof.
      constructor.
      eapply type_bdec_ok.
    Defined.

    Instance Typ0_Prop : Typ0 RType_type Prop :=
    { typ0 := tyProp
    ; typ0_cast := eq_refl
    ; typ0_match := fun T t f =>
                      match t as t in type' 0
                            return T (typD t) -> T (typD t)
                      with
                      | tyProp => fun _ => f
                      | tyVar' k _ =>
                        match k with
                        | 0 => fun d => d
                        | _ => idProp
                        end
                      | _ => fun d => d
                      end
    }.

    Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop :=
    { typ0_match_iota := fun _ _ _ => eq_refl
    ; typ0_match_case := fun x => _
    ; typ0_match_Proper := _
    }.
    { refine
        match x as x in type' 0
              return (exists pf : Rty x (typ0 (F:=Prop)),
                         forall (T : Type -> Type) (tr : T Prop) (fa : T (typD x)),
                           typ0_match T x tr fa =
                           Relim T pf
                                 match eq_sym (typ0_cast (F:=Prop)) in (_ = t) return (T t) with
                                 | eq_refl => tr
                                 end) \/
                     (forall (T : Type -> Type) (tr : T Prop) (fa : T (typD x)), typ0_match T x tr fa = fa)
        with
        | tyProp => _
        | _ => _
        end; try solve [ right; reflexivity ].
      left. exists eq_refl. reflexivity.
      destruct k; auto using idProp. }
    { destruct pf. reflexivity. }
    Defined.

    Instance Typ2_Fun : Typ2 RType_type RFun :=
    { typ2 := tyArr
    ; typ2_cast := fun _ _ => eq_refl
    ; typ2_match := fun T t f =>
                      match t as t in type' 0
                            return T (typD t) -> T (typD t)
                      with
                      | tyArr d c => fun _ => f d c
                      | tyVar' k _ =>
                        match k with
                        | 0 => fun d => d
                        | _ => idProp
                        end
                      | _ => fun d => d
                      end
    }.

    Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun :=
    { typ2_match_iota := fun _ _ _ _ _ => eq_refl
    ; tyAcc_typ2L := tyAcc_tyArrL
    ; tyAcc_typ2R := tyAcc_tyArrR
    ; typ2_inj := Injective_tyArr
    ; typ2_match_case := fun x => _
    ; typ2_match_Proper := _
    }.
    { refine
        match x as x in type' 0
              return (exists (d r : type Kstar) (pf : Rty x (typ2 d r)),
     forall (T : Type -> Type) (tr : forall a b : type Kstar, T (RFun (typD a) (typD b)))
       (fa : T (typD x)),
     typ2_match T x tr fa =
     Relim T pf
       match eq_sym (typ2_cast d r) in (_ = t) return (T t) with
       | eq_refl => tr d r
       end) \/
  (forall (T : Type -> Type) (tr : forall a b : type Kstar, T (RFun (typD a) (typD b)))
     (fa : T (typD x)), typ2_match T x tr fa = fa)
        with
        | tyArr _ _ => _
        | _ => _
        end; try solve [ right ; reflexivity ].
      { left. do 2 eexists. exists eq_refl. reflexivity. }
      { destruct k; auto using idProp. } }
    { destruct pf; reflexivity. }
    Defined.

    Global Instance Typ0_sym (s : symbol Kstar) : Typ0 RType_type (symbolD kindD s) :=
    { typ0 := tyBase0 s
    ; typ0_cast := eq_refl
    ; typ0_match := fun T r m =>
                      match r as r in type' 0
                            return T (typeD r) -> T (typeD r) with
                      | tyBase0 s' =>
                        match symbol_dec _ s s' with
                        | left pf => match pf with
                                    | eq_refl => fun _ => m
                                    end
                        | right _ => fun x => x
                        end
                      | tyVar' k _ => match k with
                                     | 0 => fun x => x
                                     | _ => idProp
                                     end
                      | _ => fun x => x
                      end }.

    Global Instance Typ0Ok_sym (s : symbol Kstar) : Typ0Ok (Typ0_sym s) :=
    { typ0_match_iota := _
    ; typ0_match_case := _
    ; typ0_match_Proper := _
    }.
    { simpl. intros. destruct (symbol_dec kindD s s); [ | exfalso; eauto ].
      rewrite (UIP_refl e). reflexivity. }
    { intros.
      induction x using type_ind; try solve [ right ; reflexivity ].
      simpl. destruct (symbol_dec kindD s s0); try solve [ right; reflexivity ].
      subst. left; exists eq_refl; reflexivity. }
    { destruct pf; reflexivity. }
    Unshelve. apply (symbol_dec kindD).
    Defined.

    Global Instance Typ1_sym (s : symbol 1) : Typ1 RType_type (symbolD kindD s) :=
    { typ1 := tyBase1 s
    ; typ1_cast := fun _ => eq_refl
    ; typ1_match := fun T r m =>
                      match r as r in type' 0
                            return T (typeD r) -> T (typeD r) with
                      | tyBase1 s' x =>
                        match symbol_dec _ s s' with
                        | left pf => match pf with
                                    | eq_refl => fun _ => m x
                                    end
                        | right _ => fun x => x
                        end
                      | tyVar' k _ => match k with
                                     | 0 => fun x => x
                                     | _ => idProp
                                     end
                      | _ => fun x => x
                      end }.

    Global Instance Typ1Ok_sym (s : symbol 1) : Typ1Ok (Typ1_sym s) :=
    { typ1_match_iota := _
    ; typ1_match_case := _
    ; typ1_match_Proper := _
    }.
    { simpl. intros. destruct (symbol_dec kindD s s); [ | exfalso; eauto ].
      rewrite (UIP_refl e). reflexivity. }
    { constructor. }
    { inversion 1. reflexivity. }
    { intros.
      induction x using type_ind; try solve [ right ; reflexivity ].
      simpl. destruct (symbol_dec kindD s s0); try solve [ right; reflexivity ].
      subst. left; eexists; exists eq_refl; reflexivity. }
    { destruct pf; reflexivity. }
    Unshelve. apply (symbol_dec kindD).
    Defined.

    Global Instance Typ2_sym (s : symbol 2) : Typ2 RType_type (symbolD kindD s) :=
    { typ2 := tyBase2 s
    ; typ2_cast := fun _ _ => eq_refl
    ; typ2_match := fun T r m =>
                      match r as r in type' 0
                            return T (typeD r) -> T (typeD r) with
                      | tyBase2 s' x y =>
                        match symbol_dec _ s s' with
                        | left pf => match pf with
                                    | eq_refl => fun _ => m x y
                                    end
                        | right _ => fun x => x
                        end
                      | tyVar' k _ => match k with
                                     | 0 => fun x => x
                                     | _ => idProp
                                     end
                      | _ => fun x => x
                      end }.

    Global Instance Typ2Ok_sym (s : symbol 2) : Typ2Ok (Typ2_sym s) :=
    { typ2_match_iota := _
    ; typ2_match_case := _
    ; typ2_match_Proper := _
    }.
    { simpl. intros. destruct (symbol_dec kindD s s); [ | exfalso; eauto ].
      rewrite (UIP_refl e). reflexivity. }
    { constructor. }
    { constructor. }
    { inversion 1. split; reflexivity. }
    { intros.
      induction x using type_ind; try solve [ right ; reflexivity ].
      simpl. destruct (symbol_dec kindD s s0); try solve [ right; reflexivity ].
      subst. left; do 2 eexists; exists eq_refl; reflexivity. }
    { destruct pf; reflexivity. }
    Unshelve. apply (symbol_dec kindD).
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

Module TypeLangUnify_mtyp <: TypeLangUnify with Module RT := TypeLang_mtyp.
  Module RT := TypeLang_mtyp.
  Import RT.

  Section with_symbols.
    Variable tsym : kind -> Set.

    Definition Sub := pmap { k : kind & type tsym k }.
    Definition add {n} (a :  positive) (b : type tsym n) (c : Sub)
    : option Sub := Some (pmap_insert a c (@existT _ _ n b)).

    Fixpoint type_unify {k} (a b : type tsym k) (s : Sub) {struct a}
    : option Sub :=
      match a with
      | @tyArr _ da ca =>
        match b with
        | @tyArr _ db cb =>
          match type_unify da db s with
          | Some s' => type_unify ca cb s'
          | _ => None
          end
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase0 _ _ =>
        match b with
        | @tyBase0 _ _ => Some s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase1 _ _ ta =>
        match b with
        | @tyBase1 _ _ tb => type_unify ta tb s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase2 _ _ ta ta' =>
        match b with
        | @tyBase2 _ _ tb tb' =>
          match type_unify ta tb s with
          | Some s' => type_unify ta' tb' s'
          | _ => None
          end
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyApp _ _ _ va =>
        match b with
        | @tyApp _ _ _ vb =>
          (fix go n n' (va : Vector.vector _ n) (vb : Vector.vector _ n') (s : Sub)
           : option Sub :=
             match va , vb with
             | Vector.Vnil _ , Vector.Vnil _ => Some s
             | Vector.Vcons a va , Vector.Vcons b vb =>
               match type_unify a b s with
               | Some s' => go _ _ va vb s'
               | _ => None
               end
             | _ , _ => None
             end) _ _ va vb s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyProp _ => match b with
                 | @tyProp _ => Some s
                 | @tyVar' _ _ v => add v a s
                 | _ => None
                 end
      | @tyVar' _ _ v =>
        match b with
        | @tyVar' _ _ v' => Some s
        | _ => add v b s
        end
      end.

  End with_symbols.

End TypeLangUnify_mtyp.

Export MirrorCore.Types.ModularTypesT.

Definition kind : Set := TypeLang_mtyp.kind.
Definition kindD : kind -> Type@{Ukind} := TypeLang_mtyp.kindD.
Definition Kstar : kind := TypeLang_mtyp.Kstar.
Definition Karr : kind -> kind := S.

Definition ctyp : (kind -> Set) -> kind -> Set:= TypeLang_mtyp.type.
Definition ctype (tsym : kind -> Set) : Set := ctyp tsym Kstar.

Definition TSub : (kind -> Set) -> Set := TypeLangUnify_mtyp.Sub.
Definition ctype_unify {tsym : kind -> Set} : ctype tsym -> ctype tsym -> TSub tsym -> option (TSub tsym) :=
  @TypeLangUnify_mtyp.type_unify tsym Kstar.

Definition RType_ctype := @TypeLang_mtyp.RType_type.
Definition RTypeOk_ctype := @TypeLang_mtyp.RTypeOk_type.

Global Existing Instance TypeLang_mtyp.RType_type.
Global Existing Instance TypeLang_mtyp.RTypeOk_type.

Definition tyArr : forall {tsym : kind -> Set}, ctype tsym -> ctype tsym -> ctype tsym :=
  @TypeLang_mtyp.tyArr.
Definition tyBase0 : forall {tsym : kind -> Set}, tsym Kstar -> ctype tsym :=
  @TypeLang_mtyp.tyBase0.
Definition tyBase1 : forall {tsym : kind -> Set}, tsym (Karr Kstar) -> ctype tsym -> ctype tsym :=
  @TypeLang_mtyp.tyBase1.
Definition tyBase2 : forall {tsym : kind -> Set}, tsym (Karr (Karr Kstar)) -> ctype tsym -> ctype tsym -> ctype tsym :=
  @TypeLang_mtyp.tyBase2.
Definition tyApp : forall {tsym : kind -> Set} (k : kind), tsym (Karr (Karr (Karr k))) -> vector (ctype tsym) (3 + k) -> ctype tsym :=
  @TypeLang_mtyp.tyApp.
Definition tyProp : forall {tsym : kind -> Set}, ctype tsym := @TypeLang_mtyp.tyProp.
Definition tyVar {tsym : kind -> Set} (v : positive) : ctype tsym :=
  TypeLang_mtyp.tyVar Kstar v.

Global Existing Instance TypeLang_mtyp.Typ0_Prop.
Global Existing Instance TypeLang_mtyp.Typ0Ok_Prop.
Global Existing Instance TypeLang_mtyp.Typ2_Fun.
Global Existing Instance TypeLang_mtyp.Typ2Ok_Fun.

Definition Typ0_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym Kstar),
    Typ0 (RType_ctype tsym ts) (symbolD kindD s) := @TypeLang_mtyp.Typ0_sym.
Definition Typ0Ok_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym Kstar),
    Typ0Ok (Typ0_sym s) := TypeLang_mtyp.Typ0Ok_sym.
Definition Typ1_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym (Karr Kstar)),
    Typ1 (RType_ctype tsym ts) (symbolD kindD s) := TypeLang_mtyp.Typ1_sym.
Definition Typ1Ok_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym (Karr Kstar)),
    Typ1Ok (Typ1_sym s) := TypeLang_mtyp.Typ1Ok_sym.
Definition Typ2_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym (Karr (Karr Kstar))),
    Typ2 (RType_ctype tsym ts) (symbolD kindD s) := TypeLang_mtyp.Typ2_sym.
Definition Typ2Ok_sym : forall {tsym : kind -> Set} {ts : TSym kindD tsym} (s : tsym (Karr (Karr Kstar))),
    Typ2Ok (Typ2_sym s) := TypeLang_mtyp.Typ2Ok_sym.
