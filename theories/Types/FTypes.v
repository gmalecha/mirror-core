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
          match PeanoNat.Nat.eq_dec n n' with
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