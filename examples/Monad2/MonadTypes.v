Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

(** This is just a positive map to a fixed type universe
 ** Literally this is just [positive_map Type]
 **)
(** TODO: Move this/replace it with pmap **)
Inductive types : Type :=
| TEemp : types
| TEbranch : types -> option Type -> types -> types.

Definition types_left (t : types) : types :=
  match t with
    | TEemp => TEemp
    | TEbranch l _ _ => l
  end.

Definition types_right (t : types) : types :=
  match t with
    | TEemp => TEemp
    | TEbranch l _ _ => l
  end.

Definition types_here (t : types) : option Type :=
  match t with
    | TEemp => None
    | TEbranch _ v _ => v
  end.

Fixpoint types_add (n : positive) (v : Type) (t : types) : types :=
  match n with
    | xH => TEbranch (types_left t) (Some v) (types_right t)
    | xI n => TEbranch (types_left t) (types_here t) (types_add n v (types_right t))
    | xO n => TEbranch (types_add n v (types_left t)) (types_here t) (types_right t)
  end.

Fixpoint list_to_types' (ls : list (option Type)) (n : positive) : types -> types :=
  match ls with
    | nil => fun x => x
    | None :: ls => list_to_types' ls (Pos.succ n)
    | Some v :: ls => fun ts => list_to_types' ls (Pos.succ n) (types_add n v ts)
  end.

Definition list_to_types (ls : list (option Type)) : types :=
  list_to_types' ls 1%positive TEemp.

Fixpoint getType (ts : types) (n : positive) {struct n} : Type :=
  match n with
    | xH => match ts with
              | TEbranch _ (Some T) _ => T
              | _ => Empty_set
            end
    | xO n => getType (types_left ts) n
    | xI n => getType (types_right ts) n
  end.

(** This is the actual monad types **)
Section types.
  Variable m : Type -> Type.
  Variable ts : types.

  (** this type requires decidable equality **)
  Inductive typ : Type :=
  | tyProp
  | tyArr : typ -> typ -> typ
  | tyType : positive -> typ
  | tyM : typ -> typ.

  Section with_env.
    Fixpoint typD (x : typ) {struct x} : Type :=
      match x return Type with
        | tyProp => Prop
        | tyArr l r => typD l -> typD r
        | tyType x => getType ts x
        | tyM x => m (typD x)
      end.

    Definition Rty : typ -> typ -> Prop := @eq _.
    Definition Relim (F : Type -> Type)
               (to from : typ) (pf : Rty to from)
    : F (typD from) -> F (typD to).
      destruct pf. refine (fun x => x).
    Defined.

    Fixpoint positive_eq_odec (a b : positive) : option (a = b) :=
      match a as a , b as b return option (a = b) with
        | xH , xH => Some (eq_refl _)
        | xI a , xI b =>
          match positive_eq_odec a b with
            | None => None
            | Some pf => Some (match pf in _ = b' return xI a = xI b' with
                                 | eq_refl => eq_refl
                               end)
          end
        | xO a , xO b =>
          match positive_eq_odec a b with
            | None => None
            | Some pf => Some (match pf in _ = b' return xO a = xO b' with
                                 | eq_refl => eq_refl
                               end)
          end
        | _ , _ => None
      end.

    Fixpoint type_cast (a b : typ) {struct a} : option (Rty a b) :=
      match a , b with
        | tyProp , tyProp => Some eq_refl
        | tyArr a b , tyArr c d =>
          match type_cast a c , type_cast b d with
            | Some pf1 , Some pf2 =>
              Some match pf1 in _ = t1 , pf2 in _ = t2
                         return tyArr a b = tyArr t1 t2
                   with
                     | eq_refl , eq_refl => eq_refl
                   end
            | _ , _ => None
          end
        | tyType x , tyType y =>
          fmap (@f_equal _ _ tyType _ _) (positive_eq_odec x y)
        | tyM x , tyM y => fmap (@f_equal _ _ tyM _ _) (type_cast x y)
        | _ , _ => None
      end.

  End with_env.

  Inductive tyAcc_typ : typ -> typ -> Prop :=
  | acc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
  | acc_tyArrR : forall a b, tyAcc_typ a (tyArr b a)
  | acc_tyM    : forall a, tyAcc_typ a (tyM a).

  Instance RType_typ : RType typ :=
  { typD := typD
  ; type_cast := type_cast
  ; tyAcc := tyAcc_typ
  }.

  Theorem positive_eq_odec_None
  : forall a b, positive_eq_odec a b = None -> a <> b.
  Proof.
    clear; induction a; destruct b; simpl; try congruence.
    { specialize (IHa b).
      destruct (positive_eq_odec a b); intros; try congruence.
      specialize (IHa eq_refl). congruence. }
    { specialize (IHa b).
      destruct (positive_eq_odec a b); intros; try congruence.
      specialize (IHa eq_refl). congruence. }
  Qed.

  Theorem positive_eq_odec_refl
  : forall a, positive_eq_odec a a = Some eq_refl.
  Proof.
    clear; induction a; simpl; auto; Cases.rewrite_all_goal; auto.
  Qed.

  Instance RTypeOk_typ : @RTypeOk _ RType_typ.
  constructor; simpl; auto.
  { red.
    induction a; simpl; intros; constructor; intros;
    try solve [ inversion H ].
    { inversion H; clear H; subst; auto. }
    { inversion H; clear H; subst; auto. } }
  { destruct pf. reflexivity. }
  { destruct pf1; destruct pf2; reflexivity. }
  { induction x; simpl; intros; auto; Cases.rewrite_all_goal; auto.
    rewrite positive_eq_odec_refl. reflexivity. }
  { admit. }
  Qed.

End types.

Instance Typ2_tyArr ts m : @Typ2 _ (RType_typ ts m) Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match := fun T t tr =>
                  match t as t return T (typD _ _ t) -> T (typD _ _ t) with
                    | tyArr a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.

Instance Typ2Ok_tyArr ts m
: Typ2Ok (Typ2_tyArr ts m).
Proof.
  constructor.
  { reflexivity. }
  { eapply acc_tyArrL. }
  { eapply acc_tyArrR. }
  { unfold TypesI.Rty. simpl.
    inversion 1. auto. }
  { destruct x; simpl; try solve [ right; reflexivity ].
    left. eexists; eexists. exists eq_refl. reflexivity. }
  { destruct pf. reflexivity. }
Qed.
