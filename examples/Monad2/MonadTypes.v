Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda2.ExprDIm.

Set Implicit Arguments.
Set Strict Implicit.

Module Type M.
  Parameter m : Type -> Type.
End M.

Module Type TyExt.
  Parameter ext : Type.
  Parameter extD : ext -> Type.

  Parameter ext_cast : forall a b : ext, option (a = b).
  Parameter ext_cast_refl : forall a, ext_cast a a = Some eq_refl.
  Parameter ext_cast_total : forall a b, ext_cast a b = None -> a <> b.
End TyExt.

Module MonadTypes (TE : TyExt) (M : M)
<: ExprType.
  Inductive typ' : Type :=
  | tyM : typ' -> typ'
  | tyExt : TE.ext -> typ'
  | tyArr : typ' -> typ' -> typ'.

  Definition typ := typ'.

  Fixpoint typD (t : typ) : Type :=
    match t with
      | tyExt e => TE.extD e
      | tyArr a b => typD a -> typD b
      | tyM t => M.m (typD t)
    end.

  Definition Rty : typ -> typ -> Prop := @eq typ.
  Definition Rty_refl : Reflexive Rty := @eq_refl _.
  Definition Rty_trans : Transitive Rty := @eq_trans _.

  Fixpoint type_cast (a b : typ) : option (Rty a b) :=
    match a as a , b as b return option (a = b) with
      | tyExt a , tyExt b =>
        fmap (@f_equal _ _ tyExt _ _) (TE.ext_cast a b)
      | tyArr a1 a2 , tyArr b1 b2 =>
        match type_cast a1 b1 , type_cast a2 b2 with
          | Some pf1 , Some pf2 =>
            Some match pf1 in _ = t , pf2 in _ = t'
                       return tyArr a1 a2 = tyArr t t'
                 with
                   | eq_refl , eq_refl => eq_refl
                 end
          | _ , _ => None
        end
      | tyM a , tyM b => fmap (@f_equal _ _ tyM _ _) (type_cast a b)
      | _ , _ => None
    end.

   Definition typ_arr : typ -> typ -> typ := tyArr.

   Definition arr_match (T : Type -> Type) (t : typ)
     (tr : forall a b : typ, T (typD a -> typD b))
     : T (typD t) -> T (typD t) :=
     match t as t return T (typD t) -> T (typD t) with
       | tyArr a b => fun _ => tr a b
       | _ => fun x => x
     end.

   Definition typD_arr (a b : typ) : typD (typ_arr a b) = (typD a -> typD b) :=
     eq_refl.

   Definition Rcast (T : Type -> Type) (a b : typ) (pf : Rty a b)
   : T (typD a) -> T (typD b) :=
     match pf in _ = t return T (typD a) -> T (typD t) with
       | eq_refl => fun x => x
     end.

   Definition Rcast_refl (T : Type -> Type) (x : typ)
   : Rcast T (Rty_refl x) = (fun x0 : T (typD x) => x0) :=
     eq_refl.

   Definition Rcast_trans (T : Type -> Type) (x y z : typ) (pf : Rty x y)
       (pf' : Rty y z) (result : T (typD x)) :
     Rcast T (Rty_trans pf pf') result =
     Rcast T pf' (Rcast T pf result).
     destruct pf. destruct pf'. reflexivity.
   Defined.

   Fixpoint type_cast_refl (x : typ)
   : type_cast x x = Some (Rty_refl x) :=
     match x as x return type_cast x x = Some (Rty_refl x) with
       | tyM t =>
         match eq_sym (type_cast_refl t) in _ = Z
               return match Z with
                        | Some x => Some (f_equal tyM x)
                        | None => None
                      end = Some (Rty_refl (tyM t))
         with
           | eq_refl => eq_refl
         end
       | tyArr a b =>
         match eq_sym (type_cast_refl a) in _ = Z
             , eq_sym (type_cast_refl b) in _ = Y
               return match Z , Y with
                        | Some x , Some y => Some _
                        | _ , _ => None
                      end = Some (Rty_refl (tyArr a b))
         with
           | eq_refl , eq_refl => eq_refl
         end
       | tyExt e =>
         match eq_sym (TE.ext_cast_refl e) in _ = Z
               return match Z with
                        | Some x => Some (f_equal tyExt x)
                        | None => None
                      end = Some (Rty_refl (tyExt e))
         with
           | eq_refl => eq_refl
         end
     end.

   Definition type_cast_total (x y : typ)
   : type_cast x y = None -> ~ Rty x y.
   Proof.
     induction x; simpl; intros; forward;
     try congruence; auto.
     { subst. intro. inversion H; clear H; subst.
       rewrite type_cast_refl in H0. congruence. }
     { intro. inversion H0; clear H0; subst.
       eapply TE.ext_cast_total in H4. congruence. }
     { intro. inversion H1; clear H1; subst.
       repeat rewrite type_cast_refl in H0. congruence. }
   Qed.

   Definition arr_match_case (x : typ)
   : (exists (d r : typ) (pf : Rty x (typ_arr d r)),
        forall (T : Type -> Type)
          (tr : forall a b : typ, T (typD a -> typD b))
          (fa : T (typD x)),
        arr_match T x tr fa =
        match eq_sym pf in (_ = t) return (T (typD t)) with
        | eq_refl =>
            match eq_sym (typD_arr d r) in (_ = t) return (T t) with
            | eq_refl => tr d r
            end
        end) \/
     (forall (T : Type -> Type) (tr : forall a b : typ, T (typD a -> typD b))
        (fa : T (typD x)), arr_match T x tr fa = fa).
   Proof.
     destruct x; simpl; auto.
     { left. exists x1; exists x2; exists eq_refl.
       simpl. auto. }
   Defined.

   Definition arr_match_typ_arr (a b : typ) (T : Type -> Type)
              (tr : forall a0 b0 : typ, T (typD a0 -> typD b0))
              (fa : T (typD (typ_arr a b)))
   : arr_match T (typ_arr a b) tr fa =
     match eq_sym (typD_arr a b) in (_ = t) return (T t) with
     | eq_refl => tr a b
     end :=
     eq_refl.

   Definition Rty_typ_arr (a b c d : typ)
   : Rty (typ_arr a b) (typ_arr c d) <-> Rty c a /\ Rty b d.
     split.
     { inversion 1. split; reflexivity. }
     { unfold Rty. destruct 1. subst; reflexivity. }
   Qed.
End MonadTypes.