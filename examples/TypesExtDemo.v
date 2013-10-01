Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Fun.
Require Import MirrorCore.Iso.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Module example.

  Require Import ExtLib.Data.Nat.
  Require Import ExtLib.Data.List.
  Require Import ExtLib.Data.Fun.

  Inductive my_type : Type :=
  | List : my_type -> my_type
  | Nat : my_type
  | Arr : my_type -> my_type -> my_type
  | Var : nat -> my_type.

  Fixpoint my_typeD (ts : list Type) (t : my_type) : Type :=
    match t with
      | List t => list (my_typeD ts t)
      | Nat => nat
      | Arr d r => my_typeD ts d -> my_typeD ts r
      | Var v => match nth_error ts v with
                   | Some T => T
                   | None => Empty_set
                 end
    end.

  Fixpoint my_type_eq (a b : my_type) {struct a} : option (a = b).
  refine (
    match a , b with
      | Nat , Nat => Some eq_refl
      | List a , List b =>
        match my_type_eq a b with
          | Some pf => Some _
          | None => None
        end
      | Arr ad ar , Arr bd br => 
        match my_type_eq ad bd , my_type_eq ar br with
          | Some _ , Some _ => Some _
          | _ , _ => None
        end
      | Var x , Var y =>
        match EqNat.beq_nat x y as z return z = EqNat.beq_nat x y -> option (Var x = Var y) with
          | true => fun pf => Some _
          | false => fun _ => None
        end eq_refl 
      | _ , _ => None
    end); subst; try reflexivity.
  rewrite (EqNat.beq_nat_eq _ _ pf). reflexivity.
  Defined.
  
  Definition my_type_cast (F : Type -> Type) ts (a b : my_type) : option (F (my_typeD ts a) -> F (my_typeD ts b)) :=
    match my_type_eq a b with
      | None => None
      | Some pf => Some match pf in _ = a' return (F (my_typeD ts a) -> F (my_typeD ts a')) with
                          | eq_refl => fun x => x
                        end
    end.
(* This requires well-founded recursion, e.g. recursion on the sum of the heights
  Fixpoint my_type_cast (a b : my_type) {struct b} : option (my_typeD a -> my_typeD b) :=
    match a as a , b as b return option (my_typeD a -> my_typeD b) with
      | Nat , Nat => Some (fun x => x)
      | List a , List b => 
        match my_type_cast a b with
          | None => None
          | Some f => Some (map f)
        end
      | Arr ad ar , Arr bd br =>
        match my_type_cast bd ad , my_type_cast ar br with
          | Some dcast , Some rcast =>
            Some (fun f => (fun x => rcast (f (dcast x))))
          | _ , _ => None
        end
      | _ , _ => None
    end.
*)

  Fixpoint my_type_eq_valb ts (a : my_type) : my_typeD ts a -> my_typeD ts a -> option bool :=
    match a as a return my_typeD ts a -> my_typeD ts a -> option bool with 
      | Nat => fun x y => Some (x ?[ eq ] y)
      | List a =>
        let C := my_type_eq_valb ts a in
        fix cmp (x y : list (my_typeD ts a)) {struct x} : option bool :=
          match x , y with 
            | nil , nil => Some true
            | x :: xs , y :: ys => 
              match C x y with
                | Some false => Some false
                | None => match cmp xs ys with
                            | Some false => Some false
                            | _ => None
                          end
                | Some true => cmp xs ys
              end
            | _ , _ => Some false
          end
        | Arr _ _ => fun _ _ => None
        | Var _ => fun _ _ => None
    end.

  Definition my_type_of_apply (y : my_type) (x : my_type) : option my_type :=
    match y with
      | Arr d r =>
        match my_type_eq x d with
          | None => None
          | Some _ => Some r
        end
      | _ => None
    end.
  
  Instance RType_my_type : RType my_typeD :=
  { typ_cast := my_type_cast
  ; typ_eqb := {| rel_dec := fun x y => match my_type_eq x y with
                            | Some _ => true
                            | None => false
                          end |}
(*  ; eqb := my_type_eq_valb *)
  ; typeFor := fun ts => fix typeFor t : type (my_typeD ts t) :=
               match t as t return type (my_typeD ts t) with
                 | Nat => type_nat
                 | List t => @type_list _ (typeFor t)
                 | Arr a b => type_Fun (typeFor a) (typeFor b)
                 | Var v => type_libniz _
               end
  ; instantiate_typ := fun _ x => x
  ; type_of_apply := my_type_of_apply
(*  ; type_apply := fun _ _ _ _ _ => None *)
  }.

  Instance TypInstance_nat : @TypInstance0 _ my_typeD nat :=
  { typ0 := Nat
  ; typ0_iso := fun _ => {| Iso.siso := fun F => {| into := fun x => x ; outof := fun x => x |} |}
  ; typ0_match := fun ts R caseNat caseElse t =>
                    match t as t return R t (my_typeD ts t) with
                      | Nat => caseNat tt
                      | _ => caseElse _
                    end
  }.


  Instance TypInstance1_list : @TypInstance1 _ my_typeD list :=
  { typ1 := List
  ; typ1_iso := fun _ _ => {| Iso.siso := fun F => {| into := fun x => x ; outof := fun x => x |} |}
  ; typ1_match := fun ts R caseList caseElse t =>
      match t as t return R t (my_typeD ts t) with
        | List t => caseList t
        | _ => caseElse _
      end
  }.

  Definition Fun D R : Type := D -> R.
  Instance TypInstance2_arr : @TypInstance2 _ my_typeD Fun :=
  { typ2 := Arr
  ; typ2_iso := fun _ _ _ => {| Iso.siso := fun F => {| into := fun x => x ; outof := fun x => x |} |}
  ; typ2_match := fun ts R caseArr caseElse t =>
      match t as t return R t (my_typeD ts t) with
        | Arr t1 t2 => caseArr t1 t2
        | _ => caseElse _
      end
  }.

End example.
