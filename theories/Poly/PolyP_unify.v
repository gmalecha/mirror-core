Require Import ExtLib.Data.HList.
Require Import MirrorCore.Poly.PolyPHOAS.

(** UNIFICATION **)
Section unify_type.

(** With this representation, I lose the fact that Fu determines the list and the kind **)
Let Fu : list kind -> kind -> Type := fun _ _ => nat.
Let F : kind -> Type := fun _ => nat.

Definition TSubst : Type :=
  forall ks k, Fu ks k -> option (hlist (type Fu F) ks -> type Fu F k).


Definition kind_eq_dec : forall a b : kind, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition type_eq_dec : forall {k} (a b : type Fu F k), {a = b} + {a <> b}.
Proof. Admitted.

Definition TSubst_add {ks k} (u : Fu ks k) (val : hlist (type Fu F) ks -> type Fu F k) (s : TSubst) : TSubst :=
  fun a b x =>
    match PeanoNat.Nat.eq_dec u x with
    | left _ =>
      match List.list_eq_dec kind_eq_dec ks a
            , kind_eq_dec k b
      with
      | left pf , left pf' =>
        Some match pf in _ = X , pf' in _ = Y
                   return hlist (type Fu F) X -> type Fu F Y
             with
             | eq_refl , eq_refl => val
             end
      | _ , _ => None
      end
    | right _ => s a b x
    end.

Fixpoint find_in_list {ks k} (x : type Fu F k) (ls : hlist (type Fu F) ks)
: option (hlist (type Fu F) ks -> type Fu F k) :=
  match ls in hlist _ ks
        return option (hlist (type Fu F) ks -> type Fu F k)
  with
  | Hnil => None
  | @Hcons _ _ k' _ l ls =>
    match kind_eq_dec k' k with
    | left pf =>
      match @type_eq_dec k x match pf with
                             | eq_refl => l
                             end with
      | left _ => Some (fun xs => match pf with
                                  | eq_refl => hlist_hd xs
                                  end)
      | right _ =>
        match find_in_list x ls with
        | None => None
        | Some v => Some (fun x => v (hlist_tl x))
        end
      end
    | right _ =>
      match find_in_list x ls with
      | None => None
      | Some v => Some (fun x => v (hlist_tl x))
      end
    end
  end.

Fixpoint pattern_type {ks k} (a : type Fu F k) (xs : hlist (type Fu F) ks)
: option (hlist (type Fu F) ks -> type Fu F k).
refine
  match find_in_list a xs with
  | Some x => Some x
  | None =>
    match a in type _ _ k
          return option (hlist (type Fu F) ks -> type Fu F k)
    with
    | smUVar _ _ => None (* Bad *)
    | smArr l r =>
      match pattern_type _ _ l xs , pattern_type _ _ r xs with
      | Some l' , Some r' => Some (fun a => smArr (l' a) (r' a))
      | _ , _ => None
      end
    | smApp l r =>
      match pattern_type _ _ l xs , pattern_type _ _ r xs with
      | Some l' , Some r' => Some (fun a => smApp (l' a) (r' a))
      | _ , _ => None
      end
    | smAbs t => None (** TODO **)
    | smVar v => None
    end
  end.
Defined.

Variable unify' : forall {k} (f : nat) (a b : type Fu F k) (s : TSubst), option TSubst.


Definition pattern_add {ks k} (u : Fu ks k) (xs : hlist (type Fu F) ks)
           (e : type Fu F k) (s : TSubst) : option TSubst :=
  match pattern_type e xs with
  | None => None
  | Some o' => Some (TSubst_add u o' s)
  end.

Fixpoint unify_type {k} (f : nat) (a b : type Fu F k) (s : TSubst) {struct a}
: option TSubst.
  refine (
    match a in type _ _ k , b in type _ _ k' return k' = k -> option TSubst with
    | smVar v , smVar v' => fun _ =>
      if PeanoNat.Nat.eq_dec v v' then Some s else None
    | smArr l r , smArr l' r' => fun _ =>
      match unify_type _ f l l' s with
      | Some s' => unify_type _ f r r' s
      | _ => None
      end
    | @smApp _ _ k1 k2 l r , @smApp _ _ k1' k2' l' r' =>
      fun pf =>
        match kind_eq_dec k1' k1 with
        | left pf' =>
          match pf' in _ = X , pf in _ = Y
                return (type Fu F (kArr X Y) -> TSubst -> option TSubst) ->
                       (type Fu F X -> TSubst -> option TSubst) ->
                       option TSubst
          with
          | eq_refl , eq_refl => fun rl rr =>
                                   match rl l' s with
                                   | Some s' => rr r' s'
                                   | _ => None
                                   end
          end (fun x => unify_type _ f l x) (fun x => unify_type _ f r x)
        | right _ => None
        end
    | @smAbs _ _ k1 k2 t , @smAbs _ _ k1' k2' t' => fun pf =>
      match pf in _ = X
            return match X with
                   | kArr a b => (type Fu F b -> TSubst -> option TSubst) -> option TSubst
                   | _ => unit
                   end
      with
      | eq_refl => fun rec => rec (t' f) s
      end (unify_type _ (S f) (t f))
    | @smUVar _ _ ks k u xs , @smUVar _ _ ks' k' u' xs' => fun pf =>
      match PeanoNat.Nat.eq_dec u u' with
      | left pf' =>
        match List.list_eq_dec kind_eq_dec ks' ks with
        | left pf'' =>
          (fix rec ls (xs : hlist (type Fu F) ls) (s : TSubst) : hlist (type Fu F) ls -> option TSubst :=
             match xs in hlist _ ls
                   return hlist (type Fu F) ls -> option TSubst
             with
             | Hnil => fun _ => Some s
             | Hcons x xs => fun ys =>
                               match unify' _ f x (hlist_hd ys) s with
                               | None => None
                               | Some s' => rec _ xs s' (hlist_tl ys)
                               end
             end)
            ks xs s match pf'' with
                    | eq_refl => xs'
                    end
        | _ => None
        end
      | _ =>
        match s _ _ u , s _ _ u' with
        | Some e , Some e' => unify' _ f (e xs) match pf with
                                                | eq_refl => e' xs'
                                                end s
        | Some e , None => pattern_add u' xs' match eq_sym pf with
                                              | eq_refl => e xs
                                              end s
        | None , Some e' => pattern_add u xs match pf with
                                             | eq_refl => e' xs'
                                             end s
        | None , None =>
          match pattern_add u xs match pf with
                                 | eq_refl => smUVar u' xs'
                                 end s with
          | Some s => Some s
          | None => pattern_add u' xs' match eq_sym pf with
                                       | eq_refl => smUVar u xs
                                       end s
          end
        end
      end
    | smUVar u xs , other => fun pf =>
      match s _ _ u with
      | None =>
        pattern_add u xs match pf with
                         | eq_refl => other
                         end s
      | Some e' => unify' _ f (e' xs) match pf with
                                      | eq_refl => other
                                      end s
      end
    | other , smUVar u xs => fun pf =>
      match s _ _ u with
      | None =>
        pattern_add u xs match eq_sym pf with
                         | eq_refl => other
                         end s
      | Some e' => unify' _ f match eq_sym pf with
                              | eq_refl => other
                              end (e' xs) s
      end
    | _ , _ => fun _ => None
    end eq_refl).
Defined.
End unify_type.