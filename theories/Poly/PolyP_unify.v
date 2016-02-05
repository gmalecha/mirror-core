Require Import ExtLib.Data.HList.
Require Import MirrorCore.Poly.PolyPHOAS.

Section Rtype.
  Context {Fu Fu' : list kind -> kind -> Type}.
  Context {F F' : kind -> Type}.
  Variable Rfu : forall ks k, Fu ks k -> Fu' ks k -> Prop.
  Variable Rf : forall k, F k -> F' k -> Prop.

  Inductive Rtype : forall k, type Fu F k -> type Fu' F' k -> Prop :=
  | RsmVar : forall k v v', Rf k v v' -> Rtype k (smVar v) (smVar v')
  | RsmUVar : forall ks k u u' xs xs',
      Rfu ks k u u' -> True ->
      Rtype _ (smUVar u xs) (smUVar u' xs')
  | RsmArr : forall l r l' r',
      Rtype _ l l' -> Rtype _ r r' -> Rtype _ (smArr l r) (smArr l' r')
  | RsmAbs : forall k1 k2 t t',
      (forall (a : F k1) (b : F' k1), Rf k1 a b -> Rtype k2 (t a) (t' b)) ->
      Rtype _ (smAbs t) (smAbs t')
  | RsmApp : forall k1 k2 f x f' x',
      Rtype _ f f' -> Rtype k1 x x' ->
      Rtype k2 (smApp f x) (smApp f' x').
End Rtype.

Definition kind_eq_dec : forall a b : kind, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Section type_eq_odec.
  Context {Fu : list kind -> kind -> Type}.
  Context {F : kind -> Type}.

  Variable u_odec : forall {ks k} (a b : Fu ks k), option (a = b).
  Variable v_odec : forall {k} (a b : F k), option (a = b).

  Fixpoint type_eq_odec {k} (a : type Fu F k) {struct a}
  : forall b : type Fu F k, option (a = b).
    refine
      match a as a in type _ _ k
            return forall b : type Fu F k, option (a = b)
      with
      | @smVar _ _ k v => fun b : type Fu F k =>
        match b as b in type _ _ k
              return forall v : F k, option (smVar v = b)
        with
        | smVar v' => fun v =>
          match v_odec _ v v' with
          | Some pf => Some (f_equal _ pf)
          | None => None
          end
        | _ => fun _ => None
        end v
      | smUVar _ _ => fun _ => None
      | smArr l r => fun b =>
        match b as b in type _ _ k'
              return option (match k' as k' return type Fu F k' -> Prop with
                             | kStar => fun b => smArr l r = b
                             | _ => fun _ => False
                             end b)
        with
        | smArr l' r' =>
          match type_eq_odec _ l l'
              , type_eq_odec _ r r'
          with
          | Some pf , Some pf' => Some match pf in _ = X
                                           , pf' in _ = Y
                                             return smArr _ _ = smArr _ _ with
                                       | eq_refl , eq_refl => eq_refl
                                       end
          | _ , _ => None
          end
        | _ => None
        end
      | smAbs _ => fun b => None (* Not implementable *)
      | smApp _ _ => fun b => None
      end.
  Defined.
End type_eq_odec.

(** * Unification **)
Section unify_type.

(** With this representation, I lose the fact that Fu determines the list and the kind **)
Let Fu : list kind -> kind -> Type := fun _ _ => nat.
Let F : kind -> Type := fun _ => nat.

Definition TSubst : Type :=
  forall ks k, Fu ks k -> option (hlist (type Fu F) ks -> type Fu F k).

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

Definition F_eq_odec (k : kind) (a b : F k) : option (a = b) :=
  match PeanoNat.Nat.eq_dec a b with
  | left pf => Some pf
  | right _ => None
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
      match type_eq_odec F_eq_odec x match pf with
                                     | eq_refl => l
                                     end
      with
      | Some _ => Some (fun xs => match pf with
                                  | eq_refl => hlist_hd xs
                                  end)
      | None =>
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