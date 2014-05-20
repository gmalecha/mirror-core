Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Poly.TypeI.

Set Implicit Arguments.
Set Strict Implicit.

(** Ocaml **)
Definition UU := Type.
Definition Ustar : UU := Type.
Definition Usmall : Ustar := Type.

Inductive kind :=
| kTy : kind
| kArr : kind -> kind -> kind.

Fixpoint kindD (k : kind) : UU :=
  match k with
    | kTy => Ustar
    | kArr k1 k2 => kindD k1 -> kindD k2
  end.

Module Type OcamlExt.
  Record TypeCtor : Type :=
  { Kind : kind
  ; Value : kindD Kind
  }.

  Parameter Ext : Type.
  Parameter ExtD : Ext -> option TypeCtor.
End OcamlExt.

Module Ocaml (Ext : OcamlExt) (MkCtx : ContextBuilder).
  Definition skind := kind.

  Fixpoint skindD (k : skind) : Ustar :=
    match k with
      | kTy => Usmall
      | kArr k1 k2 => skindD k1 -> skindD k2
    end.

  Module CtxP_skind <: ContextP.
    Definition iT := skind.
    Definition Denote := skindD.
  End CtxP_skind.

  Module Ctx := MkCtx CtxP_skind.

  Definition skindD_to_kindD (k : kind) : option (skindD k -> kindD k) :=
    match k as k return option (skindD k -> kindD k) with
      | kTy => Some (fun x : Usmall => x : Ustar)
      | _ => None
    end.

  Inductive typ :=
  | tPi  : typ -> typ
  | tApp : typ -> typ -> typ
  | tArr : typ -> typ -> typ
  | tVar : nat -> typ
  | tExt : Ext.Ext -> typ.

  (** Forall **)
  Definition Quant_Ctx
  : forall (T : UU) {k : skind} {ks : list skind},
      ((skindD k -> T) -> T) ->
      Ctx.Ctx (k :: ks) T -> Ctx.Ctx ks T :=
    Ctx.Quant_Ctx.

  (** Arrow **)
  Definition Arr_Ctx {ks : list skind} (L R : Ctx.Ctx ks (kindD kTy))
  : Ctx.Ctx ks (kindD kTy) :=
    ap (ap (pure (fun l r => l -> r)) L) R.

  (** Application **)
  Definition App_Ctx {ks : list skind} {k k' : kind}
             (F : Ctx.Ctx ks (kindD (kArr k' k)))
             (X : Ctx.Ctx ks (kindD k'))
  : Ctx.Ctx ks (kindD k) :=
    ap (ap (pure (fun f x => f x)) F) X.

  (** Injection **)
  Definition Inj_Ctx {ks : list skind} (k : kind) (val : kindD k)
  : Ctx.Ctx ks (kindD k) := pure val.


Fixpoint kind_eq (k1 k2 : kind) : option (k1 = k2) :=
  match k1 as k1 , k2 as k2 return option (k1 = k2) with
    | kTy , kTy => Some eq_refl
    | kArr l1 l2 , kArr r1 r2 =>
      match kind_eq l1 r1 , kind_eq l2 r2 with
        | Some pf1 , Some pf2 =>
          Some match pf1 in _ = l , pf2 in _ = r return (kArr l1 l2 = kArr l r) with
                 | eq_refl , eq_refl => eq_refl
               end
        | _ , _ => None
      end
    | _ , _ => None
  end.

Fixpoint nth_mem (ks : list skind) (k : skind) (n : nat) : option (member k ks) :=
  match ks as ks return option (member k ks) with
    | nil => None
    | cons k' ks =>
      match n with
        | 0 => match kind_eq k' k with
                 | Some pf => Some match pf in _ = kk return member kk (cons k' ks) with
                                     | eq_refl => MZ _ _
                                   end
                 | None => None
               end
        | S n => match nth_mem ks k n with
                   | Some m => Some (@MN _ _ _ _ m)
                   | None => None
                 end
      end
  end.

  Fixpoint typD (ks : list skind) (t : typ) (k : kind)
  : option (Ctx.Ctx ks (kindD k)) :=
    match t with
      | tPi t =>
        match k as k return option (Ctx.Ctx ks (kindD k))
        with
          | kTy =>
            match typD (cons kTy ks) t kTy with
              | Some T => Some (Quant_Ctx (k := kTy) (fun P => forall x : Usmall, P x) T)
              | _ => None
            end
          | _ => None
        end
      | tArr t t' =>
        match k as k return option (Ctx.Ctx ks (kindD k))
        with
          | kTy =>
            match typD ks t kTy , typD ks t' kTy with
              | Some K , Some T => Some (Arr_Ctx K T)
              | _ , _ => None
            end
          | _ => None
        end
      | tApp t t' =>
        let k' := kTy in
        (** TODO: This is fine since [tPi] only ranges over [*] **)
        match typD ks t k' , typD ks t (kArr k' k) with
          | Some T , Some F => Some (App_Ctx F T)
          | _ , _ => None
        end
      | tVar v =>
        match skindD_to_kindD k , nth_mem ks k v with
          | Some f , Some m => Some (@fmap _ _ _ _ f (Ctx.Use_Ctx m))
          | _ , _ => None
        end
      | tExt u =>
        match Ext.ExtD u with
          | Some {| Ext.Kind := k' ; Ext.Value := v |} =>
            match kind_eq k' k with
              | Some pf => Some match pf in _ = k return Ctx.Ctx ks (kindD k)
                                with
                                  | eq_refl => Inj_Ctx _ v
                                end
              | None => None
            end
          | None => None
        end
    end.
End Ocaml.
