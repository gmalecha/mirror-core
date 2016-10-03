Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Util.PositivePolyMap.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Polymorphic2.

Set Implicit Arguments.
Set Strict Implicit.

Section poly.
  Context {typ : nat -> Type} {sym : Type}.
  Context {RT : RType (typ 0)}
          {RS : RSym sym}.

  Variable mkVar : forall n, positive -> typ n.

  Variable typ_unify : typ 0 -> typ 0 -> pmap { n : nat & typ n }
                            -> option (pmap { n : nat & typ n }).

  (** NOTE: This function does not need to be complete
   ** TODO: We should really stop looking at the term as
   **       soon as we have instantiated everything
   **)
  Local Fixpoint get_types {T} (a b : expr (typ 0) sym) (s : pmap { n : nat & typ n })
        (ok : pmap { n : nat & typ n } -> T) (bad : T) {struct a}
  : T :=
    match a , b with
    | App fa aa , App fb ab =>
      get_types fa fb s
                (fun s' => get_types aa ab s' ok bad)
                bad
    | Inj a , Inj b =>
      match typeof_sym a
          , typeof_sym b
      with
      | Some ta , Some tb =>
        match typ_unify ta tb s with
        | Some s' => ok s'
        | None => bad
        end
      | _ , _ => bad
      end
    | _ , _ => ok s
    end.

  Local Fixpoint build_vars p (n : list nat) : hlist typ n :=
    match n with
    | nil => Hnil
    | n :: ns => Hcons (mkVar n p) (build_vars (Pos.succ p) ns)
    end.

  Local Fixpoint get_vars {T} n p
  : forall (ok : hlist typ n -> T) (bad : T) (m : pmap { n : nat & typ n }), T :=
    match n as n return (hlist typ n -> T) -> T -> pmap { n : nat & typ n } -> T with
    | nil => fun ok _ _ => ok Hnil
    | n :: ns => fun ok bad m =>
               match pmap_lookup m p with
               | pNone => bad
               | pSome (existT _ n' z) =>
                 match NPeano.Nat.eq_dec n' n with
                 | right _ => bad
                 | left pf =>
                   get_vars (Pos.succ p)
                            (fun vs => ok (Hcons match pf in _ = X return typ X with
                                              | eq_refl => z
                                              end vs)) bad m
                 end
               end
    end.

  Definition get_inst {n} (t : polymorphic typ n (expr (typ 0) sym))
             (w : expr (typ 0) sym)
  : option (hlist typ n) :=
    let t' := inst t (build_vars 1 n) in
    get_types t' w (pmap_empty _)
              (get_vars 1 Some None)
              None.
End poly.