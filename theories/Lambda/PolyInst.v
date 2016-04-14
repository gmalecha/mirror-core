Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.Vector.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Views.View.

Set Implicit Arguments.
Set Strict Implicit.

Section poly.
  Context {typ : Type} {sym : Type}.
  Context {RT : RType typ}
          {RS : RSym sym}.

  Inductive VType : Type :=
  | tVar : positive -> VType.

  Context {PV_vtype : PartialView typ VType}.

  Variable typ_unify : typ -> typ -> pmap typ -> option (pmap typ).

  Definition type_remember (p : positive) (t : typ) (m : pmap typ)
  : option (pmap typ) :=
    Some (pmap_insert p t m).

  (** NOTE: This function does not need to be complete
   ** TODO: We should really stop looking at the term as
   **       soon as we have instantiated everything
   **)
  Fixpoint get_types {T} (a b : expr typ sym) (s : pmap typ)
           (ok : pmap typ -> T) (bad : T) {struct a}
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

  Fixpoint polymorphic (n : nat) T : Type :=
    match n with
    | 0 => T
    | S n => typ -> polymorphic n T
    end.

  Fixpoint inst {T} (n : nat)
  : polymorphic n T -> vector typ n -> T :=
    match n as n return polymorphic n T -> vector typ n -> T with
    | 0 => fun p _ => p
    | S n => fun p a => inst (p (Vector.vector_hd a)) (Vector.vector_tl a)
    end.

  Fixpoint build_vector p (n : nat) : vector typ n :=
    match n with
    | 0 => Vnil _
    | S n => Vcons (f_insert (tVar p)) (build_vector (Pos.succ p) n)
    end.

  Fixpoint get_vector {T} n p
  : forall (ok : vector typ n -> T) (bad : T) (m : pmap typ), T :=
    match n as n return (vector typ n -> T) -> T -> pmap typ -> T with
    | 0 => fun ok _ _ => ok (Vnil _)
    | S n => fun ok bad m =>
               match pmap_lookup p m with
               | None => bad
               | Some z => get_vector (Pos.succ p)
                                      (fun vs => ok (Vcons z vs)) bad m
               end
    end.

  Definition get_inst {n} (t : polymorphic n (expr typ sym)) (w : expr typ sym)
  : option (vector typ n) :=
    let t' := inst t (build_vector 1 n) in
    get_types t' w (pmap_empty _)
              (get_vector 1 Some None)
              None.
End poly.