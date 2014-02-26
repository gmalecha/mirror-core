Require Import Coq.Lists.List.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Subst2.

Set Implicit Arguments.
Set Strict Implicit.
(** This is the simplest form of substitution, it only supports lookup.
 ** But, it is efficient to implement.
 **)
Section list_subst.

  (** the [expr] type requires a notion of unification variable **)
  Variable expr : Type.
  Let uvar : Type := nat.

  Inductive list_subst : Type :=
  | Snil : list_subst
  | Sfilled : expr -> list_subst -> list_subst
  | Sempty : list_subst -> list_subst.

  Fixpoint list_subst_lookup (u : uvar) (l : list_subst) : option expr :=
    match l with
      | Snil => None
      | Sfilled x l => match u with
                         | 0 => Some x
                         | S u => list_subst_lookup u l
                       end
      | Sempty l => match u with
                      | 0 => None
                      | S u => list_subst_lookup u l
                    end
    end.

  Section add.
    Variable e : expr.

    Fixpoint list_subst_add (u : uvar) (l : list_subst) : list_subst :=
      match u with
        | 0 => Sfilled e match l with
                           | Snil => Snil
                           | Sfilled _ l => l
                           | Sempty l => l
                         end
        | S u => match l with
                   | Snil => Sempty (list_subst_add u Snil)
                   | Sfilled x l => Sfilled x (list_subst_add u l)
                   | Sempty l => Sempty (list_subst_add u l)
                 end
      end.
  End add.

  Fixpoint list_subst_domain' (l : list_subst) (u : uvar) : list uvar :=
    match l with
      | Snil => nil
      | Sfilled _ l => S u :: list_subst_domain' l (S u)
      | Sempty l => list_subst_domain' l (S u)
    end.

  Definition list_subst_domain (l : list_subst) : list uvar :=
    list_subst_domain' l 0.

  Local Instance Subst_list_subst : @Subst2.Subst list_subst expr :=
  { lookup := list_subst_lookup
  ; domain := list_subst_domain
  }.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : Expr typD expr.

  Definition WellTyped_for_domain (T : Type) (S : Subst T expr)
             (tus tvs : EnvI.tenv typ) (s : T) : Prop :=
    Forall (fun u =>
              match nth_error tus u , lookup u s with
                | _ , None => True
                | None , Some _ => False
                | Some t , Some e =>
                  Safe_expr tus tvs e t
              end) (domain s).

  Definition substD_for_domain (T : Type) (S : Subst T expr)
             (us vs : EnvI.env typD) (s : T) : list Prop :=
    List.map (fun u =>
                match nth_error us u , lookup (expr := expr) u s with
                  | _ , None => True
                  | None , Some _ => False
                  | Some (existT t val) , Some e =>
                    match exprD us vs e t with
                      | Some v => v = val
                      | None => False
                    end
                end) (domain s).

  (** TODO: There should be some reasonably generic proofs for this! **)
  Local Instance SubstOk_list_subst : SubstOk _ Subst_list_subst :=
  { WellFormed_subst := fun _ => True
  ; WellTyped_subst := WellTyped_for_domain Subst_list_subst
  ; substD := substD_for_domain Subst_list_subst
  }.
  Proof.
    admit.
    admit.
    admit.
  Defined.

  Section to_list_subst.
    Variable T : Type.
    Variable Subst_T : Subst T expr.
    Variable SubstOk_T : SubstOk _ _.

    Section prime.
      Variable s : T.

      Fixpoint to_list_subst' (dom : list uvar) (acc : list_subst) : list_subst :=
        match dom with
          | nil => acc
          | d :: dom => to_list_subst' dom (match lookup d s with
                                              | None => acc
                                              | Some e => list_subst_add e d acc
                                            end)
        end.
    End prime.

    Definition to_list_subst (s : T) : list_subst :=
      to_list_subst' s (domain s) Snil.

    Theorem WellFormed_to_list_subst
    : forall s, WellFormed_subst s -> WellFormed_subst (to_list_subst s).
    Proof. compute. auto. Qed.

    Theorem WellTyped_to_list_subst
    : forall tus tvs s,
        WellFormed_subst s ->
        WellTyped_subst tus tvs s ->
        WellTyped_subst tus tvs (to_list_subst s).
    Proof.
      unfold to_list_subst.
      intros tus tvs.
      intros.
      generalize (@WellFormed_domain _ _ _ _ _ _ SubstOk_T s _ H eq_refl).
      red; simpl. red; simpl.
      admit.
    Qed.

    Theorem substD_to_list_subst
    : forall us vs s,
        WellFormed_subst s ->
        Forall (fun x => x) (substD us vs s) ->
        Forall (fun x => x) (substD us vs (to_list_subst s)).
    Proof.
    Admitted.
  End to_list_subst.
End list_subst.