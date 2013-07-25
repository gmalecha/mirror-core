Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Core.Type.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section Env.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.

  (** Environments **)
  Definition tenv : Type := list typ.
  Definition env : Type := list (sigT (typD nil)).
  
  Definition typeof_env (e : env) : tenv :=
    map (@projT1 _ _) e.

  Definition lookupAs (e : env) (n : nat) (ty : typ) : option (typD nil ty) :=
    match nth_error e n with
      | None => None
      | Some (existT t v) =>
        match typ_cast (fun x => x) nil t ty with
          | Some f => Some (f v)
          | None => None
        end
    end.

  Theorem lookupAs_weaken : forall (a b : env) n t x, 
    lookupAs a n t = Some x ->
    lookupAs (a ++ b) n t = Some x.
  Proof.
    clear. unfold lookupAs. intros.
    consider (nth_error a n); intros; try congruence.    
    erewrite nth_error_weaken by eassumption. auto.
  Qed.
  
  Fixpoint split_env (gs : env) : sigT (hlist (typD nil)) :=
    match gs with
      | nil => existT _ nil Hnil
      | g :: gs =>
        let res := split_env gs in
        existT _ (projT1 g :: projT1 res) (Hcons (projT2 g) (projT2 res))
    end.

  Theorem split_env_app : forall gs gs', 
    split_env (gs ++ gs') = 
    let (a,b) := split_env gs in
    let (c,d) := split_env gs' in
    existT _ (a ++ c) (hlist_app b d).
  Proof.
    induction gs; simpl; intros.
    { destruct (split_env gs'); reflexivity. }
    { destruct a. rewrite IHgs.
      destruct (split_env gs).
      destruct (split_env gs'). reflexivity. }
  Qed.

End Env.
