Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Lib.NatView.
Require Import MirrorCore.Lib.ProdView.
Require Import MirrorCore.Lib.ListView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Printing Universes.

Inductive listOp_func (typ : Set) : Set :=
| pLength : typ -> listOp_func typ
| pNoDup : typ -> listOp_func typ
| pIn : typ -> listOp_func typ
| pMap : typ -> typ -> listOp_func typ
| pFold : typ -> typ -> listOp_func typ
| pCombine : typ -> typ -> listOp_func typ.

Section ListOpFuncInst.
  Context {typ : Set} {RType_typ : RType typ}.
  Context {func : Set}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  Context {Typ1_tyList : Typ1 _ list}.
  Context {Typ0_tyProp : Typ0 _ Prop}.
  Context {Typ0_tyNat : Typ0 _ nat}.

  Context {Typ0_tyPropOk : Typ0Ok Typ0_tyProp}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  Let tyList : typ -> typ := @typ1 _ _ _ Typ1_tyList.
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyNat : typ := @typ0 _ _ _ Typ0_tyNat.

  Definition typeof_listOp_func lf :=
    match lf with
    | pLength t => Some (tyArr (tyList t) tyNat)
    | pNoDup t => Some (tyArr (tyList t) tyProp)
    | pIn t => Some (tyArr t (tyArr (tyList t) tyProp))
    | pMap t1 t2 => Some (tyArr (tyArr t1 t2) (tyArr (tyList t1) (tyList t2)))
    | pFold t1 t2 =>
      Some (tyArr (tyArr t2 (tyArr t1 t1)) (tyArr t1 (tyArr (tyList t2) t1)))
    | pCombine t1 t2 =>
      Some (tyArr (tyList t1) (tyArr (tyList t2) (tyList (tyProd t1 t2))))
    end.

  Definition listOp_func_eq (a b : listOp_func typ) : option bool :=
    match a , b with
      | pLength t1, pLength t2 => Some (t1 ?[ eq ] t2)
      | pNoDup t1, pNoDup t2 => Some (t1 ?[ eq ] t2)
      | pIn t1, pIn t2 => Some (t1 ?[ eq ] t2)
      | pMap t1 t2, pMap t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				   t2 ?[ eq ] t4)%bool
      | pFold t1 t2, pFold t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				     t2 ?[ eq ] t4)%bool
      | pCombine t1 t2, pCombine t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				   t2 ?[ eq ] t4)%bool
      | _, _ => None
    end.

  Global Instance RelDec_list_func : RelDec (@eq (listOp_func typ)) :=
    {
      rel_dec a b := match listOp_func_eq a b with
    	  	       | Some b => b
    		       | None => false
    		     end
    }.

  Definition lengthR t : typD (tyArr (tyList t) tyNat) :=
    castR id (RFun (list (typD t)) nat) (@length (typD t)).

  Definition NoDupR t : typD (tyArr (tyList t) tyProp) :=
    castR id (RFun (list (typD t)) Prop) (@NoDup (typD t)).

  Definition InR t : typD (tyArr t (tyArr (tyList t) tyProp)) :=
    castR id (RFun (typD t) (RFun (list (typD t)) Prop)) (@In (typD t)).

  Definition mapR t u : typD (tyArr (tyArr t u) (tyArr (tyList t) (tyList u))) :=
    castR id (RFun (RFun (typD t) (typD u)) (RFun (list (typD t)) (list (typD u))))
          (@map (typD t) (typD u)).

  Definition foldR t u : typD (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t))) :=
    castR id (RFun (RFun (typD u) (RFun (typD t) (typD t)))
                  (RFun (typD t) (RFun (list (typD u)) (typD t))))
          (@fold_right (typD t) (typD u)).

  Definition combineR t u : typD (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u)))) :=
    castR id (RFun (list (typD t)) (RFun (list (typD u)) (list ((typD t) * (typD u)))))
          (@combine (typD t) (typD u)).

  Definition listOp_func_symD lf :=
    match lf as lf return match typeof_listOp_func lf return Type@{Urefl} with
			    | Some t => typD t
			    | None => unit
			  end with
      | pLength t => lengthR t
      | pNoDup t => NoDupR t
      | pIn t => InR t
      | pMap t1 t2 => mapR t1 t2
      | pFold t1 t2 => foldR t1 t2
      | pCombine t1 t2 => combineR t1 t2
    end.

  Global Instance RSym_ListOpFunc : SymI.RSym (listOp_func typ) :=
    {
      typeof_sym := typeof_listOp_func;
      symD := listOp_func_symD;
      sym_eqb := listOp_func_eq
    }.

  Global Instance RSymOk_ListOpFunc : SymI.RSymOk RSym_ListOpFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t0); intuition congruence.
    + consider (t ?[ eq ] t0); intuition congruence.
    + consider (t ?[ eq ] t0); intuition congruence.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence.
  Qed.

End ListOpFuncInst.

Section MakeListOp.
  Context {typ func : Set} {FV : PartialView func (listOp_func typ)}.

  Definition fLength t := f_insert (pLength t).
  Definition fNoDup t := f_insert (pNoDup t).
  Definition fIn t := f_insert (pIn t).
  Definition fMap t u := f_insert (pMap t u).
  Definition fFold t u := f_insert (pFold t u).
  Definition fCombine t u := f_insert (pCombine t u).

  Definition mkLength t (lst : expr typ func) : expr typ func :=
    App (Inj (fLength t)) lst.

  Definition mkNoDup t (lst : expr typ func) : expr typ func :=
    App (Inj (fNoDup t)) lst.

  Definition mkIn t (lst : expr typ func) : expr typ func :=
    App (Inj (fIn t)) lst.

  Definition mkMap t u (f lst : expr typ func) : expr typ func :=
    App (App (Inj (fMap t u)) f) lst.

  Definition mkFold t u (f acc lst : expr typ func) : expr typ func :=
    App (App (App (Inj (fFold t u)) f) acc) lst.

  Definition mkCombine t u (xs ys : expr typ func) : expr typ func :=
    App (App (Inj (fCombine t u)) xs) ys.

  Definition fptrnLength {T : Type} (p : Ptrns.ptrn typ T) : ptrn (listOp_func typ) T :=
    fun f U good bad =>
      match f with
        | pLength t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnNoDup {T : Type} (p : Ptrns.ptrn typ T) : ptrn (listOp_func typ) T :=
    fun f U good bad =>
      match f with
        | pNoDup t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnIn {T : Type} (p : Ptrns.ptrn typ T) : ptrn (listOp_func typ) T :=
    fun f U good bad =>
      match f with
        | pIn t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnMap {T : Type} (p : ptrn (typ * typ) T) :
    ptrn (listOp_func typ) T :=
    fun f V good bad =>
      match f with
        | pMap t u => p (t, u) V good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnFold {T : Type} (p : ptrn (typ * typ) T) :
    ptrn (listOp_func typ) T :=
    fun f V good bad =>
      match f with
        | pFold t u => p (t, u) V good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnCombine {T : Type} (p : ptrn (typ * typ) T) :
    ptrn (listOp_func typ) T :=
    fun f V good bad =>
      match f with
        | pCombine t u => p (t, u) V good (fun x => bad f)
        | _ => bad f
      end.

  Global Instance fptrnLength_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnLength p).
  Proof.
    red; intros.
    destruct x; simpl;
    try (right; unfold Fails; reflexivity).
    destruct (Hok t).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnNoDup_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnNoDup p).
  Proof.
    red; intros.
    destruct x; simpl;
    try (right; unfold Fails; reflexivity).
    destruct (Hok t).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnIn_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnIn p).
  Proof.
    red; intros.
    destruct x; simpl;
    try (right; unfold Fails; reflexivity).
    destruct (Hok t).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }repeat rewrite Rcast_val_eq_refl by eauto.
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnMap_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnMap p).
  Proof.
    red; intros; destruct x; try (right; unfold Fails; reflexivity).
    destruct (Hok (t, t0)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnFold_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnFold p).
  Proof.
    red; intros; destruct x; try (right; unfold Fails; reflexivity).
    destruct (Hok (t, t0)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Global Instance fptrnCombine_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnCombine p).
  Proof.
    red; intros; destruct x; try (right; unfold Fails; reflexivity).
    destruct (Hok (t, t0)).
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnLength {T : Type} (f : listOp_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnLength p) res) :
    exists t, Succeeds t p res /\ f = pLength t.
  Proof.
    unfold Succeeds, fptrnLength in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnNoDup {T : Type} (f : listOp_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnNoDup p) res) :
    exists t, Succeeds t p res /\ f = pNoDup t.
  Proof.
    unfold Succeeds, fptrnNoDup in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnIn {T : Type} (f : listOp_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnIn p) res) :
    exists t, Succeeds t p res /\ f = pIn t.
  Proof.
    unfold Succeeds, fptrnIn in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnMap {T : Type} (f : listOp_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnMap p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pMap t u.
  Proof.
    unfold Succeeds, fptrnMap in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnFold {T : Type} (f : listOp_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnFold p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pFold t u.
  Proof.
    unfold Succeeds, fptrnFold in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnCombine {T : Type} (f : listOp_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnCombine p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pCombine t u.
  Proof.
    unfold Succeeds, fptrnCombine in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnLength_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnLength p) res := {
      s_result := exists t, Succeeds t p res /\ f = pLength t;
      s_elim := @Succeeds_fptrnLength T f p res pok
    }.

  Global Instance fptrnNoDup_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnNoDup p) res := {
      s_result := exists t, Succeeds t p res /\ f = pNoDup t;
      s_elim := @Succeeds_fptrnNoDup T f p res pok
    }.

  Global Instance fptrnIn_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnIn p) res := {
      s_result := exists t, Succeeds t p res /\ f = pIn t;
      s_elim := @Succeeds_fptrnIn T f p res pok
    }.

  Global Instance fptrnMap_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnMap p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = pMap t u;
      s_elim := @Succeeds_fptrnMap T f p res pok
    }.

  Global Instance fptrnFold_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnFold p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = pFold t u;
      s_elim := @Succeeds_fptrnFold T f p res pok
    }.

  Global Instance fptrnCombine_SucceedsE {T : Type} {f : listOp_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnCombine p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = pCombine t u;
      s_elim := @Succeeds_fptrnCombine T f p res pok
    }.

End MakeListOp.

Section PtrnListOp.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {FV : PartialView func (listOp_func typ)}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkLength typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnLength {T A : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnLength p))) a.

  Definition ptrnNoDup {T A : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnNoDup p))) a.

  Definition ptrnIn {T A B : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) (b : ptrn (expr typ func) B) :
    ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnIn p))) a) b.

  Definition ptrnMap {T A B : Type}
             (p : ptrn (typ * typ) T) (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnMap p))) a) b.

  Definition ptrnFold {T A B C : Type}
             (p : ptrn (typ * typ) T) (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) (c : ptrn (expr typ func) C) :
    ptrn (expr typ func) (T * A * B * C) :=
    app (app (app (inj (ptrn_view _ (fptrnFold p))) a) b) c.

  Definition ptrnCombine {T A B : Type}
             (p : ptrn (typ * typ) T) (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnCombine p))) a) b.

End PtrnListOp.

Require Import MirrorCore.Reify.ReifyClass.

Section ReifyListOp.

  Polymorphic Context {typ func : Set} {FV : PartialView func (listOp_func typ)}.
  Polymorphic Context {t : Reify typ}.

  Polymorphic Definition reify_length : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RExact (@length)) (RGet 0 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fLength x)).

  Polymorphic Definition reify_NoDup : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RExact (@NoDup)) (RGet 0 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fNoDup x)).

  Polymorphic Definition reify_In : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RExact (@In)) (RGet 0 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fIn x)).

  Polymorphic Definition reify_map : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RExact (@map)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fMap x y)).

  Polymorphic Definition reify_fold : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RExact (@fold_right)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fFold x y)).

  Polymorphic Definition reify_combine : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RExact (@combine)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fCombine x y)).

  Polymorphic Definition reify_listOp : Command (expr typ func) :=
    CFirst (reify_length :: reify_NoDup :: reify_In ::
            reify_map :: reify_fold :: reify_combine :: nil).

End ReifyListOp.

Arguments reify_listOp _ _ {_ _}.
