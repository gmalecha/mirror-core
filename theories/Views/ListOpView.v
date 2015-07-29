Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.NatView.
Require Import MirrorCore.Views.ProdView.
Require Import MirrorCore.Views.ListView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive listOp_func (typ : Type) :=
  | pLength : typ -> listOp_func typ
  | pNoDup : typ -> listOp_func typ
  | pIn : typ -> listOp_func typ
  | pMap : typ -> typ -> listOp_func typ
  | pFold : typ -> typ -> listOp_func typ
  | pCombine : typ -> typ -> listOp_func typ.

Section ListOpFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
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
      | pFold t1 t2 => Some (tyArr (tyArr t2 (tyArr t1 t1)) (tyArr t1 (tyArr (tyList t2) t1))) 
      | pCombine t1 t2 => Some (tyArr (tyList t1) (tyArr (tyList t2) (tyList (tyProd t1 t2))))
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
    castR id (Fun (list (typD t)) nat) (@length (typD t)).

  Definition NoDupR t : typD (tyArr (tyList t) tyProp) :=
    castR id (Fun (list (typD t)) Prop) (@NoDup (typD t)).
  
  Definition InR t : typD (tyArr t (tyArr (tyList t) tyProp)) := 
    castR id (Fun (typD t) (Fun (list (typD t)) Prop)) (@In (typD t)).

  Definition mapR t u : typD (tyArr (tyArr t u) (tyArr (tyList t) (tyList u))) :=
    castR id (Fun (Fun (typD t) (typD u)) (Fun (list (typD t)) (list (typD u)))) 
          (@map (typD t) (typD u)).

  Definition foldR t u : typD (tyArr (tyArr u (tyArr t t)) (tyArr t (tyArr (tyList u) t))) :=
    castR id (Fun (Fun (typD u) (Fun (typD t) (typD t))) 
                  (Fun (typD t) (Fun (list (typD u)) (typD t)))) 
          (@fold_right (typD t) (typD u)).

  Definition combineR t u : typD (tyArr (tyList t) (tyArr (tyList u) (tyList (tyProd t u)))) :=
    castR id (Fun (list (typD t)) (Fun (list (typD u)) (list ((typD t) * (typD u))))) 
          (@combine (typD t) (typD u)).

  Definition listOp_func_symD lf :=
    match lf as lf return match typeof_listOp_func lf return Type with
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
  Context {typ func : Type} {FV : FuncView func (listOp_func typ)}.

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
    destruct x; simpl; [destruct (Hok t) | | | | | ].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnNoDup_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnNoDup p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok t) | | | | ].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnIn_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnIn p).
  Proof.
    red; intros.
    destruct x; simpl; [| | destruct (Hok t) | | | ].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
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
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func (listOp_func typ)}.

(* Putting this in the previous sectioun caused universe inconsistencies 
  when calling '@mkLength typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnLength {T A : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnLength p))) a.

  Definition ptrnNoDup {T A : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnNoDup p))) a.

  Definition ptrnIn {T A : Type}
             (p : ptrn typ T) (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnIn p))) a.

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

Section Tactics.
  Context {typ func : Type}.
  Context {FV_listOp : FuncView func (listOp_func typ)}.
  Context {FV_list : FuncView func (list_func typ)}.
  Context {FV_nat : FuncView func natFunc}.
  Context {FV_prod : FuncView func (prod_func typ)}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RTypeOk_typ : @RTypeOk _ RType_typ}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {RelDecEq : RelDec (@eq typ)}.
  Context {RelDecCorrectEq : RelDec_Correct RelDecEq}.
  Context {Typ2_tyArr : Typ2 _ Fun} {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ2_tyProd : Typ2 _ prod} {Typ2Ok_tyProd : Typ2Ok Typ2_tyProd}.
  Context {Typ1_tyList : Typ1 _ list} {Typ1Ok_tyList : Typ1Ok Typ1_tyList}.
  Context {Typ0_tyProp : Typ0 _ Prop} {Typ0Ok_tyProp : Typ0Ok Typ0_tyProp}.
  Context {Typ0_tyNat : Typ0 _ nat} {Typ0Ok_tyNat : Typ0Ok Typ0_tyNat}.
  Context {FVOk_listOp : FuncViewOk (typ := typ) FV_listOp RSym_func RSym_ListOpFunc}.
  Context {FVOk_list : FuncViewOk (typ := typ) FV_list RSym_func RSym_ListFunc}.
  Context {FVOk_nat : FuncViewOk (typ := typ) FV_nat RSym_func RSym_NatFunc}.
  Context {FVOk_prod : FuncViewOk (typ := typ) FV_prod RSym_func RSym_ProdFunc}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.
  Let tyList : typ -> typ := @typ1 _ _ _ Typ1_tyList.
  Let tyProp : typ := @typ0 _ _ _ Typ0_tyProp.
  Let tyNat : typ := @typ0 _ _ _ Typ0_tyNat.

  Fixpoint lst_length (lst : expr typ func) (t : typ) (acc : nat) : expr typ func :=
    run_tptrn 
      (list_cases 
         (fun _ => mkNat acc)
         (fun _ _ lst => (lst_length lst t (S acc)))
         (mkPlus (mkLength t lst) (mkNat acc))) lst.
    
  Lemma lst_length_unfold (lst : expr typ func) (t : typ) (acc : nat) : 
    lst_length lst t acc = 
    run_tptrn 
      (list_cases 
         (fun _ => mkNat acc)
         (fun _ _ lst => (lst_length lst t (S acc)))
         (mkPlus (mkLength t lst) (mkNat acc))) lst.
  Proof.
    destruct lst; simpl; reflexivity.
  Qed.
    
  Definition red_length_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun x => lst_length (snd x) (fst x) 0) (ptrnLength get get).

  Definition red_length := run_tptrn (pdefault_id red_length_ptrn).


(* Coq goes into a loop when parsing this *)
(*
  Fixpoint lst_combine (xs ys : expr typ func) (t u : typ) {struct xs} : expr typ func:=
         match xs with
         | ExprCore.Var _ => mkCombine t u xs ys
         | Inj a =>
             match f_view a with
             | Some (pNil _) => mkNil (tyProd t u)
             | Some (pCons _) => mkCombine t u xs ys
             | None => mkCombine t u xs ys
             end
         | App (ExprCore.Var _) _ => mkCombine t u xs ys
         | App (Inj _) _ => mkCombine t u xs ys
         | App (App (ExprCore.Var _) _) _ => mkCombine t u xs ys
         | App (App (Inj a0) r) b =>
             match f_view a0 with
             | Some (pNil _) => mkCombine t u xs ys
             | Some (pCons _) =>
                 match ys with
                 | ExprCore.Var _ => mkCombine t u xs ys
                 | Inj a1 =>
                     match f_view a1 with
                     | Some (pNil _) => mkNil (tyProd t u)
                     | Some (pCons _) => mkCombine t u xs ys
                     | None => mkCombine t u xs ys
                     end
                 | App (ExprCore.Var _) _ => mkCombine t u xs ys
                 | App (Inj _) _ => mkCombine t u xs ys
                 | App (App (ExprCore.Var _) _) _ => mkCombine t u xs ys
                 | App (App (Inj a2) r0) b0 =>
                     match f_view a2 with
                     | Some (pNil _) => mkCombine t u xs ys
                     | Some (pCons _) =>
                         mkCons (tyProd t u) (mkPair t u r r0)
                           (lst_combine b b0 t u)
                     | None => mkCombine t u xs ys
                     end
                 | App (App (App _ _) _) _ => mkCombine t u xs ys
                 | App (App (Abs _ _) _) _ => mkCombine t u xs ys
                 | App (App (ExprCore.UVar _) _) _ => mkCombine t u xs ys
                 | App (Abs _ _) _ => mkCombine t u xs ys
                 | App (ExprCore.UVar _) _ => mkCombine t u xs ys
                 | Abs _ _ => mkCombine t u xs ys
                 | ExprCore.UVar _ => mkCombine t u xs ys
                 end
             | None => mkCombine t u xs ys
             end
         | App (App (App _ _) _) _ => mkCombine t u xs ys
         | App (App (Abs _ _) _) _ => mkCombine t u xs ys
         | App (App (ExprCore.UVar _) _) _ => mkCombine t u xs ys
         | App (Abs _ _) _ => mkCombine t u xs ys
         | App (ExprCore.UVar _) _ => mkCombine t u xs ys
         | Abs _ _ => mkCombine t u xs ys
         | ExprCore.UVar _ => mkCombine t u xs ys
         end.
    run_tptrn
      (@list_cases typ func FV_list (expr typ func)
         (fun _ => @mkNil typ func FV_list (tyProd t u))
         (fun _ x xs' => 
            run_tptrn 
              (@list_cases typ func FV_list (expr typ func)
                 (fun _ => @mkNil typ func FV_list (tyProd t u))
                 (fun _ y ys' => @mkCons typ func FV_list (tyProd t u) 
                                         (@mkPair typ func FV_prod t u x y) 
                                        (TODO xs' ys' t u)) 
                 (@mkCombine typ func FV_listOp t u xs ys)) ys)
         (@mkCombine typ func FV_listOp t u xs ys)) xs.

Print lst_combine.
Eval unfold lst_combine, list_cases, run_tptrn, pdefault, por, pmap,
  ptrnNil, ptrnCons, app, inj, Mmap, Mrebuild, Mbind, ptrn_view, fptrnCons, fptrnNil, get in lst_combine.
*)

  Fixpoint red_map_ptrn t u (f lst : expr typ func) : expr typ func :=
    run_tptrn (@list_cases typ func _ _
                           (fun _ => mkNil u)
                           (fun _ x xs => mkCons u (beta (App f x)) (red_map_ptrn t u f xs))
                           (mkMap t u f lst)) lst.

  Lemma red_map_unfold (t u : typ) (f lst : expr typ func) : 
    red_map_ptrn t u f lst =
    run_tptrn (@list_cases typ func _ _
                           (fun _ => mkNil u)
                           (fun _ x xs => mkCons u (beta (App f x)) (red_map_ptrn t u f xs))
                           (mkMap t u f lst)) lst.
  Proof.
    destruct lst; simpl; reflexivity.
  Qed.    

  Definition red_map := 
    run_tptrn (pdefault_id (pmap (fun x => match x with
                                             | ((t, u), f, lst) => red_map_ptrn t u f lst
                                           end) (ptrnMap get get get))).


  Fixpoint red_fold_ptrn t u (f acc lst : expr typ func) : expr typ func :=
    run_tptrn (@list_cases typ func _ _
                           (fun _ => acc)
                           (fun _ x xs => 
                              beta (beta (App (App f x) (red_fold_ptrn t u f acc xs))))
                           (mkFold t u f acc lst)) lst.

  Lemma red_fold_unfold (t u : typ) (f acc lst : expr typ func) : 
    red_fold_ptrn t u f acc lst =
    run_tptrn (@list_cases typ func _ _
                           (fun _ => acc)
                           (fun _ x xs => 
                              beta (beta (App (App f x) (red_fold_ptrn t u f acc xs))))
                           (mkFold t u f acc lst)) lst.

  Proof.
    destruct lst; simpl; reflexivity.
  Qed.    

  Definition red_fold := 
    run_tptrn (pdefault_id (pmap (fun x => match x with
                                             | ((t, u), f, acc, lst) => 
                                               red_fold_ptrn t u f acc lst
                                           end) (ptrnFold get get get get))).




  Lemma lst_length_sound tus tvs (t : typ) (lst : expr typ func) 
        (x : exprT tus tvs (typD (tyList t))) (n : nat)
        (H : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) lst = Some x) :
    ExprDsimul.ExprDenote.exprD' tus tvs tyNat (lst_length lst t n) = 
    Some (castR (exprT tus tvs) nat 
                (fun us vs => length (castD (exprT tus tvs)
                                            (list (typD t)) x us vs) + n)).
  Proof.
    revert H. generalize dependent n. generalize dependent x.
    apply expr_strong_ind_no_case with (e := lst); intros.
    rewrite lst_length_unfold.
    unfold run_tptrn, list_cases.
    apply pdefault_sound; [apply _ | | intros; ptrnE; destruct H1; ptrnE |].
    { intros a b Hab c d Hcd; subst; erewrite Hcd; reflexivity. }
    { unfold nilR, mkNat, fNat, ptret. solve_denotation. 
      unfold natR. solve_denotation. reflexivity. }
    { unfold ptret, consR. solve_denotation; simpl.
      erewrite H; [| eauto with acc_db | eassumption].
      Require Import Omega FunctionalExtensionality.
      repeat f_equal.
      do 2 (apply functional_extensionality; intros).
      omega. }
    { unfold ptret, mkPlus, mkLength, fPlus, mkNat, fNat, fLength.
      solve_denotation.
      unfold plusR, natR, lengthR.
      solve_denotation.
      reflexivity.
    }
  Qed.
    
  Lemma red_length_ok : partial_reducer_ok (fun e args => red_length (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_length.
  
    apply run_tptrn_id_sound; [assumption|]; intros.
    unfold red_length_ptrn in H0.
    solve_denotation.
    unfold lengthR.
    solve_denotation. simpl.
    rewrite lst_length_sound with (x := x1); [|assumption].
    repeat f_equal. do 2 (apply functional_extensionality; intros). omega.
  Qed.

  Lemma map_ptrn_ok tus tvs (t u : typ) (f lst : expr typ func) 
        (df : exprT tus tvs (typD (tyArr t u)))
        (dlst : exprT tus tvs (typD (tyList t)))
        (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (tyArr t u) f = Some df) 
        (Hlst : ExprDsimul.ExprDenote.exprD' tus tvs (tyList t) lst = Some dlst) :
    ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) (red_map_ptrn t u f lst) = 
    Some (castR (exprT tus tvs) (list (typD u))
                (fun vs us =>
                   map (castD (exprT tus tvs) (Fun (typD t) (typD u)) df vs us)
                       (castD (exprT tus tvs) (list (typD t)) dlst vs us))).
  Proof.
    Opaque beta.
    revert Hlst. generalize dependent dlst.
    apply expr_strong_ind_no_case with (e := lst); intros.
    rewrite red_map_unfold.
    unfold run_tptrn, list_cases.
    apply pdefault_sound; [apply _ | | intros; ptrnE; destruct H0 |].
    { intros a b Hab c d Hcd; subst; erewrite Hcd; reflexivity. }
    { intros; unfold ptret; simpl; solve_denotation.
      unfold mkNil, fNil; solve_denotation.
       unfold nilR. solve_denotation. reflexivity. }
    { unfold ptret. solve_denotation.
      unfold mkCons, fCons; solve_denotation; simpl.
      erewrite H; [| eauto with acc_db | eassumption].
      reflexivity.
      unfold consR. solve_denotation. reflexivity. }
    { unfold ptret, mkMap, fMap.
      solve_denotation.
      unfold mapR. solve_denotation.
      reflexivity.
    }
  Qed.

  Lemma map_red_ok : partial_reducer_ok (fun e args => red_map (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_map.
    apply run_tptrn_id_sound; [assumption|]; intros.
    solve_denotation.
    unfold mapR.
    solve_denotation.
    erewrite map_ptrn_ok; [reflexivity | eassumption | eassumption].
  Qed.

  Lemma fold_ptrn_ok tus tvs (t u : typ) (f acc lst : expr typ func) 
        (df : exprT tus tvs (typD (tyArr u (tyArr t t))))
        (dacc : exprT tus tvs (typD t))
        (dlst : exprT tus tvs (typD (tyList u)))
        (Hf : ExprDsimul.ExprDenote.exprD' tus tvs (tyArr u (tyArr t t)) f = Some df) 
        (HAcc : ExprDsimul.ExprDenote.exprD' tus tvs t acc = Some dacc) 
        (Hlst : ExprDsimul.ExprDenote.exprD' tus tvs (tyList u) lst = Some dlst) :
    ExprDsimul.ExprDenote.exprD' tus tvs t (red_fold_ptrn t u f acc lst) = 
    Some (castR (exprT tus tvs) (typD t)
                (fun vs us =>
                   fold_right (castD (exprT tus tvs) (Fun (typD u) (Fun (typD t) (typD t))) df vs us)
                              (castD (exprT tus tvs) (typD t) dacc vs us)
                              (castD (exprT tus tvs) (list (typD u)) dlst vs us))).
  Proof.
    Opaque beta.
    revert Hlst. generalize dependent dlst. 
    apply expr_strong_ind_no_case with (e := lst); intros.
    rewrite red_fold_unfold.
    unfold run_tptrn, list_cases.
    apply pdefault_sound; [apply _ | | intros; ptrnE; destruct H0 |].
    { intros a b Hab c d Hcd; subst; erewrite Hcd; reflexivity. }
    { intros; unfold ptret; simpl; solve_denotation.
      unfold nilR. solve_denotation. simpl.
      solve_denotation. }

    { unfold ptret. solve_denotation.
      eapply H; [eauto with acc_db | eassumption].
      unfold consR. solve_denotation. 
      solve_denotation.
      reflexivity. }
    { unfold ptret, mkFold, fFold.
      solve_denotation.
      unfold foldR.
      solve_denotation.
      reflexivity.
    }
  Qed.

  Lemma fold_red_ok : partial_reducer_ok (fun e args => red_fold (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_fold.
    apply run_tptrn_id_sound; [assumption|]; intros.
    solve_denotation.
    unfold foldR.
    solve_denotation.
    erewrite fold_ptrn_ok; [reflexivity | eassumption | eassumption | eassumption].
  Qed.

End Tactics.