Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive list_func (typ : Type) :=
  | pNil : typ -> list_func typ
  | pCons : typ -> list_func typ.

Section ListFuncInst.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {func : Type}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ1_tyList : Typ1 _ list}.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyList : typ -> typ := @typ1 _ _ _ _.

  Definition typeof_list_func lf :=
    match lf with
      | pNil t => Some (tyList t)
      | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
    end.

  Definition list_func_eq (a b : list_func typ) : option bool :=
    match a , b with
      | pNil t1, pNil t2 => Some (t1 ?[ eq ] t2)
      | pCons t1, pCons t2 => Some (t1 ?[ eq ] t2)
      | _, _ => None
    end.

  Global Instance RelDec_list_func : RelDec (@eq (list_func typ)) := 
    {
      rel_dec a b := match list_func_eq a b with 
    	  	       | Some b => b 
    		       | None => false 
    		     end
    }.

  Definition nilR t : typD (tyList t) := castR id (list (typD t)) nil.
  Definition consR t : typD (tyArr t (tyArr (tyList t) (tyList t))) :=
    castR id (RFun (typD t) (RFun (list (typD t)) (list (typD t)))) cons.

  Definition list_func_symD lf :=
    match lf as lf return match typeof_list_func lf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pNil t => nilR t
      | pCons t => consR t
    end.

  Global Instance RSym_ListFunc : SymI.RSym (list_func typ) := 
    {
      typeof_sym := typeof_list_func;
      symD := list_func_symD;
      sym_eqb := list_func_eq
    }.

  Global Instance RSymOk_ListFunc : SymI.RSymOk RSym_ListFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t0); intuition congruence.
    + consider (t ?[ eq ] t0); intuition congruence.
  Qed.

End ListFuncInst.

Section MakeList.
  Context {typ func : Type} {FV : FuncView func (list_func typ)}.
  
  Definition fNil t := f_insert (pNil t).
  Definition fCons t := f_insert (pCons t).

  Definition mkNil t : expr typ func := Inj (fNil t).
  Definition mkCons (t : typ) (x xs : expr typ func) := App (App (Inj (fCons t)) x) xs.

  Definition fptrnNil {T : Type} (p : Ptrns.ptrn typ T) : ptrn (list_func typ) T :=
    fun f U good bad =>
      match f with
        | pNil t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnCons {T : Type} (p : Ptrns.ptrn typ T) : ptrn (list_func typ) T :=
    fun f U good bad =>
      match f with
        | pCons t => p t U good (fun x => bad f)
        | _ => bad f
      end.

  Global Instance fptrnNil_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnNil p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok t) |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnCons_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnCons p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok t)].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Lemma Succeeds_fptrnNil {T : Type} (f : list_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnNil p) res) :
    exists t, Succeeds t p res /\ f = pNil t.
  Proof.
    unfold Succeeds, fptrnNil in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnCons {T : Type} (f : list_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnCons p) res) :
    exists t, Succeeds t p res /\ f = pCons t.
  Proof.
    unfold Succeeds, fptrnCons in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.
  
  Global Instance fptrnNil_SucceedsE {T : Type} {f : list_func typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnNil p) res := {
      s_result := exists t, Succeeds t p res /\ f = pNil t;
      s_elim := @Succeeds_fptrnNil T f p res pok
    }.

  Global Instance fptrnCons_SucceedsE {T : Type} {f : list_func typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnCons p) res := {
      s_result := exists t, Succeeds t p res /\ f = pCons t;
      s_elim := @Succeeds_fptrnCons T f p res pok
    }.
  
End MakeList.

Section PtrnList.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func (list_func typ)}.

(* Putting this in the previous sectioun caused universe inconsistencies 
  when calling '@mkNil typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnNil {T : Type}
             (p : ptrn typ T) : ptrn (expr typ func) T :=
    inj (ptrn_view _ (fptrnNil p)).

  Definition ptrnCons {A B T : Type}
             (p : ptrn typ T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnCons p))) a) b.

  Definition list_cases {T : Type}
             (do_nil : typ -> T)
             (do_cons : typ -> expr typ func -> expr typ func -> T)
             (do_default : T)
  : Ptrns.tptrn (expr typ func) T :=
    Ptrns.pdefault
      (Ptrns.por
         (Ptrns.pmap do_nil (ptrnNil Ptrns.get))
         (Ptrns.pmap (fun t_x_xs =>
                        let '(t,x,xs) := t_x_xs in
                        do_cons t x xs) (ptrnCons Ptrns.get Ptrns.get Ptrns.get)))
      do_default.


End PtrnList.