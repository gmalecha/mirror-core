Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import ExtLib.Relations.TransitiveClosure.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Lambda.ExprTac.

Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.RedAll.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Inductive prod_func {typ : Set} : Set :=
| pPair : typ -> typ -> prod_func
| pFst : typ -> typ -> prod_func
| pSnd : typ -> typ -> prod_func.

Arguments prod_func _ : clear implicits.

Section ProdFuncInst.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RelDecCorrect_typ : RelDec_Correct RelDec_typ}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2_tyProd : Typ2 _ prod}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyProd.

  Definition typeof_prod_func pf :=
    match pf with
      | pPair t1 t2 => Some (tyArr t1 (tyArr t2 (tyProd t1 t2)))
      | pFst t1 t2 => Some (tyArr (tyProd t1 t2) t1)
      | pSnd t1 t2 => Some (tyArr (tyProd t1 t2) t2)
    end.

  Definition prod_func_eq (a b : prod_func typ) : option bool :=
    match a , b with
      | pPair t1 t2, pPair t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				     t2 ?[ eq ] t4)%bool
      | pFst t1 t2, pFst t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				     t2 ?[ eq ] t4)%bool
      | pSnd t1 t2, pSnd t3 t4 => Some (t1 ?[ eq ] t3 &&
	      				     t2 ?[ eq ] t4)%bool
      | _, _ => None
    end.

  Definition pairR t u : typD (tyArr t (tyArr u (tyProd t u))) :=
    castR id (RFun (typD t) (RFun (typD u) (typD t * typD u))) pair.

  Definition fstR t u : typD (tyArr (tyProd t u) t) :=
    castR id (RFun (typD t * typD u) (typD t)) fst.

  Definition sndR t u : typD (tyArr (tyProd t u) u) :=
    castR id (RFun (typD t * typD u) (typD u)) snd.

  Definition prod_func_symD bf :=
    match bf as bf return match typeof_prod_func bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pPair t u => pairR t u
      | pFst t u => fstR t u
      | pSnd t u => sndR t u
    end.

  Global Instance RSym_ProdFunc
  : SymI.RSym (prod_func typ) :=
    {
      typeof_sym := typeof_prod_func;
      symD := prod_func_symD ;
      sym_eqb := prod_func_eq
    }.

  Global Instance RSymOk_ProdFunc : SymI.RSymOk RSym_ProdFunc.
  Proof.
    split; intros.
    destruct a, b; simpl; try apply I.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool;
      intuition congruence.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool;
      intuition congruence.
    + consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool;
      intuition congruence.
  Qed.

End ProdFuncInst.

Section MakeProd.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {HF : PartialView func (prod_func typ)}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2_tyProd : Typ2 _ prod}.

  Definition fPair t u := f_insert (pPair t u).
  Definition fFst t u := f_insert (pFst t u).
  Definition fSnd t u := f_insert (pSnd t u).

  Definition mkPair (t u : typ) (a b : expr typ func) := App (App (Inj (fPair t u)) a) b.
  Definition mkFst (t u : typ) (p : expr typ func) := App (Inj (fFst t u)) p.
  Definition mkSnd (t u : typ) (p : expr typ func) := App (Inj (fSnd t u)) p.

  Definition fptrnPair {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (prod_func typ) T :=
    fun f U good bad =>
      match f with
        | pPair t u => p (t, u) U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnFst {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (prod_func typ) T :=
    fun f U good bad =>
      match f with
        | pFst t u => p (t, u) U good (fun x => bad f)
        | _ => bad f
      end.

  Definition fptrnSnd {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (prod_func typ) T :=
    fun f U good bad =>
      match f with
        | pSnd t u => p (t, u) U good (fun x => bad f)
        | _ => bad f
      end.

  Global Instance fptrnPair_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnPair p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok (t, t0))| |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnFst_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnFst p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok (t, t0)) |].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnSnd_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnSnd p).
  Proof.
    red; intros.
    destruct x; simpl; [| |destruct (Hok (t, t0))].
    { right; unfold Fails; reflexivity. }
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Definition ptrnPair@{V R L} {A B T : Type@{V}}
             (p : ptrn@{Set V R L} (typ * typ) T)
             (a : ptrn@{Set V R L} (expr typ func) A)
             (b : ptrn@{Set V R L} (expr typ func) B)
  : ptrn@{Set V R L} (expr typ func) (T * A * B) :=
    app@{V R L} (app@{V R L} (inj@{V R L} (ptrn_view HF (fptrnPair p))) a) b.
  Global Instance ptrnPair_ok : ltac:(PtrnOk (@ptrnPair)) :=
    ltac:(unfold ptrnPair ; refine _).

  Definition ptrnFst {A T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnFst p))) a.
  Global Instance ptrnFst_ok : ltac:(PtrnOk (@ptrnFst)) :=
    ltac:(unfold ptrnFst ; refine _).

  Definition ptrnSnd {A T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A) :=
    app (inj (ptrn_view _ (fptrnSnd p))) a.
  Global Instance ptrnSnd_ok : ltac:(PtrnOk (@ptrnSnd)) :=
    ltac:(unfold ptrnSnd ; refine _).

  Lemma Succeeds_fptrnPair {T : Type} (f : prod_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnPair p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pPair t u.
  Proof.
    unfold Succeeds, fptrnPair in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnFst {T : Type} (f : prod_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnFst p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pFst t u.
  Proof.
    unfold Succeeds, fptrnFst in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnSnd {T : Type} (f : prod_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnSnd p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pSnd t u.
  Proof.
    unfold Succeeds, fptrnSnd in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.

  Global Instance fptrnPair_SucceedsE {T : Type} {f : prod_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnPair p) res :=
  { s_result := exists t u, Succeeds (t, u) p res /\ f = pPair t u
  ; s_elim := @Succeeds_fptrnPair T f p res  pok
  }.

  Global Instance fptrnFst_SucceedsE {T : Type} {f : prod_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnFst p) res :=
  { s_result := exists t u, Succeeds (t, u) p res /\ f = pFst t u
  ; s_elim := @Succeeds_fptrnFst T f p res pok
  }.

  Global Instance fptrnSnd_SucceedsE {T : Type} {f : prod_func typ}
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p}
  : SucceedsE f (fptrnSnd p) res :=
  { s_result := exists t u, Succeeds (t, u) p res /\ f = pSnd t u
  ; s_elim := @Succeeds_fptrnSnd T f p res  pok
  }.

End MakeProd.

Section Tactics.
  Context {typ func : Set}.
  Context {FV : PartialView func (prod_func typ)}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RTypeOk_typ : @RTypeOk _ RType_typ}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ RFun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ2Ok_tyProd : Typ2Ok Typ2_tyProd}.
  Context {RelDecEq : RelDec (@eq typ)}.
  Context {RelDecCorrectEq : RelDec_Correct RelDecEq}.
  Context {FVOk : FuncViewOk (typ := typ) FV RSym_func RSym_ProdFunc}.

  Let tyArr := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd := @typ2 _ _ _ Typ2_tyProd.

  Definition red_fst_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => snd (fst (snd xy))) (ptrnFst ignore (ptrnPair ignore get ignore)).

  Local Ltac solve_ok :=
    repeat first [ simple eapply ptrn_ok_pmap
                 | simple eapply ptrn_ok_app
                 | simple eapply ptrn_ok_inj
                 | simple eapply ptrn_view_ok
                 | simple eapply ptrn_ok_ignore
                 | simple eapply ptrn_ok_get
                 | simple eapply fptrnFst_ok
                 | simple eapply fptrnSnd_ok
                 | simple eapply fptrnPair_ok ].

  Opaque por.

  Local Instance ptrn_ok_red_fst_ptrn : ptrn_ok red_fst_ptrn.
  Proof.
    unfold red_fst_ptrn, ptrnFst, ptrnPair.
    solve_ok.
  Defined.

  Definition red_fst : expr typ func -> expr typ func :=
    run_ptrn_id red_fst_ptrn.

  Definition red_snd_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => snd (snd xy)) (ptrnSnd ignore (ptrnPair ignore ignore get)).

  Local Instance ptrn_ok_red_snd_ptrn : ltac:(PtrnOk red_snd_ptrn) := _.

  Definition red_snd : expr typ func -> expr typ func :=
    run_ptrn_id red_snd_ptrn.

(*
  Definition FST :=
    SIMPLIFY (typ := typ)
             (fun _ _ _ _ =>
                (beta_all (fun _ e args => red_fst (apps e args)))).
*)

  Lemma red_fst_ok : partial_reducer_ok (fun e args => red_fst (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_fst.
    eapply run_ptrn_id_sound; eauto with typeclass_instances.
    unfold red_fst_ptrn.
    intros.
    repeat ptrnE; subst.

    (*  *)
    (* Require Import ExtLib.Tactics. *)
(*    inv_all; subst. *)

    lambda_exprD_fwd.
    subst.
    repeat rewrite Rcast_val_eq_refl by eauto.

    rewrite H3. f_equal.
    unfold fstR, pairR.

    simpl_exprT.
    simpl.
    simpl_exprT. reflexivity.
  Defined.

  Lemma red_snd_ok : partial_reducer_ok (fun e args => red_snd (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_snd.
    eapply run_ptrn_id_sound; eauto with typeclass_instances.
    unfold red_snd_ptrn.
    intros.
    repeat ptrnE. subst.
    lambda_exprD_fwd. rewrite H1.
    f_equal.
    subst.
    repeat rewrite Rcast_val_eq_refl by eauto.
    simpl. unfold sndR, pairR. simpl.
    simpl_exprT.
    simpl.
    simpl_exprT. reflexivity.
  Qed.

End Tactics.

Require Import MirrorCore.Reify.ReifyClass.

Section ReifyProd.
  Context {typ func : Set} {FV : PartialView func (prod_func typ)}.
  Context {t : Reify typ}.

  Definition reify_pair@{X} : Command (expr typ func) :=
    CPattern (ls := @cons Type@{X} typ (@cons Type@{X} typ nil))
             (RApp (RApp (@RExact (forall a b : Set, a -> b -> a * b)(@pair))
                         (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fPair x y)).

  Definition reify_fst@{X} : Command (expr typ func) :=
    CPattern (ls := @cons Type@{X} typ (@cons Type@{X} typ nil))
             (RApp (RApp (@RExact (forall a b : Set, a * b -> a) (@fst))
                         (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fFst x y)).

  Definition reify_snd@{X} : Command (expr typ func) :=
    CPattern (ls := @cons Type@{X} typ (@cons Type@{X} typ nil))
             (RApp (RApp (@RExact (forall a b : Set, a * b -> b) (@snd))
                         (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fSnd x y)).

  Definition reify_prod : Command (expr typ func) :=
    CFirst (reify_pair :: reify_fst :: reify_snd :: nil).
End ReifyProd.

Arguments reify_prod _ _ {_ _}.
