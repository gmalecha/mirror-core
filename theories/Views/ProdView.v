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
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.TrmD.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.RedAll.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive prod_func {typ : Type} :=
  | pPair : typ -> typ -> prod_func
  | pFst : typ -> typ -> prod_func
  | pSnd : typ -> typ -> prod_func.

Implicit Arguments prod_func [].

Section ProdFuncInst.
  Context {typ func : Type} {HR : RType typ}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {RelDecCorrect_typ : RelDec_Correct RelDec_typ}.
  
  Context {Typ2_tyArr : Typ2 _ Fun}.
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

  Definition prodE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : 
    typD (tyProd t u) = (A * B)%type :=
    eq_ind (typD t) (fun X : Type => typD (tyProd t u) = (X * B)%type)
      (eq_ind (typD u) (fun Y : Type => typD (tyProd t u) = (typD t * Y)%type)
              (typ2_cast t u) B e2) A e1.  
  
  Definition prodD t u (p : typD (tyProd t u)) : typD t * typD u :=
    trmD p (prodE (t := t) (u := u) eq_refl eq_refl).
  
  Definition prodR t u (p : typD t * typD u) : typD (tyProd t u) :=
    trmR p (prodE (t := t) (u := u) eq_refl eq_refl).
  
  Lemma prodDR (t u : typ) A B C D (x : A) (y : B) (e1 : typD t = A) 
        (e2 : typD u = B) (e3 : typD t = C) (e4 : typD u = D) :
    trmD (trmR (x, y) (prodE e1 e2)) (prodE e3 e4) = 
    (trmD (trmR x e1) e3, trmD (trmR y e2) e4).
  Proof.
    unfold trmD, trmR, prodE, eq_ind, eq_rect_r, eq_rect, eq_sym, id.
    clear.
    revert e1 e2 e3 e4.
    generalize (typ2_cast t u).
    unfold tyProd.
    generalize dependent (typ2 t u).
    generalize dependent (typD t).
    generalize dependent (typD u).
    do 3 intros.
    generalize dependent (typD t0).
    intros; repeat subst. reflexivity.
  Qed.

  Definition pairD (t u : typ) : typD (tyArr t (tyArr u (tyProd t u))) :=
    tyArrR2 (fun a b => prodR t u (a, b)).

  Definition fstD (t u : typ) : typD (tyArr (tyProd t u) t) :=
    tyArrR (fun p => fst (prodD t u p)).
  
  Definition sndD (t u : typ) : typD (tyArr (tyProd t u) u) :=
    tyArrR (fun p => snd (prodD t u p)).
  
  Definition prod_func_symD bf :=
    match bf as bf return match typeof_prod_func bf return Type with
			    | Some t => typD t
			    | None => unit
			  end with
      | pPair t u => pairD t u
      | pFst t u => fstD t u
      | pSnd t u => sndD t u
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
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {HF : FuncView func (prod_func typ)}.
  
  Definition fPair t u := f_insert (pPair t u).
  Definition fFst t u := f_insert (pFst t u).
  Definition fSnd t u := f_insert (pSnd t u).

  Definition mkPair (t u : typ) (a b : expr typ func) := App (App (Inj (fPair t u)) a) b.
  Definition mkFst (t u : typ) (p : expr typ func) := App (Inj (fFst t u)) p.
  Definition mkSnd (t u : typ) (p : expr typ func) := App (Inj (fSnd t u)) p.

  Definition fptrnPair : ptrn func unit :=
    fun f _ good bad => 
    match f_view f with
      | Some (pPair _ _) => good tt
      | _ => bad f
    end.

  Definition ptrnPair {A B : Type} 
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun x => match x with | (_, a, b) => (a, b) end) (app (app (inj fptrnPair) a) b).

  Definition fptrnFst : ptrn func unit :=
    fun f _ good bad => 
    match f_view f with
      | Some (pFst _ _) => good tt
      | _ => bad f
    end.

  Definition ptrnFst {A : Type} 
             (p : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj fptrnFst) p).

  Definition fptrnSnd : ptrn func unit :=
    fun f _ good bad => 
    match f_view f with
      | Some (pSnd _ _) => good tt
      | _ => bad f
    end.

  Definition ptrnSnd {A : Type} 
             (p : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj fptrnSnd) p).
  
End MakeProd.

Section Tactics.
  Context {typ func : Type}.
  Context {FV : FuncView func (prod_func typ)}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  
  Definition red_fst_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => fst xy) (ptrnFst (ptrnPair get ignore)).

  Definition pdefault_id {X} (p : ptrn X X) : tptrn X X :=
    fun e => pdefault p e e. 

  Definition red_fst := run_tptrn (pdefault_id red_fst_ptrn).

  Definition red_snd_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => snd xy) (ptrnSnd (ptrnPair ignore get)).

  Definition red_snd := run_tptrn (pdefault_id red_snd_ptrn).

  Definition FST := SIMPLIFY (typ := typ) 
                             (fun _ _ _ _ => 
                                (beta_all (fun _ e args => red_fst (apps e args)))).

  Lemma run_tptrn_id_sound tus tvs t p e val
        (H : ExprDsimul.ExprDenote.exprD' tus tvs t e = Some val)
        (HSucceeds : forall e', Succeeds e p e' ->
                                ExprDsimul.ExprDenote.exprD' tus tvs t e' = Some val) :
    ExprDsimul.ExprDenote.exprD' tus tvs t
                                 (run_tptrn (pdefault_id p) e) = Some val.
  Proof.
    admit.
  Admitted.

  Lemma red_fst_ok : partial_reducer_ok (fun e args => red_fst (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es). clear e es; intros e H.
    unfold red_fst.

    apply run_tptrn_id_sound; [assumption|].
    intros.
    unfold red_fst_ptrn in H0.
    apply Succeeds_pmap in H0.
    destruct H0 as [[x y] [H1 H2]].
    simpl in H2; subst.
    unfold ptrnFst in H1.
    apply Succeeds_pmap in H1. 
    destruct H1 as [[x' [y' z']] [H1 H2]].
    simpl in H2. inversion H2; subst. clear H2.
    apply Succeeds_app in H1.
    destruct H1 as [l [r [Heq [H1 H2]]]]. subst. simpl in H1, H2.
    apply Succeeds_inj in H1.
    destruct H1 as [f [Heq H1]].
    subst.
    unfold ptrnPair in H2.
    apply Succeeds_pmap in H2.
    destruct H2 as [[[x y] z] [H2 H3]].
    inversion H3; subst. clear H3.
    apply Succeeds_app in H2.
    destruct H2 as [l' [r' [Heq [H2 H3]]]].
    subst.
    apply Succeeds_app in H2.
    destruct H2 as [l'' [r'' [Heq [H2 H4]]]].
    simpl in *.
    apply Succeeds_inj in H2.
    subst.
    destruct H2 as [f' [Heq H2]].
    apply Succeeds_get in H4. subst.

    Admitted.

End Tactics.