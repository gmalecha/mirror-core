Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.

Section TrmDR.
  Context {typ : Type} {RType_typ : RType typ}.
  
  Definition trmD {A B : Type} (p : A) (e : A = B) : B :=
    eq_rect _ id p _ e.
    
  Definition trmR {A B : Type} (p : B) (e : A = B) : A :=
    eq_rect_r id p e.
     
  Lemma trmD_eq_refl A (x : A) :
    trmD x eq_refl = x.
  Proof.
    reflexivity.
  Qed.
  
  Lemma trmR_eq_refl A (x : A) :
    trmR x eq_refl = x.
  Proof.
    reflexivity.
  Qed.

  Lemma trmD_inj {A B : Type} (a b : A) (e : A = B)
    (H : trmD a e = trmD b e) : a = b.
  Proof.
    unfold trmD, eq_rect, id in H.
    destruct e; apply H.
  Qed.
  
  Lemma trmR_inj {A B : Type} (a b : B) (e : A = B)
    (H : trmR a e = trmR b e) : a = b.
  Proof.
    unfold trmR, eq_rect_r, eq_rect, eq_sym, id in H.
    destruct e; apply H.
  Qed.
  
  Lemma trmDR {A B : Type} (p : B) (e : A = B) : trmD (trmR p e) e = p.
  Proof.
    subst. reflexivity.
  Qed.
    
  Lemma trmRD {A B : Type} (p : A) (e : A = B) : trmR (trmD p e) e = p.
  Proof.
    subst. reflexivity.
  Qed.
(*
 Lemma trmDR2 f g (h : forall {A : Type} {t : typ}, (typD t = A) -> typD (f t) = g A) 
    t A B (x : forall A, g A) (e1 : typD t = A) (e2 : typD t = B) : trmD (trmR (x A) (h e1)) (h e2) = x B.
  Proof.
    unfold trmD, trmR, eq_rect_r, eq_rect, id, eq_sym.
    generalize dependent (h B t e2).
    generalize dependent (h A t e1); intros; subst.
	generalize dependent (typD (f t)).
	generalize dependent (typD t). intro.
	generalize dependent (x T).
	generalize dependent (g T).
	clear.
	intros; subst.
	subst.
	assert (e = eq_refl) by admit.
	subst. reflexivity.
  Qed.
  *)  
End TrmDR.

Section Denotation.
  Context {typ : Type} {RType_typ : RType typ}.
  Context {Typ2_tyArr : Typ2 _ Fun}.

  Let tyArr := @typ2 _ _ _ _.

  Definition funE {A B : Type} {t u : typ} (e1 : typD t = A) (e2 : typD u = B) : typD (tyArr t u) = (A -> B) :=
    eq_ind (typD t) (fun X : Type => typD (tyArr t u) = (X -> B))
      (eq_ind (typD u) (fun Y : Type => typD (tyArr t u) = (typD t -> Y))
         (typ2_cast t u) B e2) A e1.
         
  Definition tyArrD' {a b : typ} {A B : Type} (f : typD (tyArr a b)) (e1 : typD a = A) (e2 : typD b = B) : A -> B :=
    trmD f (funE e1 e2).

  Program Definition tyArrD2' {a b c : typ} {A B C : Type} (f : typD (tyArr a (tyArr b c))) 
    (e1 : typD a = A) (e2 : typD b = B) (e3 : typD c = C) : 
    A -> B -> C := fun x => tyArrD' ((tyArrD' f e1 eq_refl) x) e2 e3.

  Program Definition tyArrD3' {a b c d : typ} {A B C D : Type} (f : typD (tyArr a (tyArr b (tyArr c d)))) 
    e1 e2 e3 e4 : A -> B -> C -> D :=
      fun x y => tyArrD' ((tyArrD2' f e1 e2 eq_refl) x y) e3 e4.

  Program Definition tyArrD4' {a b c d e : typ} {A B C D E : Type} (f : typD (tyArr a (tyArr b (tyArr c (tyArr d e))))) 
    e1 e2 e3 e4 e5 : A -> B -> C -> D -> E := 
      fun x y z => tyArrD' ((tyArrD3' f e1 e2 e3 eq_refl) x y z) e4 e5.

  Definition tyArrD {a b : typ} (f : typD (tyArr a b)) : typD a -> typD b :=
    tyArrD' f eq_refl eq_refl.

  Program Definition tyArrD2 {a b c : typ} (f : typD (tyArr a (tyArr b c)))  : 
    typD a -> typD b -> typD c := tyArrD2' f eq_refl eq_refl eq_refl.
    
  Program Definition tyArrD3 {a b c d : typ} (f : typD (tyArr a (tyArr b (tyArr c d)))) 
    : typD a -> typD b -> typD c -> typD d := tyArrD3' f eq_refl eq_refl eq_refl eq_refl.

  Program Definition tyArrD4 {a b c d e : typ} (f : typD (tyArr a (tyArr b (tyArr c (tyArr d e))))) 
    : typD a -> typD b -> typD c -> typD d -> typD e := 
	  tyArrD4' f eq_refl eq_refl eq_refl eq_refl eq_refl.
	  
  Definition tyArrR' {a b : typ} {A B : Type} (f : A -> B) e1 e2 : typD (tyArr a b) :=
    trmR f (funE e1 e2).  

  Definition tyArrR2' {a b c : typ} {A B C : Type} (f : A -> B -> C) (e1 : typD a = A) (e2 : typD b = B) (e3 : typD c = C) : 
    typD (tyArr a (tyArr b c)) := tyArrR' (fun x => (tyArrR' (f x) e2 e3)) e1 eq_refl.

  Definition tyArrR3' {a b c d : typ} {A B C D : Type} (f : A -> B -> C -> D) e1 e2 e3 e4 : 
    typD (tyArr a (tyArr b (tyArr c d))) := 
    tyArrR' (fun x => tyArrR2' (f x) e2 e3 e4) e1 eq_refl.

  Definition tyArrR4' {a b c d e : typ} {A B C D E : Type} (f : A -> B -> C -> D -> E) 
    e1 e2 e3 e4 e5 : typD (tyArr a (tyArr b (tyArr c (tyArr d e)))) :=
    tyArrR' (fun x => tyArrR3' (f x) e2 e3 e4 e5) e1 eq_refl.

  Definition tyArrR {a b : typ} (f : typD a -> typD b) : typD (tyArr a b) :=
    tyArrR' f eq_refl eq_refl.
    
  Definition tyArrR2 {a b c : typ} (f : typD a -> typD b -> typD c) : 
    typD (tyArr a (tyArr b c)) :=
    tyArrR2' f eq_refl eq_refl eq_refl.

  Definition tyArrR3 {a b c d : typ} (f : typD a -> typD b -> typD c -> typD d) : 
    typD (tyArr a (tyArr b (tyArr c d))) :=
    tyArrR3' f eq_refl eq_refl eq_refl eq_refl.

  Definition tyArrR4 {a b c d e : typ} (f : typD a -> typD b -> typD c -> typD d -> typD e) 
    : typD (tyArr a (tyArr b (tyArr c (tyArr d e)))) :=
    tyArrR4' f eq_refl eq_refl eq_refl eq_refl eq_refl.
    
    
  Lemma tyArrDR {a b : typ} (f : typD a -> typD b) : tyArrD (tyArrR f) = f.
  Proof.
    unfold tyArrD, tyArrD', tyArrR, tyArrR'; rewrite trmDR. reflexivity.
  Qed.

  Lemma tyArrRD {a b : typ} (f : typD (tyArr a b)) : tyArrR (tyArrD f) = f.
  Proof.
    unfold tyArrD, tyArrD', tyArrR, tyArrR'; rewrite trmRD. reflexivity.
  Qed.

  Lemma exprT_App_tyArrD tus tvs (t u : typ) (f : exprT tus tvs (typD (tyArr t u))) (a : exprT tus tvs (typD t)) :
    exprT_App f a = fun us vs => (tyArrD (f us vs)) (a us vs).
  Proof.
    unfold tyArrD, tyArrD', trmD, funE, exprT_App, eq_rect_r, eq_sym, eq_rect.
    unfold tyArr in *.
    generalize (typ2_cast t u).
    generalize dependent (typ2 t u).
    intros.
    generalize dependent (typD t0).
    intros. subst. reflexivity.
  Qed.

  Lemma trmD_App t u A B (f : typD (tyArr t u)) (e1 : typD t = A) (e2 : typD u = B) :
    (fun x : typD t => trmD f (funE e1 e2) (trmD x e1)) =
    trmD f (funE eq_refl e2).
  Proof.
	unfold trmD, eq_rect, id, eq_ind; simpl.
	unfold funE.
	unfold eq_ind, eq_rect.
	generalize (typ2_cast t u).
	clear.
	revert f e1 e2. unfold tyArr.
	generalize dependent (typD (typ2 t u)).
	generalize dependent (typD t).
	generalize dependent (typD u).
	intros; subst. reflexivity.
  Qed.
(*
  Lemma trmR_App t u A B (f : typD (tyArr t u)) (e1 : typD t = A) (e2 : typD u = B) :
    (fun x : A => trmD f (funE e1 e2) (trmR x e1)) =
    trmR f (funE eq_refl e2).
  Proof.
	unfold trmD, eq_rect, id, eq_ind; simpl.
	unfold funE.
	unfold eq_ind, eq_rect.
	generalize (typ2_cast t u).
	clear.
	revert f e1 e2. unfold tyArr.
	generalize dependent (typD (typ2 t u)).
	generalize dependent (typD t).
	generalize dependent (typD u).
	intros; subst. reflexivity.
  Qed.
*)

End Denotation.
