Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.
Require Import ExtLib.Relations.TransitiveClosure.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.RedAll.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Section TypeOfSymAs.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RSym_func : RSym func}.
  
  Lemma typeof_sym_symAs (s : func) t v (H : symAs s t = Some v) : typeof_sym s = Some t.
  Proof.
    unfold symAs in H. 
    generalize dependent (symD s).
    forward.
  Qed.

End TypeOfSymAs.

Inductive prod_func {typ : Type} :=
  | pPair : typ -> typ -> prod_func
  | pFst : typ -> typ -> prod_func
  | pSnd : typ -> typ -> prod_func.

Implicit Arguments prod_func [].

Section ProdFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
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

  Definition castD F U {T : Typ0 _ U} (val : F (typD (typ0 (F:=U)))) : F U :=
    match @typ0_cast typ _ _ T in _ = x return F x with
      | eq_refl => val
    end.

  Definition castR F U {T : Typ0 _ U} (val : F U) : F (typD (typ0 (F:=U))) :=
    match eq_sym (@typ0_cast typ _ _ T) in _ = x return F x with
    | eq_refl => val
    end.

  Existing Instance Typ2_App.
  Existing Instance Typ1_App.
  Existing Instance Typ0_term.

  Implicit Arguments castD [[T]].
  Implicit Arguments castR [[T]].

  Definition pairD t u : typD (tyArr t (tyArr u (tyProd t u))) -> 
                         Fun (typD t) (Fun (typD u) (typD t * typD u)) :=
    castD id (Fun (typD t) (Fun (typD u) (typD t * typD u)%type)).

  Definition pairR t u : typD (tyArr t (tyArr u (tyProd t u))) :=
    castR id (Fun (typD t) (Fun (typD u) (typD t * typD u))) pair.

  Definition fstD t u : typD (tyArr (tyProd t u) t) -> Fun (typD t * typD u) (typD t) :=
    castD id (Fun (typD t * typD u) (typD t)).

  Definition fstR t u : typD (tyArr (tyProd t u) t) :=
    castR id (Fun (typD t * typD u) (typD t)) fst.

  Definition sndD t u : typD (tyArr (tyProd t u) u) -> Fun (typD t * typD u) (typD u) :=
    castD id (Fun (typD t * typD u) (typD u)).
  
  Definition sndR t u : typD (tyArr (tyProd t u) u) :=
    castR id (Fun (typD t * typD u) (typD u)) snd.
  
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

Implicit Arguments castD [[RType_typ] [T]].
Implicit Arguments castR [[RType_typ] [T]].

Section MakeProd.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {HF : FuncView func (prod_func typ)}.
  Context {RelDec_typ : RelDec (@eq typ)}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
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

  Definition ptrnPair {A B T : Type} 
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (A * B) :=
    pmap (fun x => match x with | (_, a, b) => (a, b) end) 
         (app (app (inj (ptrn_view _ (fptrnPair p))) a) b).

  Definition ptrnFst {A T : Type} 
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj (ptrn_view _ (fptrnFst p))) a).

  Definition ptrnSnd {A T : Type} 
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) : ptrn (expr typ func) A :=
    pmap snd (app (inj (ptrn_view _ (fptrnSnd p))) a).
  
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
  
End MakeProd.

Section Tactics.
  Context {typ func : Type}.
  Context {FV : FuncView func (prod_func typ)}.
  Context {RType_typ : RType typ} {RSym_func : RSym func}.
  Context {RTypeOk_typ : @RTypeOk _ RType_typ}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ2_tyProd : Typ2 _ prod}.
  Context {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.
  Context {Typ2Ok_tyProd : Typ2Ok Typ2_tyProd}.
  Context {RelDecEq : RelDec (@eq typ)}.
  Context {RelDecCorrectEq : RelDec_Correct RelDecEq}.
  Context {FVOk : FuncViewOk (typ := typ) FV RSym_func RSym_ProdFunc}.

  Let tyArr := @typ2 _ _ _ Typ2_tyArr.
  Let tyProd := @typ2 _ _ _ Typ2_tyProd.
  
  Definition red_fst_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => fst xy) (ptrnFst ignore (ptrnPair ignore get ignore)).

  Definition red_fst := run_tptrn (pdefault_id red_fst_ptrn).

  Definition red_snd_ptrn : ptrn (expr typ func) (expr typ func) :=
    pmap (fun xy => snd xy) (ptrnSnd ignore (ptrnPair ignore ignore get)).

  Definition red_snd := run_tptrn (pdefault_id red_snd_ptrn).

  Definition FST := SIMPLIFY (typ := typ) 
                             (fun _ _ _ _ => 
                                (beta_all (fun _ e args => red_fst (apps e args)))).

  Ltac destruct_prod :=
    match goal with 
      | p : ?A * ?B |- _ => destruct p; destruct_prod
      | _ => idtac
    end.

  Existing Instance Typ2_App.
  Existing Instance Typ1_App.
  Existing Instance Typ0_term.
  Existing Instance MirrorCore.ExprI.Applicative_exprT.

Require Import MirrorCore.Util.Compat.

Theorem exprT_App_Fun tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)
        (e1 : exprT tus tvs (Fun T U))
        (e2 : exprT tus tvs T) :
@exprT_App typ _ Typ2_tyArr tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _) (@castR typ _ (exprT tus tvs) _ _ e1)
                 (@castR typ _ (exprT tus tvs) _ _ e2) =
      @castR typ _ (exprT tus tvs) U U0 (Applicative.ap e1 e2).
  Proof.
    unfold exprT_App. simpl. intros.
    unfold castR. simpl.
    generalize dependent (typ2_cast (typ0 (F:=T)) (typ0 (F:=U))).
    generalize dependent (typ0_cast (F:=T)).
    generalize dependent (typ0_cast (F:=U)).
    intros.
    autorewrite_with_eq_rw.
    generalize dependent (typD (typ2 (typ0 (F:=T)) (typ0 (F:=U)))).
    intros. subst T1.
    admit.
(*
    destruct (eq_sym e0).
    destruct (eq_sym e). simpl. reflexivity.*)
  Admitted.

Theorem exprT_App_Fun' tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)  P
        (e1 : exprT tus tvs (Fun T U))
        (e2 : exprT tus tvs T) 
        (Hres : P (@castR typ _ (exprT tus tvs) U U0 (Applicative.ap e1 e2))) :
  P (@exprT_App typ _ Typ2_tyArr tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _) (@castR typ _ (exprT tus tvs) _ _ e1) (@castR typ _ (exprT tus tvs) _ _ e2)).
  Proof.
    subst. rewrite exprT_App_Fun. assumption.
  Qed.

  Lemma exprT_App_castR_pure {A : Type} {T0 : Typ0 RType_typ A} tus tvs (f : exprT tus tvs A) :
    (fun us vs => castR typ id A (f us vs)) = 
    (castR typ (exprT tus tvs) A f).
  Proof.
    unfold castR, eq_sym; simpl.
    Require Import FunctionalExtensionality.
    do 2 (apply functional_extensionality; intros).
    admit.
  Admitted.


    Ltac force_apply lem :=
      let L := fresh "L" in 
      pose proof lem as L; apply L; clear L.

Ltac ptrn_prod_sound_step :=
  match goal with
    | H : Succeeds _ (fptrnPair _) _ |- _ => 
      apply Succeeds_fptrnPair in H; destruct H as [? [? ?]]; repeat subst
    | H : Succeeds _ (fptrnFst _) _ |- _ => 
      apply Succeeds_fptrnFst in H; destruct H as [? [? ?]]; repeat subst
    | H : Succeeds _ (fptrnSnd _) _ |- _ => 
      apply Succeeds_fptrnSnd in H; destruct H as [? [? ?]]; repeat subst
end.

Ltac ptrn_sound_step :=
  first [
      ptrn_base_sound_step |
      ptrn_prod_sound_step
    ].

Class SucceedsE {X T : Type} (f : X) (p : ptrn X T) (v : T) := {
  s_result : Prop;
  s_elim : Succeeds f p v -> s_result
}.

Global Instance fptrnPair_SucceedsE {T : Type} {f : prod_func typ} {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :

  SucceedsE f (fptrnPair p) res := {
  s_result := exists t u, Succeeds (t, u) p res /\ f = pPair t u;
  s_elim := @Succeeds_fptrnPair typ T f p res  pok
}.

Global Instance fptrnFst_SucceedsE {T : Type} {f : prod_func typ} {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :

  SucceedsE f (fptrnFst p) res := {
  s_result := exists t u, Succeeds (t, u) p res /\ f = pFst t u;
  s_elim := @Succeeds_fptrnFst typ T f p res pok
}.

Global Instance fptrnSnd_SucceedsE {T : Type} {f : prod_func typ} {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :

  SucceedsE f (fptrnSnd p) res := {
  s_result := exists t u, Succeeds (t, u) p res /\ f = pSnd t u;
  s_elim := @Succeeds_fptrnSnd typ T f p res  pok
}.

Global Instance pmap_SucceedsE {X T U : Type} {x : X} {f : T -> U} {p : ptrn X T} {res : U} 
         {pok : ptrn_ok p} : 
  SucceedsE x (pmap f p) res := {
  s_result := exists y, Succeeds x p y /\ res = f y;
  s_elim := Succeeds_pmap pok
}.

Global Instance app_SucceedsE {T U : Type} {e : expr typ func} 
       {p : ptrn (expr typ func) T} {q : ptrn (expr typ func) U} {res : T * U} 
         {pok_p : ptrn_ok p} {pok_q : ptrn_ok q} :
  SucceedsE e (app p q) res := {
  s_result := exists l r, e = App l r /\ Succeeds l p (fst res) /\ Succeeds r q (snd res);
  s_elim := Succeeds_app pok_p pok_q
}.

Global Instance inj_SucceedsE {T : Type} {e : expr typ func} 
       {p : ptrn func T}  {res : T} 
         {pok_p : ptrn_ok p} :
  SucceedsE e (inj p) res := {
  s_result := exists f, e = Inj f /\ Succeeds f p res;
  s_elim := Succeeds_inj pok_p
}.

Global Instance get_SucceedsE {X : Type} {x res : X} :
  SucceedsE x get res := {
  s_result := x = res;
  s_elim := @Succeeds_get X x res 
}.

Global Instance ignore_SucceedsE {X : Type} {x : X} (res : unit) :
  SucceedsE x ignore res := {
  s_result := res = tt;
  s_elim := 
    fun _ => match res as x return (x = tt) with
               | tt => eq_refl
             end
}.

Global Instance ptrn_view_SucceedsE {A T : Type} {x : func} {res : T} {p : ptrn A T} 
       {FV : FuncView func A} {Sym_A : RSym A} {FVOk : FuncViewOk FV _ Sym_A}
       {pok : ptrn_ok p} :
  SucceedsE x (ptrn_view FV p) res := {
  s_result := exists f : A, f_insert f = x /\ Succeeds f p res;
  s_elim := @Succeeds_ptrn_view func A FV typ _ _ _ _ _ p x res _
}.


Ltac ptrn_elim :=
  repeat
   match goal with
   | H:Succeeds ?f ?p ?v
     |- _ =>
         let z := constr:(_:SucceedsE f p v) in
         apply s_elim in H; do 2 red in H; destruct_ands H
   end.

Ltac exprT_App_red :=
    match goal with
      | |- context [castR _ id _ _] => rewrite exprT_App_castR_pure
      | |- context [@exprT_App _ _ _ ?tus ?tvs _ _ (castR _ _ (Fun ?t1 ?t2) _) ?v] =>

        first [
            force_apply (@exprT_App_Fun' tus tvs t1 t2 _ _) |
            replace v with (castR typ (exprT tus tvs) _ v) by reflexivity;
              force_apply (@exprT_App_Fun' tus tvs t1 t2 _ _)
          ]
    end. 

Check @exprD'.
Require Import ExprD.
Class ExprDE tus tvs (e : expr typ func) (t : typ) (v : exprT tus tvs (typD t)) := {
  e_result : Prop;
  e_elim : exprD' tus tvs t e = Some v -> e_result
}.

Instance Injective_exprD'_App tus tvs (e1 e2 : expr typ func) (t : typ) (v : exprT tus tvs (typD t)):
  Injective (exprD' tus tvs t (App e1 e2) = Some v) := {
    result := exists u v1 v2, exprD' tus tvs (tyArr u t) e1 = Some v1 /\
                              exprD' tus tvs u e2 = Some v2 /\
                              v = exprT_App v1 v2;
    injection := fun H => _
}.
Proof.
  autorewrite with exprD_rw in H.
  simpl in H. forward; inv_all; subst.
  do 3 eexists; repeat split; eassumption.
Defined.

Instance Injective_exprD'_Inj tus tvs (f : func) (t : typ) (v : exprT tus tvs (typD t)):
  Injective (exprD' tus tvs t (Inj f) = Some v) := {
    result := exists v', symAs f t = Some v' /\ v = fun _ _ => v';
    injection := fun H => _
}.
Proof.
  autorewrite with exprD_rw in H.
  simpl in H. forward; inv_all; subst.
  eexists; repeat split.
Defined.
Instance Injective_exprD'_f_insert {A : Type} (a : A) (t : typ) (v : typD t) 
         {FV : FuncView func A} {RSym_A : RSym A}  {FVOk : FuncViewOk _ _ RSym_A} :
  Injective (symAs (f_insert a) t = Some v) := {
    result := symAs a t = Some v;
    injection := fun H => _
}.
Proof.
  rewrite fv_compat; assumption.
Defined.
Check Relim.
Definition symAs' := symAs.
Lemma test : @symAs' = @symAs.
Proof.
  reflexivity.
Qed.
Opaque symAs'.
(*
Instance Injective_pPair (a b c : typ) v : Injective (symAs (pPair a b) c = Some v) := {
  result := exists r : c = (tyArr a (tyArr b (tyProd a b))), v = Relim id r (pairR a b);
  injection := fun H => _
}.
Proof.
  unfold symAs in H.
  simpl in H. 
  forward.
  unfold Rty in r; subst.
  inv_all; subst. eexists; split.
Defined.
*)


    Ltac symAsE := 
      match goal with
        | H : symAs ?f ?t = Some ?v |- _ =>
          let Heq := fresh "Heq" in
          pose proof (typeof_sym_symAs _ _ H) as Heq;
            simpl in Heq; inv_all; repeat subst;
            unfold symAs in H; simpl in H; rewrite type_cast_refl in H; [|apply _];
            simpl in H; inv_all; subst
      end.

Ltac ptrnE :=
  ptrn_elim; destruct_prod; simpl in *; subst; inv_all; repeat subst;
  repeat symAsE.

  Lemma red_fst_ok : partial_reducer_ok (fun e args => red_fst (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_fst.
    
    apply run_tptrn_id_sound; [assumption|]; intros.
    ptrnE.
    unfold pairR, fstR.
    repeat exprT_App_red.
    apply H4.
  Qed.

End Tactics.