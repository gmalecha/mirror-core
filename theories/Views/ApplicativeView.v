Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ap_func typ :=
| pPure (_ : typ)
| pAp (_ _ : typ).
    
Implicit Arguments ap_func [].
    
Section ApplicativeFuncInst.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {T : Type -> Type} {Applicative_T : Applicative T}.

  Context {Typ2_tyArr : Typ2 _ Fun}.
  Context {Typ1_T : Typ1 _ T}.
    	
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyT : typ -> typ := @typ1 _ _ _ _.

  Definition typeof_ap_func (f : ap_func typ) : option typ :=
    match f with
    | pPure t => Some (tyArr t (tyT t))
    | pAp t u => Some (tyArr (tyT (tyArr t u)) (tyArr (tyT t) (tyT u)))
    end.

  Global Instance RelDec_ap_func : RelDec (@eq (ap_func typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
	  	       | pPure t, pPure t' => t ?[eq] t'
	  	       | pAp t u, pAp t' u' => t ?[eq] t' && u ?[eq] u'
	  	       | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_ap_func : RelDec_Correct RelDec_ap_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl; try rewrite andb_true_iff;
    repeat rewrite rel_dec_correct; try intuition congruence.
  Qed.

  Definition pureR t : typD (tyArr t (tyT t)) :=
    castR id (Fun (typD t) (T (typD t))) (@pure T Applicative_T (typD t)).

  Definition apR t u : typD (tyArr (tyT (tyArr t u)) (tyArr (tyT t) (tyT u))) :=
    castR id (Fun (T (Fun (typD t) (typD u))) (Fun (T (typD t)) (T (typD u))))
          (@ap T Applicative_T (typD t) (typD u)).
  
  Definition ap_func_symD f : match typeof_ap_func f return Type with
	                      | Some t => typD t
	                      | None => unit
	                      end :=
    match f as f return match typeof_ap_func f return Type with
			| Some t => typD t
			| None => unit
			end with
    | pPure t => pureR t
    | pAp t u => apR t u
    end.
      
    Global Instance RSym_ApFunc : SymI.RSym (ap_func typ) := {
      typeof_sym := typeof_ap_func;
      symD := ap_func_symD;
      sym_eqb := (fun a b => Some (rel_dec a b))
    }.

  Global Instance RSymOk_lopen_func : SymI.RSymOk RSym_ApFunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End ApplicativeFuncInst.

Section MakeApplicative.
  Context {typ func : Type} {RType_typ : RType typ}.
  Context {FV : FuncView func (ap_func typ)}.
  Context {Typ2_tyArr : Typ2 _ Fun}.
    	
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Definition fPure t := f_insert (pPure t).
  Definition fAp t u := f_insert (pAp t u).

  Definition mkPure (t : typ) (f : expr typ func) : expr typ func := App (Inj (fPure t)) f.
  Definition mkAp (t u : typ) (f a : expr typ func) := App (App (Inj (fAp t u)) f) a.

  Fixpoint mkAps f es t :=
    match es with 
    | nil => mkPure t f
    | (e, t')::es => mkAp t' t (mkAps f es (tyArr t' t)) e
    end.

  Definition fptrnPure {T : Type} (p : Ptrns.ptrn typ T) : ptrn (ap_func typ) T :=
    fun f U good bad =>
      match f with
        | pPure t => p t U good (fun _ => bad (pPure t))
        | pAp t u => bad (pAp t u)
      end.

  Definition fptrnAp {T : Type} (p : Ptrns.ptrn (typ * typ) T) : ptrn (ap_func typ) T :=
    fun f U good bad =>
      match f with
        | pPure t => bad (pPure t)
        | pAp t u => p (t, u) U good (fun _ => bad (pAp t u))
      end.

  Global Instance fptrnPure_ok {T : Type} {p : ptrn typ T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnPure p).
  Proof.
    red; intros.
    destruct x; simpl; [destruct (Hok t) |].
    { left. destruct H; exists x. revert H. compute; intros.
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
    { right; unfold Fails; reflexivity. }
  Qed.

  Global Instance fptrnAp_ok {T : Type} {p : ptrn (typ * typ) T} {Hok : ptrn_ok p} :
    ptrn_ok (fptrnAp p).
  Proof.
    red; intros.
    destruct x; simpl; [|destruct (Hok (t, t0))].
    { right; unfold Fails; reflexivity. }
    { left. destruct H; exists x; revert H; compute; intros. 
      rewrite H. reflexivity. }
    { right; unfold Fails in *; intros; simpl; rewrite H; reflexivity. }
  Qed.

  Definition ptrnPure {T A : Type}
             (p : ptrn typ T)  (a : ptrn (expr typ func) A) : ptrn (expr typ func) (T * A):=
    app (inj (ptrn_view _ (fptrnPure p))) a.

  Definition ptrnAp {A B T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A) 
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnAp p))) a) b.

  Lemma Succeeds_fptrnPure {T : Type} (f : ap_func typ) (p : ptrn typ T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnPure p) res) :
    exists t, Succeeds t p res /\ f = pPure t.
  Proof.
    unfold Succeeds, fptrnPure in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok t).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t; split; [assumption | reflexivity].
  Qed.

  Lemma Succeeds_fptrnAp {T : Type} (f : ap_func typ) (p : ptrn (typ * typ) T) (res : T)
        {pok : ptrn_ok p} (H : Succeeds f (fptrnAp p) res) :
    exists t u, Succeeds (t, u) p res /\ f = pAp t u.
  Proof.
    unfold Succeeds, fptrnAp in H.
    unfold ptrn_ok in pok.
    specialize (H (option T) Some (fun _ => None)).
    destruct f; try congruence.
    specialize (pok (t, t0)).
    destruct pok; [|rewrite H0 in H; congruence].
    destruct H0.
    rewrite H0 in H; inv_all; subst.
    exists t, t0; split; [assumption | reflexivity].
  Qed.
  
  Global Instance fptrnPure_SucceedsE {T : Type} {f : ap_func typ} 
         {p : ptrn typ T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnPure p) res := {
      s_result := exists t, Succeeds t p res /\ f = pPure t;
      s_elim := @Succeeds_fptrnPure T f p res pok
    }.

  Global Instance fptrnAp_SucceedsE {T : Type} {f : ap_func typ} 
         {p : ptrn (typ * typ) T} {res : T} {pok : ptrn_ok p} :
    SucceedsE f (fptrnAp p) res := {
      s_result := exists t u, Succeeds (t, u) p res /\ f = pAp t u;
      s_elim := @Succeeds_fptrnAp T f p res pok
    }.

  Definition applicative_ptrn_cases {T : Type}
             (do_pure : typ  -> expr typ func -> T)
             (do_ap : typ -> typ -> expr typ func -> expr typ func -> T) :=
    por (appr (inj (ptrn_view _ (fptrnPure (pmap do_pure Ptrns.get)))) Ptrns.get)
        (appr (appr (inj (ptrn_view _ (fptrnAp (pmap (fun x a b => do_ap (fst x) (snd x) a b)
                                                     Ptrns.get))))
                    Ptrns.get) 
              Ptrns.get).

Definition applicative_cases {T : Type}
           (do_pure : typ  -> expr typ func -> T)
           (do_ap : typ -> typ -> expr typ func -> expr typ func -> T) 
           (do_default : T) : Ptrns.tptrn (expr typ func) T :=
  pdefault (applicative_ptrn_cases do_pure do_ap)
           do_default.

End MakeApplicative.
