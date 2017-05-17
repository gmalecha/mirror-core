Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprVariables.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Reify.ReifyClass.
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.CTypeUnify.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ap_func (typ : Set) : Set :=
| pPure (_ : typ)
| pAp (_ _ : typ).

Arguments ap_func _ : clear implicits.

Section ApplicativeFuncInst.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.
  Context {T : Type -> Type} {Applicative_T : Applicative T}.

  Context {Typ2_tyArr : Typ2 _ RFun}.
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
    castR id (RFun (typD t) (T (typD t))) (@pure T Applicative_T (typD t)).

  Definition apR t u : typD (tyArr (tyT (tyArr t u)) (tyArr (tyT t) (tyT u))) :=
    castR id (RFun (T (RFun (typD t) (typD u))) (RFun (T (typD t)) (T (typD u))))
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

Section ApplicativeUnify.
  Context {typ' : nat -> Set}.
  
  Let typ := ctyp typ'.

  Definition ap_func_unify (a b : ap_func typ) (s : FMapPositive.pmap typ) : 
    option (FMapPositive.pmap typ) :=
    match a, b with
    | pPure t, pPure t' => ctype_unify_slow _ t t' s
    | pAp t u, pAp t' u' => 
      match ctype_unify_slow _ t t' s with
      | Some s' => ctype_unify_slow _ u u' s'
      | None => None
      end
    | _, _ => None
    end.

End ApplicativeUnify.

Section MakeApplicative.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {FV : PartialView func (ap_func typ)}.
  Context {Typ2_tyArr : Typ2 _ RFun}.

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
    SucceedsE f (fptrnAp p) res :=
  { s_result := exists t u, Succeeds (t, u) p res /\ f = pAp t u
  ; s_elim := @Succeeds_fptrnAp T f p res pok
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
  : Ptrns.ptrn (expr typ func) T :=
  applicative_ptrn_cases do_pure do_ap.

End MakeApplicative.

Section PtrnApplicative.
  Context {typ func : Set} {RType_typ : RType typ}.
  Context {FV : PartialView func (ap_func typ)}.

(* Putting this in the previous sectioun caused universe inconsistencies
  when calling '@mkAp typ func' in JavaFunc (with typ and func instantiated) *)

  Definition ptrnPure {T A : Type}
             (p : ptrn typ T)  (a : ptrn (expr typ func) A)
  : ptrn (expr typ func) (T * A):=
    app (inj (ptrn_view _ (fptrnPure p))) a.

  Definition ptrnAp {A B T : Type}
             (p : ptrn (typ * typ) T)
             (a : ptrn (expr typ func) A)
             (b : ptrn (expr typ func) B) : ptrn (expr typ func) (T * A * B) :=
    app (app (inj (ptrn_view _ (fptrnAp p))) a) b.

End PtrnApplicative.

Section ReifyApplicative.
  Context {typ func : Set} {FV : PartialView func (ap_func typ)}.
  Context {T : Type -> Type} {IH : Applicative T}.
  Context {t : Reify typ}.

  Definition reify_pure : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::nil)
             (RApp (RApp (RExact (@pure T)) RIgnore) (RGet 0 RIgnore))
             (fun (x : function (CCall (reify_scheme typ))) => Inj (fPure x)).

  Definition reify_ap : Command (expr typ func) :=
    CPattern (ls := (typ:Type)::(typ:Type)::nil)
             (RApp (RApp (RApp (RExact (@ap T)) RIgnore) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fAp x y)).

  Definition reify_applicative : Command (expr typ func) :=
    CFirst (reify_pure :: reify_ap :: nil).
  
End ReifyApplicative.

Arguments reify_applicative _ _ {_} _ {_}.

Section ReduceApplicative.
  Context {typ' : nat -> Set} {func : Set}.
  Let typ := ctyp typ'.
  Context {TSym_typ' : TSym typ'}.
  Local Instance RType_typ : RType typ := (RType_ctyp typ' _).
  Local Instance Typ2_typ : Typ2 _ RFun := Typ2_Fun.
  Context {RSym_func : RSym (typ := typ) func}.
  Context {FV : PartialView func (ap_func typ)}.

  Definition red_ap_ptrn 
             (f : typ -> expr typ func -> typ * expr typ func) :
    ptrn (expr typ func) (typ * expr typ func) :=
    applicative_cases
      (fun t p => (t, p))
      (fun t u p q => (u, App (snd (f (tyArr t u) p)) (snd (f t q)))).

  Fixpoint expr_eqb (e1 e2 : expr typ func) : option bool :=
    match e1 , e2 with
      | Var v1 , Var v2 => Some (EqNat.beq_nat v1 v2)
      | UVar v1 , UVar v2 => Some (EqNat.beq_nat v1 v2)
      | Inj f1 , Inj f2 =>
        sym_eqb f1 f2
      | App f1 e1 , App f2 e2 =>
        match expr_eqb f1 f2 with
        | Some true => expr_eqb e1 e2
        | Some false => Some false
        | None => None
        end
      | Abs t1 e1 , Abs t2 e2 =>
        if ctyp_dec typ' _ t1 t2 then expr_eqb e1 e2
        else Some false
      | _ , _ => Some false
    end.

  Definition restore_ap_ptrn (tus tvs : tenv typ) (s : expr typ func)
    (f : expr typ func -> (typ * expr typ func)) :=
      pmap (fun a_b => 
              let '(a, b) := a_b in 
                if expr_eqb a s then
                  match typeof_expr tus tvs a with
                  | Some (tyArr _ v) => (v, a)
                  | _ => (tyProp, a) (* should never happen *)
                  end
                else
                  let (t, ra) := f a in
                  match t with
                  | tyArr u v => 
                    let (_, rb) := f b in
                      (v, mkAp u v ra rb)
                  | _ => (t, ra) (* should never happen *)
                  end)
           (app get get).

  Definition restore_pure_ptrn (tus tvs : tenv typ) : 
    ptrn (expr typ func) (typ * expr typ func) :=
    fun e U good bad =>
      match typeof_expr tus tvs e with
      | Some t => good (t, mkPure t e)
      | None => bad e
      end.

End ReduceApplicative.