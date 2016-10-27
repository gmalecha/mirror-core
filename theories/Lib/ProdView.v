Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.
Require Import ExtLib.Relations.TransitiveClosure.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCore.Lambda.RedAll.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

(** TODO: This needs to move *)
Section thing.
  Variable typ : Set.
  Variable RType_typ : RType typ.
  Variable RTypeOk_typ : RTypeOk.
  Variable F : Type@{Urefl} -> Type@{Urefl} -> Type@{Urefl}.
  Variable Typ2_F : Typ2 _ F.
  Variable Typ2Ok_F : Typ2Ok Typ2_F.


  Definition typ2_Rty (a b c d : typ) (pf : Rty a b) (pf' : Rty c d)
    : Rty (typ2 a c) (typ2 b d).
    destruct pf. destruct pf'. apply eq_refl. Defined.

  Lemma xxx : forall {a b c d : typ} (pf : Rty (typ2  a b) (typ2 c d)),
      exists pf' pf'', pf = typ2_Rty pf' pf''.
  Proof.
    intros. generalize pf.
    intros. inv_all.
    subst. exists eq_refl. exists eq_refl. simpl.
    apply UIP_refl.
  Defined.

  Lemma symAs_D' :
    forall (Typ2_Fun : Typ2 RType_typ RFun)
      (func : Set) (RSym_func : RSym func),
      RTypeOk ->
      Typ2Ok Typ2_Fun ->
      RSymOk RSym_func ->
      forall (f : func) (t : typ) (v : typD t),
        symAs f t = Some v ->
        match typeof_sym f as X return match X with
                                       | None => unit
                                       | Some t => typD t
                                       end -> Prop with
        | None => fun _ => False
        | Some t' => fun d =>
                      exists pf : Rty t' t,
                        Rcast_val pf d = v
        end (symD f).
  Proof.
    clear. intros.
    unfold symAs in H1.
    generalize dependent (symD f).
    destruct (typeof_sym f).
    { intros. destruct (type_cast t t0).
      { exists (Rsym r). inv_all. unfold Rcast_val, Rcast, Relim in *.
        unfold Rsym. rewrite eq_sym_involutive. assumption. }
      { exfalso. clear - H1. discriminate H1. } }
    { clear. intros. discriminate H1. }
  Defined.
End thing.

Inductive prod_func {typ : Set} : Set :=
| pPair : typ -> typ -> prod_func
| pFst : typ -> typ -> prod_func
| pSnd : typ -> typ -> prod_func.

Arguments prod_func _ : clear implicits.

Section ExprDInject.
  Context {typ func : Set}.
  Context {RType_typ : RType typ} {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func} {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2_tyArr : Typ2 _ RFun} {Typ2Ok_tyArr : Typ2Ok Typ2_tyArr}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ Typ2_tyArr.

  Global Instance Injective_lambda_exprD_App tus tvs (e1 e2 : expr typ func) (t : typ)
         (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (App e1 e2) = Some v) := {
      result := exists u v1 v2, ExprDsimul.ExprDenote.lambda_exprD tus tvs (tyArr u t) e1 = Some v1 /\
                                ExprDsimul.ExprDenote.lambda_exprD tus tvs u e2 = Some v2 /\
                                v = AbsAppI.exprT_App v1 v2;
      injection := fun H => _
    }.
  Proof.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    do 3 eexists; repeat split; eassumption.
  Defined.

  Global Instance Injective_lambda_exprD_Inj tus tvs (f : func) (t : typ) (v : exprT tus tvs (typD t)):
    Injective (ExprDsimul.ExprDenote.lambda_exprD tus tvs t (Inj f) = Some v) := {
      result := exists v', symAs f t = Some v' /\ v = fun _ _ => v';
      injection := fun H => _
    }.
  Proof.
    autorewrite with exprD_rw in H.
    simpl in H. forward; inv_all; subst.
    eexists; repeat split.
  Defined.

End ExprDInject.


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

  Hint Extern 0 (PartialViewOk ?X _) =>
    match goal with
    | H : FuncViewOk _ _ _ |- _ => eexact H
    end : typeclass_instances.

  Lemma red_fst_ok : partial_reducer_ok (fun e args => red_fst (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_fst.
    eapply run_ptrn_id_sound; eauto with typeclass_instances.
    unfold red_fst_ptrn.
    intros.
    Ltac ptrnE :=
      let rec break_conj H :=
          lazymatch type of H with
          | exists x : _ , _ =>
            let H' := fresh in destruct H as [ ? H' ] ; break_conj H'
          | _ /\ _ =>
            let H' := fresh in let H'' := fresh in
            destruct H as [ H' H'' ] ; break_conj H' ; break_conj H''
          | _ => idtac
          end
      in
      match goal with
      | H : Succeeds ?e ?X ?r |- _ =>
        let el := constr:(_ : SucceedsE e X r) in
        eapply (@s_elim _ _ e X r el) in H; do 2 red in H ; break_conj H
      end.
    repeat ptrnE; subst.

    Require Import MirrorCore.Lambda.ExprTac.
    Require Import ExtLib.Tactics.
    inv_all. subst.

    
    eapply symAs_D' in H0. simpl in H0. destruct H0.
    eapply symAs_D' in H. simpl in H. destruct H.

    destruct (xxx _ _ x1) as [ ? [ ? ? ] ].
    subst.
    destruct (xxx _ _ x10) as [ ? [ ? ? ] ].
    subst.
    destruct (xxx _ _ x2) as [ ? [ ? ? ] ].
    subst.
    destruct x5. destruct x1. destruct x15. simpl in *.
    destruct x14.
    destruct (xxx _ _ x10) as [ ? [ ? ? ] ].
    subst. destruct x0. destruct x1. simpl.
    unfold Rcast_val, Rcast, Relim. simpl.
    rewrite H3. f_equal.
    unfold fstR.
    compute.

    Lemma Rty_typ2
      : forall (a b : typ)
          (P : forall c d : typ, Rty (typ2 a b) (typ2 c d) -> Prop),
        (forall c d (pf : Rty a c) (pf' : Rty b d),
            @P c d (typ2_Rty pf pf')) ->
        forall (c d : typ) (pf : Rty (typ2 a b) (typ2 c d)),
          P c d pf.
    Proof.
      clear - RTypeOk_typ Typ2Ok_tyProd. intros.
      generalize pf.
      intro. apply typ2_inj in pf; eauto.
      destruct pf.
      specialize (H c d H0 H1).
      cutrewrite (pf0 = typ2_Rty H0 H1). assumption.
      generalize (typ2_Rty H0 H1).
      clear - RTypeOk_typ.
      intros. destruct r.
      eapply UIP_refl.
    Defined.


Ltac exprT_App_red :=
  match goal with
  | |- context [castR id _ _] => rewrite exprT_App_castR_pure
  | |- context [@AbsAppI.exprT_App ?typ _ _ ?tus ?tvs _ _ (castR _ (RFun ?t1 ?t2) _) _] =>
    force_apply (@exprT_App_castR typ _ _ tus tvs t1 t2 _ _)
  | |- context [@AbsAppI.exprT_App ?typ _ _ ?tus ?tvs _ ?t2 ?e (castR _ ?t1 _)] =>
    force_apply (@exprT_App_castR2 typ _ _ _ _ _ _ _ tus tvs t1 (typD t2) _ _ e)
  | |- context [@castD ?typ _ (exprT ?tus ?tvs) ?u ?Tu
                       (@AbsAppI.exprT_App _ _ _ _ _ ?t _ ?a ?b)] =>
    force_apply (@exprT_App_castD typ _ _ tus tvs (typD t) u _ Tu a b)
  | |- _ => rewrite castDR
  | |- _ => rewrite castRD
  end.

Ltac symAsE :=
  match goal with
    | H : symAs ?f ?t = Some ?v |- _ =>
      let Heq := fresh "Heq" in
      pose proof (ExprFacts.symAs_typeof_sym _ _ H) as Heq;
        simpl in Heq; inv_all; repeat subst;
        unfold symAs in H; simpl in H; rewrite type_cast_refl in H; [|apply _];
        simpl in H; inv_all; subst
  end.


Ltac exprDI :=
  match goal with
    | |- context [ExprDsimul.ExprDenote.lambda_exprD ?tus ?tvs ?t (App ?e1 ?e2)] =>
      apply (@lambda_exprD_AppI _ _ _ _ _ _ _ _ tus tvs t e1 e2);
        (do 3 eexists); split; [exprDI | split; [exprDI | try reflexivity]]
    | |- context [ExprDsimul.ExprDenote.lambda_exprD ?tus ?tvs ?t (Inj ?f)] =>
      apply (@lambda_exprD_InjI _ _ _ _ _ _ _ _ tus tvs t f);
        eexists; split; [exprDI | try reflexivity]
    | |- context [symAs (f_insert ?p) ?t] =>
      apply (@symAs_finsertI _ _ _ _ _ _ _ _ t p);
        try (unfold symAs; simpl; rewrite type_cast_refl; [|apply _]; simpl; reflexivity)
(*    | |- context [ExprDsimul.ExprDenote.lambda_exprD ?tus ?tvs ?t (Red.beta ?e)] =>
      apply (@lambda_exprD_beta _ _ _ _ _ _ _ _ tus tvs e t);
        eexists; split; [exprDI | try reflexivity]
*)
    | _ => try eassumption
    | _ => try reflexivity
  end.
SearchAbout lambda_exprD.

    eapply Succeeds_pmap in H0; [ | eauto with typeclass_instances ].
    SearchAbout SucceedsE.

    repeat solve_denotation.
    unfold pairR, fstR.
    solve_denotation.
    eassumption.
  Qed.

  Lemma red_snd_ok : partial_reducer_ok (fun e args => red_snd (apps e args)).
  Proof.
    unfold partial_reducer_ok; intros.
    exists val; split; [|reflexivity].
    generalize dependent (apps e es); clear e es; intros e H.
    unfold red_snd.
    eapply run_ptrn_id_sound; eauto with typeclass_instances.
    unfold red_snd_ptrn.
    intros.
    repeat solve_denotation.
    unfold pairR, sndR.
    solve_denotation.
    assumption.
  Qed.

End Tactics.

Require Import MirrorCore.Reify.ReifyClass.

Section ReifyProd.
  Context {typ func : Type} {FV : PartialView func (prod_func typ)}.
  Context {t : Reify typ}.

  Definition reify_pair : Command (expr typ func) :=
    CPattern (ls := typ::typ::nil)
             (RApp (RApp (RExact (@pair)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fPair x y)).

  Definition reify_fst : Command (expr typ func) :=
    CPattern (ls := typ::typ::nil)
             (RApp (RApp (RExact (@fst)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fFst x y)).

  Definition reify_snd : Command (expr typ func) :=
    CPattern (ls := typ::typ::nil)
             (RApp (RApp (RExact (@snd)) (RGet 0 RIgnore)) (RGet 1 RIgnore))
             (fun (x y : function (CCall (reify_scheme typ))) => Inj (fSnd x y)).

  Definition reify_prod : Command (expr typ func) :=
    CFirst (reify_pair :: reify_fst :: reify_snd :: nil).

End ReifyProd.

Arguments reify_prod _ _ {_ _}.
