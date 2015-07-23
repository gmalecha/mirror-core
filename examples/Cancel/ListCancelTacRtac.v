Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.Lemma.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.RTac.InContext.

Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section canceller.
  Variables typ func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Typ0_Prop : Typ0 RType_typ Prop}.
  Context {Typ1_List : Typ1 RType_typ list}.
  Context {Typ2_func : Typ2 RType_typ Fun}.
  Context {Typ2Ok_func : Typ2Ok Typ2_func}.
  Context {Typ1Ok_list : Typ1Ok Typ1_List}.
  Context {RSym_sym : RSym func}.
  Context {RSymOk_sym : RSymOk RSym_sym}.
  Context {RelDeq_eq : RelDec (@eq typ)}.

  Context {LF : FuncView func (list_func typ)}.
  Context {LFOk : @FuncViewOk _ _ LF typ RType_typ _ _}.

  (** NOTE: These are already implemented in ListView **)
  Definition ptrn_nil {T} (p : Ptrns.ptrn typ T) : Ptrns.ptrn (list_func typ) T :=
    fun e _T good bad =>
      match e with
      | pNil t => p t _T good (fun x => bad (pNil x))
      | pCons t => bad (pCons t)
      end.

  Instance ptrn_ok_nil {T} p : Ptrns.ptrn_ok p -> Ptrns.ptrn_ok (@ptrn_nil T p).
  Proof.
    unfold ptrn_nil, Ptrns.ptrn_ok.
    intros. destruct x.
    { specialize (H t).
      destruct H as [ [ ? ? ] | ? ].
      { left; exists x.
        red. eauto. }
      { right. red.
        red in H. setoid_rewrite H. reflexivity. } }
    { right. red. reflexivity. }
  Qed.

  Definition ptrn_cons {T} (p : Ptrns.ptrn typ T) : Ptrns.ptrn (list_func typ) T :=
    fun e _T good bad =>
      match e with
      | pNil t => bad (pNil t)
      | pCons t => p t _T good (fun x => bad (pCons t))
      end.

  Instance ptrn_ok_cons {T} p : Ptrns.ptrn_ok p -> Ptrns.ptrn_ok (@ptrn_cons T p).
  Proof.
    unfold ptrn_nil, Ptrns.ptrn_ok.
    intros. destruct x.
    { right. red. reflexivity. }
    { specialize (H t).
      destruct H as [ [ ? ? ] | ? ].
      { left; exists x.
        red. eauto. }
      { right. red.
        red in H. setoid_rewrite H. reflexivity. } }
  Qed.

  Variable ctx : Ctx typ (expr typ func).

  Definition list_cases {T : Type}
             (do_nil : typ -> T)
             (do_cons : typ -> expr typ func -> expr typ func -> T)
             (do_default : T)
  : Ptrns.tptrn (expr typ func) T :=
    Ptrns.pdefault
      (Ptrns.por
         (Ptrns.pmap (do_nil) (Ptrns.inj (ptrn_view LF (ptrn_nil Ptrns.get))))
         (Ptrns.pmap (fun t_x_xs =>
                        let '(t,x,xs) := t_x_xs in
                        do_cons t x xs)
                     (Ptrns.app (Ptrns.app (Ptrns.inj (ptrn_view LF (ptrn_cons Ptrns.get))) Ptrns.get) Ptrns.get)))
      do_default.

  Require Import ExtLib.Data.Monads.IdentityMonad.

  (** TODO: This should go elsewhere **)
  Instance MonadLogic_ident : @MonadLogic ident _ :=
  { Pred := fun {T : Type} (P : T -> Prop) (id : ident T) => P (unIdent id) }.
  Proof.
    { compute. intros; tauto. }
    { compute. destruct c. eauto. }
    { compute. intros; subst. eauto. }
  Defined.


  Definition check_equality
  : typ -> expr typ func -> expr typ func -> InContext ident ctx bool :=
    fun _t x y =>
      Monad.ret (expr_eq_sdec _ (fun a b =>
                                   match sym_eqb a b with
                                   | Some true => true
                                   | _ => false
                                   end) x y).

  Fixpoint remove (e lst : expr typ func) {struct lst}
  : InContext ident ctx (option (expr typ func)) :=
    Ptrns.run_tptrn
      (list_cases (T := InContext ident ctx (option (expr typ func)))
                  (fun (_ : typ) =>
                     Monad.ret None)
                  (fun t x xs =>
                     Monad.bind (check_equality t x e)
                                (fun yes_or_no =>
                                   if yes_or_no then
                                     Monad.ret (Monad.ret xs)
                                   else
                                     Monad.bind (remove e xs)
                                                (fun xs' => Monad.ret (Functor.fmap (F:=option) (mkCons t x) xs'))))
                  (Monad.ret None))
      lst.

  Lemma remove_eta : forall e lst,
      remove e lst =
      Ptrns.run_tptrn
      (list_cases (T := InContext ident ctx (option (expr typ func)))
                  (fun (_ : typ) =>
                     Monad.ret None)
                  (fun t x xs =>
                     Monad.bind (check_equality t x e)
                                (fun yes_or_no =>
                                   if yes_or_no then
                                     Monad.ret (Monad.ret xs)
                                   else
                                     Monad.bind (remove e xs)
                                                (fun xs' => Monad.ret (Functor.fmap (F:=option) (mkCons t x) xs'))))
                  (Monad.ret None))
      lst.
  Proof.
    clear. intros.
    destruct lst; reflexivity.
  Qed.

  Require Import Coq.Sorting.Permutation.
  Require Import MirrorCore.Views.Ptrns.
  Require Import MirrorCore.Lambda.Ptrns.
  Require Import ExtLib.Tactics.

  (** TODO: These should go elsewhere **)
  Definition castD F U {T : Typ0 _ U} (val : F (typD (typ0 (F:=U)))) : F U :=
    match @typ0_cast typ _ _ T in _ = x return F x with
    | eq_refl => val
    end.

  Definition castR F U {T : Typ0 _ U} (val : F U) : F (typD (typ0 (F:=U))) :=
    match eq_sym (@typ0_cast typ _ _ T) in _ = x return F x with
    | eq_refl => val
    end.

  Arguments castR F U {T} val.
  Arguments castD F U {T} val.

  (** TODO: These should not be necessary **)
  Existing Instance Typ2_App.
  Existing Instance Typ1_App.
  Existing Instance Typ0_term.
  Existing Instance Expr_expr.

  Existing Instance ptrn_view_ok.
  Existing Instance ptrn_ok_por.
  Existing Instance ptrn_ok_pmap.
  Existing Instance ptrn_ok_app.
  Existing Instance ptrn_ok_inj.
  Existing Instance Injective_Succeeds_pmap.
  Existing Instance Injective_Succeeds_app.
  Existing Instance Injective_Succeeds_inj.
  Existing Instance Injective_Succeeds_get.

  Hypothesis InContext_spec_check_equality
    : forall t (e1 e2 : expr typ func),
      InContext_spec (Expr_expr typ func _ _) Typ0_Prop
                     MonadLogic_ident (fun _ => True)
                     (fun (y : bool) =>
                        match exprD' (getUVars ctx) (getVars ctx) e1 t
                              , exprD' (getUVars ctx) (getVars ctx) e2 t
                        with
                        | Some e1D , Some e2D =>
                          Some (fun c =>
                                  if y
                                  then e1D (fst c) (snd c) = e2D (fst c) (snd c)
                                  else True)
                        | _ , _ => None
                        end)
                     (check_equality t e1 e2).

  (** TODO: These should go elsewhere **)
  Lemma exprD'_App
    : forall tus tvs e1 e2 t eD,
      exprD' tus tvs (App e1 e2) t = Some eD ->
      exists u e1D e2D,
        exprD' tus tvs e1 (typ2 u t) = Some e1D /\
        exprD' tus tvs e2 u = Some e2D /\
        eD = exprT_App e1D e2D.
  Proof using RSymOk_sym RTypeOk_typ Typ2Ok_func.
    intros.
    unfold exprD' in H. simpl in H.
    rewrite exprD'_App in H.
    simpl in H.
    Require Import MirrorCore.Util.Forwardy.
    forwardy.
    do 3 eexists; split; eauto.
    eapply H0.
    split; eauto.
    inv_all. eauto.
  Qed.

  Lemma Succeeds_ptrn_cons
    : forall T (p : ptrn typ T) e res,
      ptrn_ok p ->
      Succeeds e (ptrn_cons p) res ->
      exists t, e = pCons t /\
                Succeeds t p res.
  Proof using.
    intros.
    destruct e.
    { red in H0. simpl in H0.
      specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
    { red in H0; simpl in H0.
      eexists; split; eauto.
      destruct (H t).
      { destruct H1. red in H1. red.
        setoid_rewrite H1 in H0.
        setoid_rewrite H1.
        eauto. }
      { red in H1. setoid_rewrite H1 in H0.
        specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. } }
  Qed.

  Instance Injective_Succeeds_ptrn_cons T p e (res : T) : ptrn_ok p -> Injective (Succeeds e (ptrn_cons p) res) :=
  { injection := @Succeeds_ptrn_cons _ _ _ _ _ }.

  Definition exprT_pure {T} (tus tvs : tenv typ) (x : T) : exprT tus tvs T :=
    fun _ _ => x.
  Lemma exprD'_Inj
    : forall tus tvs (i : func) (t : typ) iD,
      exprD' tus tvs (Inj i) t = Some iD ->
      exists iD',
        symAs i t = Some iD' /\
        iD = exprT_pure iD'.
  Proof.
    intros.
    unfold exprD' in H; simpl in H.
    rewrite exprD'_Inj in H; eauto with typeclass_instances.
    unfold Monad.bind in H. simpl in H.
    destruct (symAs i t); try congruence.
    inv_all.
    subst. eexists; split; eauto.
  Qed.

  Lemma symAs_f_insert
    : forall (t : typ) (s : list_func typ) sD,
      symAs (f_insert s) t = Some sD ->
      exists pf : typeof_sym s = Some t,
        sD = match pf in _ = T return match T with
                                      | Some t => typD t
                                      | None => unit:Type
                                      end with
             | eq_refl => symD s
             end.
  Proof.
    intros.
    rewrite <- fv_compat in H.
    unfold symAs in H.
    generalize dependent (symD s).
    destruct (typeof_sym s); intros; try congruence.
    destruct (type_cast t t0); try congruence.
    red in r. subst.
    exists eq_refl.
    inv_all. symmetry. assumption.
  Qed.

  Lemma exprD'_mkCons
    : forall tus tvs t e1 e2 e1D e2D,
      exprD' tus tvs e1 t = Some e1D ->
      exprD' tus tvs e2 (typ1 t) = Some e2D ->
      exprD' tus tvs (mkCons t e1 e2) (typ1 t) = Some (exprT_App (exprT_App (exprT_pure (consD t)) e1D) e2D).
  Proof using Typ1Ok_list Typ2Ok_func RTypeOk_typ RSymOk_sym LFOk.
    intros. unfold mkCons.
    unfold exprD' in *; simpl in *.
    autorewrite with exprD_rw; eauto with typeclass_instances.
    simpl.
    erewrite ExprTac.exprD_typeof_Some by eauto.
    autorewrite with exprD_rw; eauto with typeclass_instances. simpl.
    erewrite ExprTac.exprD_typeof_Some by eauto.
    Cases.rewrite_all_goal.
    autorewrite with exprD_rw; eauto with typeclass_instances. simpl.
    unfold fCons.
    rewrite <- fv_compat.
    unfold symAs. simpl.
    rewrite type_cast_refl; eauto.
  Qed.

  Ltac drive_exprD' :=
    repeat match goal with
           | H : exprD' _ _ _ _ = Some _ |- _ =>
             first [ eapply exprD'_App in H ; forward_reason ; subst
                   | eapply exprD'_Inj in H ; forward_reason ; subst ]
           | H : _ = Some _ |- _ =>
             eapply symAs_f_insert in H ; forward_reason ; subst
           end.

  Instance Injective_Succeeds_ptrn_view
    : forall (func A : Type) (FV : FuncView func A) (typ : Type)
             (RType_typ : RType typ) (Sym_func : RSym func) 
             (Sym_A : RSym A),
      FuncViewOk FV Sym_func Sym_A ->
      forall (T : Type) (p : ptrn A T) (x : func) (res : T),
        ptrn_ok p ->
        Injective (Succeeds x (ptrn_view FV p) res) :=
    { injection := @Succeeds_ptrn_view _ _ _ _ _ _ _ _ _ _ _ _ _ }.

  Axiom todo : forall T, T.

  Theorem exprT_App_cons
  : forall tus tvs (t : typ) (a : exprT tus tvs (typD t)) (b : exprT _ _ (typD (typ1 t)))
           us vs,
      castD (fun x => x) (typD t) (T:=Typ0_term _ t) (a us vs) ::
            castD (fun x => x) (list (typD t)) (T:=@Typ1_App _ _ list (typD t) Typ1_List (Typ0_term _ t)) (b us vs) =
      castD (fun x => x) (list (typD t)) (T:=@Typ1_App _ _ list (typD t) Typ1_List (Typ0_term _ t))
            ((exprT_App (exprT_App (exprT_pure (consD t)) a) b) us vs).
  Proof.
    clear InContext_spec_check_equality.
    intros. unfold castD, exprT_App, exprT_pure, consD, TrmD.tyArrR2, TrmD.tyArrR2', TrmD.tyArrR', TrmD.trmR, listR, TrmD.trmR, listE, TrmD.funE, TrmD.trmD.
    simpl. unfold id, eq_rect_r, eq_rect, eq_rec.
    Require Import MirrorCore.Util.Compat.
    autorewrite_with_eq_rw.
    generalize (a us vs).
    generalize (b us vs).
    uip_all.
    rewrite Eq.match_eq_sym_eq with (pf :=e0).
    rewrite Eq.match_eq_sym_eq with (pf :=e1).
    destruct e2.
    clear - RTypeOk_typ.
    apply todo. (** Jesper's stuff? **)
  Qed.

  Theorem remove_sound
  : forall e lst (t : typ) eD lstD,
      @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) e t = Some eD ->
      @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst (typ1 t) = Some lstD ->
      @InContext_spec typ (expr typ func)
                      ident _ _ _ _ _
                      (option (expr typ func))
                      (fun x => True) ctx
                      (fun (e' : option (expr typ func)) =>
                         match e' with
                         | None => Some (fun _ => True)
                         | Some e' =>
                           match @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) e' (typ1 t) with
                           | Some lst'D =>
                             Some (fun env => let '(us,vs) := env in
                                     Permutation (castD (fun x => x) (typD t) (T:=@Typ0_term _ _ _) (eD us vs) ::
                                                  castD (fun x => x) (list (typD t)) (T:=@Typ1_App _ _ _ _ Typ1_List (@Typ0_term _ _ t))
                                                        (lst'D us vs))
                                                 (castD (fun x => x) (list (typD t)) (T:=@Typ1_App _ _ _ _ Typ1_List (@Typ0_term _ _ t)) (lstD us vs)))
                           | None => None
                           end
                         end)
                      (remove e lst).
  Proof.
    Opaque exprD'.
    intros e lst t eD lstD He. revert lstD.
    eapply expr_strong_ind_no_case with (e:=lst); intros.
    rewrite remove_eta.
    unfold Ptrns.run_tptrn, list_cases.
    eapply Ptrns.pdefault_sound.
    { repeat first [ simple eapply ptrn_ok_por
                   | simple eapply ptrn_ok_pmap
                   | simple eapply ptrn_ok_inj
                   | simple eapply ptrn_ok_app
                   | simple eapply ptrn_view_ok
                   | eauto with typeclass_instances ]. }
    { red. red. red.
      intros. subst.
      red in H2.
      red in H2. erewrite H2. reflexivity.
      reflexivity. }
    { intros.
      eapply Succeeds_por in H1; try solve [ instantiate ; eauto 100 with typeclass_instances ].
      destruct H1; inv_all.
      { subst. unfold ptret.
        eapply InContext_spec_ret; [ tauto | ].
        intros. split; auto.
        eexists; split; eauto.
        intros.
        eapply Pure_pctxD; eauto. }
      { destruct x as [ [ ? ? ] ? ].
        subst.
        inv_all.
        simpl in * |-.
        unfold ptret.
        drive_exprD'.
        simpl in x3.
        assert (t0 = x2 /\ x = typ1 t0 /\ t = t0) by
           (clear - x3 Typ2Ok_func Typ1Ok_list; inv_all; subst; auto).
        forward_reason; subst.
        rewrite (UIP_refl x3); clear x3.
        eapply InContext_spec_bind.
        { eapply InContext_spec_check_equality. }
        { clear InContext_spec_check_equality.
          destruct x.
          { clear H.
            eapply InContext_spec_ret; try solve [ simpl ; eauto ].
            simpl.
            intros. split; eauto.
            Cases.rewrite_all_goal.
            eexists; split; eauto.
            simpl. intros.
            eapply Pure_pctxD; eauto.
            intros.
            rewrite <- H3; clear - RTypeOk_typ.
            rewrite <- exprT_App_cons.
            reflexivity. }
          { eapply InContext_spec_bind.
            { eapply H;
              eauto using TransitiveClosure.LTFin, TransitiveClosure.LTStep,
                          acc_App_l, acc_App_r. }
            clear H.
            intros.
            eapply InContext_spec_ret; [ tauto | ].
            simpl. intros; split; auto.
            Cases.rewrite_all_goal.
            destruct x.
            { intros.
              destruct (exprD' (getUVars ctx) (getVars ctx) e0 (typ1 x2)) eqn:Heq.
              { erewrite exprD'_mkCons by eauto.
                eexists; split; eauto. simpl.
                intros.
                eapply Pure_pctxD; eauto.
                intros. inv_all.
                rewrite <- exprT_App_cons.
                rewrite <- exprT_App_cons.
                eapply perm_trans; [ eapply perm_swap | ].
                eapply perm_skip. eassumption. }
              { eexists; split; eauto.
                simpl. intros. eapply Pure_pctxD; eauto. } }
            { eexists; split; eauto.
              intros.
              eapply Pure_pctxD; eauto. } } } } }
    { unfold ptret.
      eapply InContext_spec_ret; try tauto.
      intros. split; auto.
      eexists; split; eauto.
      intros.
      eapply Pure_pctxD; eauto. }
  Time Qed.

  (** TODO: This should go in InContext *)
  Instance MonadPlus_InContext {m : Type -> Type} {M : Monad.Monad m} {Mp : MonadPlus.MonadPlus m}
  : MonadPlus.MonadPlus (InContext m ctx) :=
  { mplus := fun _A _B ml mr ctx =>
               Monad.bind (MonadPlus.mplus (ml ctx) (mr ctx))
                          (fun x =>
                             Monad.ret match x with
                                       | inl (a,b) => (a, inl b)
                                       | inr (a,b) => (a, inr b)
                                       end) }.

(*
  Definition liftOption {T} (x : InContext option ctx T)
  : InContext ident ctx (option T).
  clear - x.
  red. red in x.
  intro. specialize (x X).
  constructor.
  destruct x.
  { exact (fst p, Some (snd p)). }
  { exact (X, None). }
  Defined.
*)

  Fixpoint cancel (lst1 lst2 : expr typ func) {struct lst1} :=
    Ptrns.run_tptrn
      (list_cases (T := InContext ident ctx (expr typ func * expr typ func))
                  (fun t => Monad.ret (mkNil t, lst2))
                  (fun t x xs =>
                     Monad.bind (remove x lst2)
                                (fun olst2 =>
                                   match olst2 with
                                   | Some lst2' => cancel xs lst2'
                                   | None =>
                                     Monad.bind (cancel xs lst2)
                                                (fun a_b => let '(lst1',lst2') := a_b in
                                                            Monad.ret (mkCons t x lst1', lst2'))
                                   end))
                  (Monad.ret (lst1, lst2)))
      lst1.

(*
  Eval compute in fun ty x => cancel (mkCons ty x (mkNil ty)) (mkCons ty x (mkNil ty)).
*)

End canceller.

Section demo.
  Inductive typ :=
  | tyArr : typ -> typ -> typ
  | tyList : typ -> typ
  | tyProp : typ
  | tyNat : typ.

  Inductive typ_acc : typ -> typ -> Prop :=
  | tyArr_l : forall a b, typ_acc a (tyArr a b)
  | tyArr_r : forall a b, typ_acc b (tyArr a b)
  | tyList_l : forall a, typ_acc a (tyList a).

  Instance RelDec_eq_typ : RelDec (@eq typ) :=
  { rel_dec := fix eqb a b : bool :=
      match a , b with
      | tyProp , tyProp
      | tyNat , tyNat => true
      | tyList a , tyList b => eqb a b
      | tyArr a b , tyArr c d => if eqb a c then eqb b d else false
      | _ , _ => false
      end }.

  Fixpoint typ_type_cast (a b : typ) : option (a = b) :=
    match a as a , b as b return option (a = b) with
    | tyNat , tyNat => Some eq_refl
    | tyProp , tyProp => Some eq_refl
    | tyList a , tyList b => match typ_type_cast a b with
                             | Some pf => Some (match pf in _ = t return tyList a = tyList t with
                                                | eq_refl => eq_refl
                                                end)
                             | None => None
                             end
    | tyArr a b , tyArr c d => match typ_type_cast a c , typ_type_cast b d with
                               | Some pf1 , Some pf2 => Some (match pf1 in _ = t1 , pf2 in _ = t2
                                                                    return tyArr a b = tyArr t1 t2
                                                              with
                                                              | eq_refl , eq_refl => eq_refl
                                                              end)
                               | _ , _ => None
                               end
    | _ , _ => None
    end.

  Instance RType_typ : RType typ :=
  { typD := fix typD x : Type :=
              match x return Type with
              | tyNat => nat
              | tyProp => Prop
              | tyList t => list (typD t)
              | tyArr a b => typD a -> typD b
              end
  ; tyAcc := typ_acc
  ; type_cast := typ_type_cast
  }.

  Definition func := list_func typ.

  Fixpoint func_eqb (a b : func) : option bool :=
    match a , b with
    | pNil a , pNil b
    | pCons a , pCons b => Some (a ?[ eq ] b)
    | _ , _ => Some false
    end.

  Instance RSym_func : @RSym _ RType_typ func :=
  { typeof_sym := fun x =>
                    match x with
                    | pNil t => Some (tyList t)
                    | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
                    end
  ; symD := fun x =>
              match x with
              | pNil t => @nil (typD t)
              | pCons t => @cons (typD t)
              end
  ; sym_eqb := func_eqb
  }.

  Instance FuncView_list_func : FuncView func (list_func typ) :=
  { f_insert := fun x => x
  ; f_view := Some }.

  Definition cncl ctx
  : expr typ func -> expr typ func ->
    @InContext typ (expr typ func) ident ctx (expr typ func * expr typ func).
      eapply cancel; eauto with typeclass_instances.
  Defined.

  Eval compute in cncl (mkNil tyNat) (mkNil tyNat).
  Time Eval vm_compute in fun ctx =>
      let lst1 := (mkCons (tyList tyNat) (mkNil tyNat) (mkNil (tyList tyNat))) in
      let lst2 := lst1 in
      cncl (ctx:=ctx) lst1 lst2.

End demo.