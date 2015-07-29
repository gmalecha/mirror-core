Require Import Coq.Sorting.Permutation.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.ListView.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.RTac.InContext.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Ptrns.
Require Import MirrorCore.ExprI. (** TODO: This should move **)
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.

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

  Variable ctx : Ctx typ (expr typ func).

  Definition list_cases {T : Type}
             (do_nil : typ -> T)
             (do_cons : typ -> expr typ func -> expr typ func -> T)
             (do_default : T)
  : Ptrns.tptrn (expr typ func) T :=
    Ptrns.pdefault
      (Ptrns.por
         (Ptrns.pmap (do_nil) (Ptrns.inj (ptrn_view LF (fptrnNil Ptrns.get))))
         (Ptrns.pmap (fun t_x_xs =>
                        let '(t,x,xs) := t_x_xs in
                        do_cons t x xs)
                     (Ptrns.app (Ptrns.app (Ptrns.inj (ptrn_view LF (fptrnCons Ptrns.get))) Ptrns.get) Ptrns.get)))
      do_default.

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
                                                (fun xs' => Monad.ret (match xs' with
                                                                       | None => None
                                                                       | Some xs' => Some (mkCons t x xs')
                                                                       end))))
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

  Existing Instance Injective_Succeeds_pmap.
  Existing Instance Injective_Succeeds_app.
  Existing Instance Injective_Succeeds_inj.
  Existing Instance Injective_Succeeds_get.
  Existing Instance Expr_expr.

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
        eD = AbsAppI.exprT_App e1D e2D.
  Proof using RSymOk_sym RTypeOk_typ Typ2Ok_func.
    intros.
    unfold exprD' in H. simpl in H.
    rewrite exprD'_App in H.
    simpl in H.
    forwardy.
    do 3 eexists; split; eauto.
    eapply H0.
    split; eauto.
    inv_all. eauto.
  Qed.

  (** TODO: This should go elsewhere **)
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
      exprD' tus tvs (mkCons t e1 e2) (typ1 t) = Some (AbsAppI.exprT_App (AbsAppI.exprT_App (exprT_pure (consR t)) e1D) e2D).
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

  Theorem exprT_App_cons
  : forall tus tvs (t : typ) (a : exprT tus tvs (typD t)) (b : exprT _ _ (typD (typ1 t)))
           us vs,
      castD (fun x => x) (typD t) (Typ0:=Typ0_term _ t) (a us vs) ::
            castD (fun x => x) (list (typD t)) (Typ0:=@Typ1_App _ _ list (typD t) Typ1_List (Typ0_term _ t)) (b us vs) =
      castD (fun x => x) (list (typD t)) (Typ0:=@Typ1_App _ _ list (typD t) Typ1_List (Typ0_term _ t))
            ((AbsAppI.exprT_App (AbsAppI.exprT_App (exprT_pure (consR t)) a) b) us vs).
  Proof.
    clear InContext_spec_check_equality.
    intros. unfold castD, AbsAppI.exprT_App, exprT_pure, consR, castR.
    simpl. unfold id, eq_rect_r, eq_rect, eq_rec.

    autorewrite_with_eq_rw.
    generalize (a us vs).
    generalize (b us vs).
    uip_all.
    generalize dependent (typD (typ1 t)).
    intros; subst.
    generalize dependent (typD (typ2 (typ1 t) (typ1 t))).
    intros; subst. simpl.
    generalize dependent (typD (typ2 t (typ2 (typ1 t) (typ1 t)))).
    intros; subst. reflexivity.
  Qed.

  (** TODO: this should be moved **)
  Ltac Rty_inv :=
    let rec find A B more none :=
        match A with
        | B => none tt
        | typ1 ?A' =>
          match B with
          | typ1 ?B' => find A' B' more none
          | _ => let r := constr:(A = B) in more r
          end
        | typ2 ?A1' ?A2' =>
          match B with
          | typ2 ?B1' ?B2' =>
            let m' x := find A2' B2' ltac:(fun y => let r := constr:(x /\ y) in more r) ltac:(fun _ => more x) in
            let n' x := find A2' B2' more none in
            find A1' B1' m' n'
          | _ => let r := constr:(A = B) in more r
          end
        | _ => let r := constr:(A = B) in more r
        end
    in
    let rec break_ands H P :=
        match P with
        | ?A /\ ?B =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [ H1 H2 ]; break_ands H1 A ; break_ands H2 B
        | _ => idtac
        end
    in
    let finish Hstart P :=
        let H := fresh in
        assert (H : P) by (inv_all; eauto) ;
          break_ands H P ; repeat progress subst ;
          try ( rewrite (UIP_refl Hstart) in * ) ; try clear Hstart
    in
    match goal with
    | H : Rty ?A ?B |- _ =>
      find A B ltac:(fun x => finish H x) ltac:(fun _ => fail)
    | H : @eq (option typ) (Some ?A) (Some ?B) |- _ =>
      find A B ltac:(fun x => finish H x) ltac:(fun _ => fail)
    end.



(*
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
                                     Permutation (castD (fun x => x) (typD t) (eD us vs) ::
                                                  castD (fun x => x) (list (typD t)) (lst'D us vs))
                                                 (castD (fun x => x) (list (typD t)) (lstD us vs)))
                           | None => None
                           end
                         end)
                      (remove e lst).
  Proof.
    Opaque exprD' Monad.bind Monad.ret.
    intros e lst t eD lstD He. revert lstD.
    eapply expr_strong_ind_no_case with (e:=lst); intros.
    rewrite remove_eta.
    unfold Ptrns.run_tptrn, list_cases.
    eapply Ptrns.pdefault_sound; eauto 100 with typeclass_instances.
    { red. red. red.
      intros. subst.
      red in H2.
      red in H2. erewrite H2. reflexivity.
      reflexivity. }
    { intros.
      eapply Succeeds_por in H1; try solve [ instantiate ; eauto 100 with typeclass_instances ].
      destruct H1; ptrnE.
      { subst. unfold ptret.
        eapply InContext_spec_ret; [ tauto | ].
        intros. split; auto.
        eexists; split; eauto.
        intros.
        eapply Pure_pctxD; eauto. }
      { unfold ptret.
        drive_exprD'.
        simpl in x3.
        Rty_inv.
        eapply InContext_spec_bind.
        { eapply InContext_spec_check_equality. }
        { clear InContext_spec_check_equality.
          destruct x.
          { clear H.
            eapply InContext_spec_ret; try solve [ simpl ; eauto ].
            simpl.
            intros. split; eauto.
            Transparent Monad.ret. simpl. Opaque Monad.ret.
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
              destruct (exprD' (getUVars ctx) (getVars ctx) e0 (typ1 t)) eqn:Heq.
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

*)

  Lemma match_option_same : forall {T U} (x : option T) (X : U),
      match x with
      | Some _ => X
      | None => X
      end = X.
  Proof. destruct x; reflexivity. Qed.

  Theorem remove_sound
  : forall e lst (t : typ),
      @InContext_spec typ (expr typ func)
                      ident _ _ _ _ _
                      (option (expr typ func))
                      (fun x => True) ctx
                      (fun (e' : option (expr typ func)) =>
                         match @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) e t
                             , @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst (typ1 t)
                         with
                         | Some eD , Some lstD =>
                           match e' with
                           | None => Some (fun _ => True)
                           | Some e' =>
                             match @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) e' (typ1 t) with
                             | Some lst'D =>
                               Some (fun env => let '(us,vs) := env in
                                                Permutation (castD (fun x => x) (typD t) (eD us vs) ::
                                                             castD (fun x => x) (list (typD t)) (lst'D us vs))
                                                            (castD (fun x => x) (list (typD t)) (lstD us vs)))
                             | None => None
                             end
                           end
                         | _ , _ => Some (fun _ => True)
                         end)
                      (remove e lst).
  Proof.
    Opaque exprD' Monad.bind Monad.ret.
    intros e lst t.
    eapply expr_strong_ind_no_case with (e:=lst); intros.
    rewrite remove_eta.
    unfold Ptrns.run_tptrn, list_cases.
    eapply Ptrns.pdefault_sound; eauto 100 with typeclass_instances.
    { red. red. red.
      intros. subst.
      do 2 red in H1. erewrite H1. reflexivity.
      reflexivity. }
    { intros.
      eapply Succeeds_por in H0; try solve [ instantiate ; eauto 100 with typeclass_instances ].
      destruct H0; ptrnE.
      { unfold ptret.
        eapply InContext_spec_ret; [ tauto | ].
        intros. split; auto.
        repeat rewrite match_option_same.
        eexists; split; eauto.
        eapply Pure_pctxD; eauto. }
      { unfold ptret.
        eapply InContext_spec_bind.
        { eapply InContext_spec_check_equality. }
        { clear InContext_spec_check_equality.
          destruct x.
          { clear H.
            eapply InContext_spec_ret; try solve [ simpl ; eauto ].
            simpl.
            intros. split; eauto.
            Transparent Monad.ret. simpl. Opaque Monad.ret.
            repeat match goal with
                   | |- context [ match ?X with _ => _ end ] =>
                     match X with
                     | match _ with _ => _ end => fail 1
                     | _ =>
                       let H := fresh in
                       destruct (X) eqn:H;
                         try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
                     end
                   | |- _ => progress drive_exprD'
                   end.
            simpl in x3. Rty_inv.
            rewrite H0 in *. rewrite H2 in *.
            inv_all; subst.
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
            repeat match goal with
                   | |- context [ match ?X with _ => _ end ] =>
                       let H := fresh in
                       destruct (X) eqn:H;
                         try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
                   | |- _ => progress drive_exprD'
                   end.
            forwardy; inv_all; subst.
            simpl in x4. Rty_inv.
            rewrite H6 in *.
            rewrite H7 in *. inv_all; subst.
            revert H0.
            Cases.rewrite_all_goal.
            intros; forwardy. inv_all; subst.
            erewrite exprD'_mkCons by eauto.
            eexists; split; eauto. simpl.
            intros.
            eapply Pure_pctxD; eauto.
            intros. inv_all.
            rewrite <- exprT_App_cons.
            rewrite <- exprT_App_cons.
            eapply perm_trans; [ eapply perm_swap | ].
            eapply perm_skip. eassumption. } } } }
    { unfold ptret.
      eapply InContext_spec_ret; try tauto.
      intros. split; auto.
      repeat rewrite match_option_same.
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

  Lemma cancel_eta : forall lst1 lst2,
      cancel lst1 lst2 =
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
  Proof.
    clear. intros.
    destruct lst1; reflexivity.
  Qed.

  Lemma match_option_push
    : forall {T U V} (x : option T) (f : T -> option U) (g : option U)
             f' (g' : V),
      match match x with
            | Some x => f x
            | None => g
            end
      with
      | Some y => f' y
      | None => g'
      end = match x with
            | Some x => match f x with
                        | Some y => f' y
                        | None => g'
                        end
            | None => match g with
                      | Some y => f' y
                      | None => g'
                      end
            end.
  Proof. clear. destruct x; reflexivity. Qed.

  Theorem cancel_sound
  : forall lst1 lst2 (t : typ),
      @InContext_spec typ (expr typ func)
                      ident _ _ _ _ _
                      _
                      (fun x => True) ctx
                      (fun (e' : expr typ func * expr typ func) =>
                         let '(lst1',lst2') := e' in
                         match @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst1 (typ1 t)
                             , @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst2 (typ1 t)
                             , @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst1' (typ1 t)
                             , @exprD' typ _ (expr typ func) _ (getUVars ctx) (getVars ctx) lst2' (typ1 t)
                         with
                         | Some lst1D , Some lst2D , Some lst1'D , Some lst2'D =>
                           Some (fun env =>
                                   let '(us,vs) := env in
                                   forall Z,
                                   Permutation (Z ++ castD (fun x => x) (list (typD t)) (lst1'D us vs))
                                               (castD (fun x => x) (list (typD t)) (lst2'D us vs)) ->
                                   Permutation (Z ++ castD (fun x => x) (list (typD t)) (lst1D us vs))
                                               (castD (fun x => x) (list (typD t)) (lst2D us vs)))
                         | None , _ , _ , _
                         | Some _ , None , _ , _ => Some (fun _ => True)
                         | Some _ , Some _ , None , _
                         | Some _ , Some _ , Some _ , None => None
                         end)
                      (cancel lst1 lst2).
  Proof.
    intro lst1.
    eapply expr_strong_ind_no_case with (e:=lst1); intros.
    rewrite cancel_eta.
    unfold Ptrns.run_tptrn, ptret, list_cases.
    eapply Ptrns.pdefault_sound; eauto 100 with typeclass_instances.
    { red. red. red.
      intros. subst.
      do 2 red in H1. erewrite H1. reflexivity.
      reflexivity. }
    { intros.
      eapply Succeeds_por in H0; try solve [ instantiate ; eauto 100 with typeclass_instances ].
      destruct H0; ptrnE.
      { eapply InContext_spec_ret; eauto.
        intros; split; auto.
        repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 let H := fresh in
                 destruct (X) eqn:H;
                   try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
               end.
        change_rewrite H1.
        eexists; split; eauto.
        intros; eapply Pure_pctxD; eauto. }
      { unfold ptret.
        eapply InContext_spec_bind.
        { eapply remove_sound; eauto. }
        instantiate (1:=t).
        destruct x.
        { eapply Proper_InContext_spec;
          [ | | reflexivity
          | eapply H; eauto using TransitiveClosure.LTFin, TransitiveClosure.LTStep,
                      acc_App_l, acc_App_r ].
          { compute. tauto. }
          { instantiate (1:=t).
            red. intros.
            destruct a.
            clear H InContext_spec_check_equality.
            repeat setoid_rewrite match_option_push.
            destruct (exprD' (getUVars ctx) (getVars ctx)
                             (App (App (Inj (f_insert (pCons t0))) e1) e0)
                             (typ1 t)) eqn:Heq.
            { drive_exprD'.
              simpl in x3. Rty_inv.
              Cases.rewrite_all_goal.
              destruct (exprD' (getUVars ctx) (getVars ctx) e (typ1 t)) eqn:Heq'.
              { destruct (exprD' (getUVars ctx) (getVars ctx) e2 (typ1 t)) eqn:Heq''; try constructor.
                destruct (exprD' (getUVars ctx) (getVars ctx) e3 (typ1 t)) eqn:Heq'''; try constructor.
                { destruct (exprD' (getUVars ctx) (getVars ctx) lst2 (typ1 t)) eqn:Heq''''.
                  { constructor. do 2 red. destruct a. simpl. intros.
                    eapply H in H4.
                    rewrite <- H3; clear H3.
                    rewrite <- exprT_App_cons.
                    rewrite <- H4.
                    rewrite Permutation_middle. reflexivity. }
                  { constructor; compute; tauto. } } }
              { destruct (exprD' (getUVars ctx) (getVars ctx) lst2 (typ1 t)); constructor;
                compute; tauto. } }
            { Lemma Roption_impl_tauto : forall {T} (R : T -> T -> Prop) a x,
                (forall y, R y x) ->
                Roption_impl R a (Some x).
              Proof.
                clear. destruct a; constructor; auto.
              Qed.
              destruct (exprD' (getUVars ctx) (getVars ctx) e1 t);
                try solve [ eapply Roption_impl_tauto ; compute; tauto ].
              destruct (exprD' (getUVars ctx) (getVars ctx) lst2 (typ1 t));
                try solve [ eapply Roption_impl_tauto ; compute; tauto ].
              destruct (exprD' (getUVars ctx) (getVars ctx) e (typ1 t));
                try solve [ eapply Roption_impl_tauto ; compute; tauto ]. } } }
        { eapply InContext_spec_bind.
          { eapply H; eauto using TransitiveClosure.LTFin, TransitiveClosure.LTStep,
                      acc_App_l, acc_App_r. }
          clear InContext_spec_check_equality H.
          instantiate (1:=t).
          destruct x.
          { eapply InContext_spec_ret; [ tauto | ].
            intros. split; [ tauto | ].
            destruct (exprD' (getUVars ctx) (getVars ctx)
                             (App (App (Inj (f_insert (pCons t0))) e1) e0)
                             (typ1 t)) eqn:Heq.
            { drive_exprD'.
              simpl in x3. Rty_inv.
              Cases.rewrite_all_goal.
              repeat match goal with
                     | |- context [ match ?X with _ => _ end ] =>
                       match X with
                       | match _ with _ => _ end => fail 1
                       | _ =>
                         let H := fresh in
                         destruct (X) eqn:H;
                           try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
                       end
                     | |- _ => progress drive_exprD'
                     end.
              erewrite exprD'_mkCons by eauto.
              eexists; split; eauto.
              intros; eapply Pure_pctxD; eauto.
              intros.
              rewrite <- exprT_App_cons in *.
              match goal with
              | |- Permutation (_ ++ ?X :: _) _ =>
                specialize (H6 (Z ++ X :: nil))
              end.
              rewrite app_ass in H6.
              simpl in H6. eapply H6 in H9.
              rewrite app_ass in H9. simpl in H9.
              assumption. }
            { repeat rewrite match_option_same.
              repeat match goal with
                     | |- context [ match ?X with _ => _ end ] =>
                       match X with
                       | match _ with _ => _ end => fail 1
                       | _ =>
                         let H := fresh in
                         destruct (X) eqn:H;
                           try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
                       end
                     | |- _ => progress drive_exprD'
                     end.
              match goal with
              | |- exists x , match ?X with _ => _ end = _ /\ _ =>
                destruct X; eexists; split; eauto; eapply Pure_pctxD; eauto
              end. } } } } }
    { eapply InContext_spec_ret; [ tauto | ].
      intros. split; eauto.
      clear H InContext_spec_check_equality.
      repeat match goal with
             | |- context [ match ?X with _ => _ end ] =>
               match X with
               | match _ with _ => _ end => fail 1
               | _ =>
                 let H := fresh in
                 destruct (X) eqn:H;
                   try solve [ eexists; split; eauto; eapply Pure_pctxD; eauto ]; [ ]
               end
             | |- _ => progress drive_exprD'
             end.
      destruct (exprD' (getUVars ctx) (getVars ctx) lst2 (typ1 t)).
      { eexists; split; eauto; eapply Pure_pctxD; eauto. }
      { eexists; split; eauto; eapply Pure_pctxD; eauto. } }
  Time Qed.

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