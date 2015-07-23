Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {RSym_func : RSym func}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.

  Let tyArr := @typ2 _ _ _ Typ2_Fun.

  Definition app {T U} (f : ptrn (expr typ func) T) (g : ptrn (expr typ func) U)
  : ptrn (expr typ func) (T * U) :=
    fun e _T good bad =>
      match e with
      | App l r =>
        Mbind (Mrebuild (fun x => App x r) (f l))
              (fun x => Mmap (fun y => (x,y)) (Mrebuild (App l) (g r))) good bad
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end%type.

  Definition var : ptrn (expr typ func) nat :=
    fun e _T good bad =>
      match e with
      | Var v => good v
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Inj a => bad (Inj a)
      end.

  Definition uvar : ptrn (expr typ func) nat :=
    fun e _T good bad =>
      match e with
      | UVar v => good v
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end.

  Definition inj {T} (p : ptrn func T) : ptrn (expr typ func) T :=
    fun e _T good bad =>
      match e with
      | UVar v => bad (UVar v)
      | App a b => bad (App a b)
      | Abs a b => bad (Abs a b)
      | Var a => bad (Var a)
      | Inj a => p a _T good (fun x => bad (Inj a))
      end.

  Definition abs {T U} (pt : ptrn typ U) (p : U -> ptrn (expr typ func) T)
  : ptrn (expr typ func) T :=
    fun e _T good bad =>
      match e with
      | Abs t e' => pt t _T (fun v => p v e' _T good (fun x => bad (Abs t x)))
                       (fun t => bad (Abs t e'))
      | UVar v => bad (UVar v)
      | App a b => bad (App a b)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end%type.

  Fixpoint exact_nat (n : nat) : ptrn nat unit :=
    fun n' _T good bad =>
      match n , n' with
      | 0 , 0 => good tt
      | S n , S n' => @exact_nat n n' _T good (fun x => bad (S x))
      | _ , 0 => bad 0
      | _ , S n => bad (S n)
      end.

  Definition exact_func (i1 : func) : ptrn func unit :=
    fun i2 _T good bad =>
    match sym_eqb i1 i2 with
      | Some true => good tt
      | _ => bad i2
    end.

  Fixpoint exact (e : expr typ func) {struct e} : ptrn (expr typ func) unit :=
    fun e' _T good bad =>
      match e , e' with
      | App a b , App c d =>
        @exact a c _T
               (fun _ => @exact b d _T good (fun x => bad (App c x)))
               (fun x => bad (App x d))
      | Abs t1 e1 , Abs t2 e2 =>
        match type_cast t1 t2 with
        | Some _ => @exact e1 e2 _T good (fun x => bad (Abs t2 x))
        | _ => bad (Abs t2 e2)
        end
      | Var v1 , Var v2 =>
        exact_nat v1 v2 good (fun v => bad (Var v))
      | UVar v1 , UVar v2 =>
        exact_nat v1 v2 good (fun v => bad (UVar v))
      | Inj i1 , Inj i2 => exact_func i1 i2 good (fun v => bad (Inj v))
      | _ , App a b => bad (App a b)
      | _ , Abs a b => bad (Abs a b)
      | _ , Inj a => bad (Inj a)
      | _ , Var a => bad (Var a)
      | _ , UVar a => bad (UVar a)
      end.

  Require Import ExtLib.Relations.TransitiveClosure.

  Theorem Succeeds_var : forall v e,
      Succeeds e var v ->
      e = Var v.
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H bool (fun _ => true) (fun _ => false)); inversion H ].
    red in H. simpl in H.
    eapply H. exact (fun x => x).
  Qed.

  Theorem Succeeds_uvar : forall v e,
      Succeeds e uvar v ->
      e = UVar v.
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H bool (fun _ => true) (fun _ => false)); inversion H ].
    red in H. simpl in H.
    eapply H. exact (fun x => x).
  Qed.

  Theorem Succeeds_inj : forall {T} p e (res : T),
      ptrn_ok p ->
      Succeeds e (inj p) res ->
      exists f, e = Inj f /\ Succeeds f p res.
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H0 bool (fun _ => true) (fun _ => false)); inversion H0 ].
    eexists; split; eauto. red; intros.
    red in H0. simpl in H0.
    destruct (H f) as [ [ ? ? ] | ? ].
    { red in H1.  setoid_rewrite H1 in H0.
      rewrite H1. eapply H0. eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      specialize (H0 _ (fun _ => true) (fun _ => false)). inversion H0. }
  Qed.

  Theorem Succeeds_abs : forall {T U} a b e res
      (Hpoka : ptrn_ok a) (Hpokb : forall x, ptrn_ok (b x)),
      Succeeds e (abs a b) res ->
      exists l r ra, e = Abs l r /\
        Succeeds (T:=T) l a ra /\
        Succeeds (T:=U) r (b ra) res.
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H _ (fun _ => true) (fun _ => false)); inversion H ].
    { red in H.
      destruct (Hpoka t) as [ [ ? ? ] | ? ].
      { red in H0.
        setoid_rewrite H0 in H.
        destruct (Hpokb x e) as [ [ ? ? ] | ? ].
        { red in H1. setoid_rewrite H1 in H.
          do 3 eexists; split; eauto.
          split; eauto.
          specialize (H _ (fun x => x)). simpl in H. destruct H; eauto. }
        { exfalso.
          red in H1.
          setoid_rewrite H1 in H.
          specialize (H _ (fun _ => true) (fun _ => false)); inversion H. } }
      { simpl in H.
        red in H0.
        setoid_rewrite H0 in H.
        specialize (H _ (fun _ => true) (fun _ => false)); inversion H. } }
  Qed.

  Theorem Succeeds_app : forall {T U} a b e res
      (Hpoka : ptrn_ok a) (Hpokb : ptrn_ok b),
      Succeeds e (app a b) res ->
      exists l r, e = App l r /\
        Succeeds (T:=T) l a (fst res) /\
        Succeeds (T:=U) r b (snd res).
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H bool (fun _ => true) (fun _ => false)); inversion H ].
    { do 2 eexists; split; eauto.
      destruct (Hpoka e1).
      { destruct H0.
        { destruct (Hpokb e2).
          { destruct H1.
            red in H. red in H0. red in H1.
            simpl in H.
            setoid_rewrite H0 in H.
            setoid_rewrite H1 in H.
            split; eauto; red.
            { intros.
              rewrite H0.
              eapply (H _ (fun x => good (fst x)) bad). }
            { intros.
              rewrite H1.
              eapply (H _ (fun x => good (snd x)) bad). } }
          { exfalso.
            red in H, H0, H1.
            setoid_rewrite H0 in H.
            setoid_rewrite H1 in H.
            specialize (H _ (fun _ => true) (fun _ => false)).
            inversion H. } } }
      { exfalso.
        red in H, H0.
        setoid_rewrite H0 in H.
        specialize (H _ (fun _ => true) (fun _ => false)).
        inversion H. } }
  Qed.

  Lemma run_tptrn_id_sound (tus tvs : tenv typ) (t : typ) (p : ptrn (expr typ func) (expr typ func))
        (e : expr typ func) (val : ExprI.exprT tus tvs (typD t))
        (H : exprD' tus tvs t e =Some val)
        (HSucceeds : forall e', Succeeds e p e' ->
                                exprD' tus tvs t e' = Some val) :
    exprD' tus tvs t (run_tptrn (pdefault_id p) e) = Some val.
  Proof.
    unfold run_tptrn, pdefault_id.
    eapply pdefault_sound; eauto.
  Abort. (** Not Provable *)

  Lemma app_sound {A B : Type} {tus tvs t e res val}
        {p1 : ptrn (expr typ func) A} {p2 : ptrn (expr typ func) B}
        (H : ExprDsimul.ExprDenote.exprD' tus tvs t e = Some val)
        (HSucceeds : Succeeds e (app p1 p2) res)
        (Hp1 : ptrn_ok p1) (Hp2 : ptrn_ok p2)
        {P : exprT tus tvs (typD t) -> Prop}
        (Hstep : forall l r tr vl vr,
                   Succeeds l p1 (fst res) -> Succeeds r p2 (snd res) ->
                   ExprDsimul.ExprDenote.exprD' tus tvs (tyArr tr t) l = Some vl ->
                   ExprDsimul.ExprDenote.exprD' tus tvs tr r = Some vr ->
                   P (exprT_App vl vr)) :
    P val.
  Proof.
    apply Succeeds_app in HSucceeds; [|assumption|assumption].
    destruct HSucceeds as [l [r [Heq [HS1 HS2]]]]; subst.
    autorewrite with exprD_rw in H.
    unfold Monad.bind in H; simpl in H.
    forward; inv_all; subst.
    eapply Hstep; try eassumption.
  Qed.

  Lemma inj_sound {A : Type} {tus tvs t e res val}
        {p : ptrn func A}
        (H : ExprDsimul.ExprDenote.exprD' tus tvs t e = Some val)
        (HSucceeds : Succeeds e (inj p) res)
        (Hp1 : ptrn_ok p)
        {P : exprT tus tvs (typD t) -> Prop}
        (Hstep : forall f ve,
                   Succeeds f p res ->
                   symAs f t = Some ve ->
                   P (fun _ _ => ve)) :
    P val.
  Proof.
    apply Succeeds_inj in HSucceeds; [|assumption].
    destruct HSucceeds as [f [Heq HSucceeds]]; subst.
    autorewrite with exprD_rw in H.
    unfold Monad.bind in H; simpl in H.
    forward; inv_all; subst.
    eapply Hstep; try eassumption.
  Qed.


(*
  Require Import MirrorCore.Lambda.AppN.

  Fixpoint appN {T} {Ts : list Type} (f : ptrn (expr typ func) T)
           (args : hlist (ptrn (expr typ func)) Ts)
  : ptrn (expr typ func) (T * hlist (fun x => x) Ts) :=
    match args in hlist _ Ts
          return ptrn (expr typ func) (T * hlist (fun x => x) Ts)
    with
    | Hnil => pmap (fun x => (x,Hnil)) f
    | Hcons p ps => pmap (fun a => let '(a,b,c) := a in
                                   (a, Hcons b c)) (appN (app f p) ps)
    end.

  Inductive Forall_hlist {T : Type} {F : T -> Type} (P : forall x, F x -> Prop)
  : forall {Ts : list T}, hlist F Ts -> Prop :=
  | Forall_hlist_nil : Forall_hlist P Hnil
  | Forall_hlist_cons : forall t Ts x xs,
      @P t x ->
      Forall_hlist P xs ->
      Forall_hlist (Ts:=t::Ts) P (Hcons x xs).

  Inductive Forall3_hlist {T : Type} {F : Type} {G : T -> Type} {H : T -> Type}
            (P : forall x, F -> G x -> H x -> Prop)
  : forall {Ts : list T}, list F -> hlist G Ts -> hlist H Ts -> Prop :=
  | Forall3_hlist_nil : Forall3_hlist P nil Hnil Hnil
  | Forall3_hlist_cons : forall t Ts x xs y ys z zs,
      @P t x y z ->
      Forall3_hlist P xs ys zs ->
      Forall3_hlist (Ts:=t::Ts) P (x :: xs) (Hcons y ys) (Hcons z zs).
*)

  Global Instance ptrn_ok_app
  : forall {T U} (p1 : ptrn _ T) (p2 : ptrn _ U),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (app p1 p2).
  Proof.
    clear; compute.
    destruct x; eauto.
    destruct (H x1) as [ [ ? ? ] | ? ]; setoid_rewrite H1; eauto.
    destruct (H0 x2) as [ [ ? ? ] | ? ]; setoid_rewrite H2; eauto.
  Qed.

  Global Instance ptrn_ok_inj
  : forall {T} (p1 : ptrn _ T), ptrn_ok p1 -> ptrn_ok (inj p1).
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
    destruct (H f) as [ [ ? ? ] | ? ]; setoid_rewrite H0; eauto.
  Qed.

  Global Instance ptrn_ok_var : ptrn_ok var.
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
  Qed.

  Global Instance ptrn_ok_uvar : ptrn_ok uvar.
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
  Qed.

  Global Instance ptrn_ok_abs
  : forall {T U} (p1 : ptrn _ T) (p2 : _ -> ptrn _ U),
      ptrn_ok p1 -> (forall x, ptrn_ok (p2 x)) -> ptrn_ok (abs p1 p2).
  Proof.
    clear; compute; destruct x; eauto.
    destruct (H t) as [ [ ? ? ] | ? ] ; setoid_rewrite H1; eauto.
    destruct (H0 x0 x) as [ [ ? ? ] | ? ] ; setoid_rewrite H2; eauto.
  Qed.

(*
  Instance ptrn_ok_appN : forall {Ts} (ps : hlist _ Ts),
      Forall_hlist (fun _ x => ptrn_ok x) ps ->
      forall T (p : ptrn _ T), ptrn_ok p ->
      ptrn_ok (appN p ps).
  Proof.
    induction 1; simpl; eauto with typeclass_instances.
  Qed.

  Theorem Succeeds_appN : forall {Ts} ps,
      Forall_hlist (fun _ x => ptrn_ok x) ps ->
      forall T val e (p : ptrn _ T), ptrn_ok p ->
      Succeeds e (appN p ps) val ->
      exists f es fv esv,
           e = apps f es
        /\ Succeeds f p fv
        /\ @Forall3_hlist _ _ _ _ (fun T e p v => Succeeds e p v) Ts es ps esv.
  Proof.
    induction 1.
    { simpl. intros.
      eapply Succeeds_pmap in H0; eauto.
      destruct H0 as [ ? [ ? ? ] ].
      subst.
      exists e; exists nil; exists x; exists Hnil.
      simpl. split; eauto.
      split; eauto.
      constructor. }
    { simpl. intros.
      eapply Succeeds_pmap in H2; eauto with typeclass_instances.
      forward_reason.
      eapply IHForall_hlist in H2; eauto with typeclass_instances.
      subst.
      forward_reason.
      subst.
      eapply Succeeds_app in H3; eauto with typeclass_instances.
      forward_reason. subst.
      do 4 eexists.
      split.
      { change (apps (App x5 x6) x2) with (apps x5 (x6 :: x2)). reflexivity. }
      split; eauto.
      constructor; eauto. }
  Qed.
*)

  Instance Injective_Succeeds_app {T U} p1 p2 x res : ptrn_ok p1 -> ptrn_ok p2 ->  Injective (Succeeds x (app p1 p2) res) :=
  { result := _
  ; injection := @Succeeds_app T U _ _ _ _ _ _ }.

  Instance Injective_Succeeds_inj {X} p x res : ptrn_ok p -> Injective (Succeeds x (inj p) res) :=
  { result := _
  ; injection := @Succeeds_inj X _ _ _ _ }.

  Instance Injective_Succeeds_var x res : Injective (Succeeds x var res) :=
  { result := _
  ; injection := @Succeeds_var _ _ }.

  Instance Injective_Succeeds_uvar x res : Injective (Succeeds x uvar res) :=
  { result := _
  ; injection := @Succeeds_uvar _ _ }.

  Instance Injective_Succeeds_abs {T U} x res pt pe
  : ptrn_ok pt -> (forall x, ptrn_ok (pe x)) ->
    Injective (Succeeds x (@abs T U pt pe) res) :=
  { result := _
  ; injection := @Succeeds_abs _ _ _ _ _ _ _ _ }.

  Global Instance app_SucceedsE {T U : Type} {e : expr typ func} 
         {p : ptrn (expr typ func) T} {q : ptrn (expr typ func) U} {res : T * U} 
         {pok_p : ptrn_ok p} {pok_q : ptrn_ok q} :
    SucceedsE e (app p q) res := {
      s_result := exists l r, e = App l r /\ Succeeds l p (fst res) /\ Succeeds r q (snd res);
      s_elim := Succeeds_app pok_p pok_q
    }.

  Global Instance inj_SucceedsE {T : Type} {e : expr typ func} 
         {p : ptrn func T}  {res : T} {pok_p : ptrn_ok p} :
    SucceedsE e (inj p) res := {
      s_result := exists f, e = Inj f /\ Succeeds f p res;
      s_elim := Succeeds_inj pok_p
    }.

  Definition castD F U {T : Typ0 _ U} (val : F (typD (typ0 (F:=U)))) : F U :=
    match @typ0_cast typ _ _ T in _ = x return F x with
      | eq_refl => val
    end.

  Definition castR F U {T : Typ0 _ U} (val : F U) : F (typD (typ0 (F:=U))) :=
    match eq_sym (@typ0_cast typ _ _ T) in _ = x return F x with
    | eq_refl => val
    end.

  Implicit Arguments castD [[T]].
  Implicit Arguments castR [[T]].

  Global Existing Instance Typ2_App.
  Global Existing Instance Typ1_App.
  Global Existing Instance Typ0_term.
  Global Existing Instance MirrorCore.ExprI.Applicative_exprT.

  Require Import MirrorCore.Util.Compat.

  Theorem exprT_App_Fun tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)
          (e1 : exprT tus tvs (Fun T U))
          (e2 : exprT tus tvs T) :
    @exprT_App typ _ Typ2_Fun tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _) 
               (@castR (exprT tus tvs) _ _ e1)
               (@castR (exprT tus tvs) _ _ e2) =
    @castR (exprT tus tvs) U U0 (Applicative.ap e1 e2).
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
    destruct (eq_sym e0).
    destruct (eq_sym e). simpl. reflexivity.
  Qed.

  Theorem exprT_App_Fun' tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)  P
          (e1 : exprT tus tvs (Fun T U))
          (e2 : exprT tus tvs T) 
          (Hres : P (@castR (exprT tus tvs) U U0 (Applicative.ap e1 e2))) :
    P (@exprT_App typ _ Typ2_Fun tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _) (@castR (exprT tus tvs) _ _ e1) (@castR (exprT tus tvs) _ _ e2)).
  Proof.
    subst. rewrite exprT_App_Fun. assumption.
  Qed.

  Lemma exprT_App_castR_pure {A : Type} {T0 : Typ0 RType_typD A} tus tvs (f : exprT tus tvs A) :
    (fun us vs => castR id A (f us vs)) = 
    (castR (exprT tus tvs) A f).
  Proof.
    unfold castR, eq_sym, id; simpl.
    generalize dependent (typ0_cast (F := A)).
    intros. autorewrite_with_eq_rw.
    reflexivity.
  Qed.

End setoid.

Implicit Arguments castD [[typ] [RType_typD] [T]].
Implicit Arguments castR [[typ] [RType_typD] [T]].

Ltac destruct_prod :=
  match goal with 
    | p : ?A * ?B |- _ => destruct p; destruct_prod
    | _ => idtac
  end.

Ltac force_apply lem :=
  let L := fresh "L" in 
  pose proof lem as L; apply L; clear L.

Ltac exprT_App_red :=
  match goal with
    | |- context [castR id _ _] => rewrite exprT_App_castR_pure
    | |- context [@exprT_App ?typ _ _ ?tus ?tvs _ _ (castR _ (Fun ?t1 ?t2) _) ?v] => 
      first [
          force_apply (@exprT_App_Fun' typ _ _ tus tvs t1 t2 _ _) |
          replace v with (castR (exprT tus tvs) t1 v) by reflexivity;
            force_apply (@exprT_App_Fun' typ _ _ tus tvs t1 t2 _ _)
        ]
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

Ltac ptrnE :=
  ptrn_elim; destruct_prod; simpl in *; subst; inv_all; repeat subst;
  repeat symAsE.


