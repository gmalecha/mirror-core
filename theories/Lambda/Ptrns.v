Require Import ExtLib.Tactics.
Require Import MirrorCore.Views.Ptrns.
Require Import MirrorCore.Views.FuncView. (* Ghost dependency *)
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.
Set Universe Polymorphism.

Section setoid.
  Context {typ : Set}.
  Context {func : Set}.
  Context {RType_typD : RType typ}.
  Context {RSym_func : RSym func}.
  Context {Typ2_Fun : Typ2 RType_typD RFun}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.

  Let tyArr := @typ2 _ _ _ Typ2_Fun.

  Definition app@{T U z} {T U : Type@{T}}
             (f : ptrn@{Set T U z} (expr typ func) T) (g : ptrn@{Set T U z} (expr typ func) U)
  : ptrn@{Set T U z} (expr typ func) (T * U) :=
    fun e _T good bad =>
      match e with
      | App l r =>
        (* Mbind@{Set T U z} (Mrebuild (fun x => App x r) (f l))
              (fun x => Mmap (fun y => (x,y)) (Mrebuild (App l) (g r))) good bad *)
        f l _ (fun l' => g r _ (fun r' => good (l', r')) (fun y => bad (App l y))) (fun x => bad (App x r))
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end.

  Definition appr@{T U z} {T U : Type@{T}} (f : ptrn@{Set T U z} (expr typ func) (U -> T))
    (g : ptrn@{Set T U z} (expr typ func) U) : ptrn@{Set T U z} (expr typ func) T :=
    fun (e : expr typ func)
        (_T : Type@{T}) (good : T -> _T) (bad : expr typ func -> _T) =>
      match e with
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      | App l r =>
        g r _ (fun r' => f l _ (fun l' => good (l' r')) (fun l' => bad (App l' r))) (fun r' => bad (App l r'))
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      end.

  Definition appl@{T U z} {T U : Type@{T}}
        (f : ptrn@{Set T U z} (expr typ func) T)
        (g : ptrn@{Set T U z} (expr typ func) (T -> U)) : ptrn@{Set T U z} (expr typ func) U :=
    fun e (_T : Type@{T}) good bad =>
      match e with
      | ExprCore.Var a => bad (ExprCore.Var a)
      | Inj a => bad (Inj a)
      | App l r =>
        f l _ (fun l' => g r _ (fun r' => good (r' l')) (fun r' => bad (App l r'))) (fun l' => bad (App l' r))         | Abs a b => bad (Abs a b)
      | ExprCore.UVar a => bad (ExprCore.UVar a)
      end.

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
      end.

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

  Set Printing Universes.

  Theorem Succeeds_inj : forall {T : Type} (p : ptrn func T) e (res : T),
      ptrn_ok p ->
      Succeeds e (inj p) res ->
      exists f, e = Inj f /\ Succeeds f p res.
  Proof.
    clear. intros.
    destruct e;
      try solve [ specialize (H0 bool (fun _ => true) (fun _ => false)); exfalso; discriminate H0 ].
    eexists; split; eauto. red; intros.
    red in H0. simpl in H0.
    destruct (H f) as [ [ ? ? ] | ? ].
    { red in H1. setoid_rewrite H1 in H0.
      rewrite H1. eapply H0. eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      specialize (H0 _ (fun _ => true) (fun _ => false)).
      exfalso. clear - H0. discriminate H0. }
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

  Lemma app_sound {A B : Type} {tus tvs t e res val}
        {p1 : ptrn (expr typ func) A} {p2 : ptrn (expr typ func) B}
        (H : ExprDsimul.ExprDenote.lambda_exprD tus tvs t e = Some val)
        (HSucceeds : Succeeds e (app p1 p2) res)
        (Hp1 : ptrn_ok p1) (Hp2 : ptrn_ok p2)
        {P : exprT tus tvs (typD t) -> Prop}
        (Hstep : forall l r tr vl vr,
                   Succeeds l p1 (fst res) -> Succeeds r p2 (snd res) ->
                   ExprDsimul.ExprDenote.lambda_exprD tus tvs (tyArr tr t) l = Some vl ->
                   ExprDsimul.ExprDenote.lambda_exprD tus tvs tr r = Some vr ->
                   P (AbsAppI.exprT_App vl vr)) :
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
        (H : ExprDsimul.ExprDenote.lambda_exprD tus tvs t e = Some val)
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

  Global Instance ptrn_ok_app
  : forall {T U} (p1 : ptrn _ T) (p2 : ptrn _ U),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (app p1 p2).
  Proof.
    clear; compute.
    destruct x; eauto.
    destruct (H x1) as [ [ ? ? ] | ? ]; setoid_rewrite H1; eauto.
    destruct (H0 x2) as [ [ ? ? ] | ? ]; setoid_rewrite H2; eauto.
  Qed.

  Global Instance ptrn_ok_appl
  : forall {T U : Type}
           (f : ptrn (expr typ func) T)
           (g : ptrn (expr typ func) (T -> U)),
      ptrn_ok f -> ptrn_ok g -> ptrn_ok (appl f g).
  Proof using.
    clear; compute.
    destruct x; eauto.
    destruct (H x1) as [ [ ? ? ] | ? ]; setoid_rewrite H1; eauto.
    destruct (H0 x2) as [ [ ? ? ] | ? ]; setoid_rewrite H2; eauto.
  Qed.

  Global Instance ptrn_ok_appr
  : forall {T U}
           (f : ptrn (expr typ func) (T -> U))
           (g : ptrn (expr typ func) T),
      ptrn_ok f -> ptrn_ok g -> ptrn_ok (appr f g).
  Proof using.
    clear; compute.
    destruct x; eauto.
    destruct (H x1) as [ [ ? ? ] | ? ]; destruct (H0 x2) as [ [ ? ? ] | ? ];
    setoid_rewrite H2; try setoid_rewrite H1; eauto.
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

  Global Instance Injective_Succeeds_app {T U} p1 p2 x res
  : ptrn_ok p1 -> ptrn_ok p2 ->  Injective (Succeeds x (app p1 p2) res) :=
  { result := _
  ; injection := @Succeeds_app T U _ _ _ _ _ _ }.

  Global Instance Injective_Succeeds_inj {X} p x res
  : ptrn_ok p -> Injective (Succeeds x (inj p) res) :=
  { result := _
  ; injection := @Succeeds_inj X _ _ _ _ }.

  Global Instance Injective_Succeeds_var x res
  : Injective (Succeeds x var res) :=
  { result := _
  ; injection := @Succeeds_var _ _ }.

  Global Instance Injective_Succeeds_uvar x res
  : Injective (Succeeds x uvar res) :=
  { result := _
  ; injection := @Succeeds_uvar _ _ }.

  Global Instance Injective_Succeeds_abs {T U} x res pt pe
  : ptrn_ok pt -> (forall x, ptrn_ok (pe x)) ->
    Injective (Succeeds x (@abs T U pt pe) res) :=
  { result := _
  ; injection := @Succeeds_abs _ _ _ _ _ _ _ _ }.

  Global Instance app_SucceedsE {T U : Type} {e : expr typ func}
         {p : ptrn (expr typ func) T} {q : ptrn (expr typ func) U} {res : T * U}
         {pok_p : ptrn_ok p} {pok_q : ptrn_ok q}
  : SucceedsE e (app p q) res :=
  { s_result := exists l r, e = App l r /\ Succeeds l p (fst res) /\ Succeeds r q (snd res)
  ; s_elim := Succeeds_app pok_p pok_q
  }.

  Global Instance abs_SucceedsE {T U : Type} {e : expr typ func}
         {p : ptrn typ T} {q : T -> ptrn (expr typ func) U} {res : U}
         {pok_p : ptrn_ok p} {pok_q : forall x, ptrn_ok (q x)}
  : SucceedsE e (abs p q) res :=
  { s_result := _
  ; s_elim := Succeeds_abs pok_p pok_q
  }.

  Global Instance inj_SucceedsE {T : Type} {e : expr typ func}
         {p : ptrn func T}  {res : T} {pok_p : ptrn_ok p}
  : SucceedsE e (inj p) res :=
  { s_result := exists f, e = Inj f /\ Succeeds f p res
  ; s_elim := Succeeds_inj pok_p
  }.

  Lemma Succeeds_appr
  : forall (T U : Type)
           (a : ptrn (expr typ func) (T -> U)) (b : ptrn (expr typ func) T)
           (e : expr typ func) (res : U),
      ptrn_ok a ->
      ptrn_ok b ->
      Succeeds e (appr a b) res ->
      exists resL resR, exists l r : expr typ func,
          e = App l r /\ Succeeds l a resL /\ Succeeds r b resR /\
          res = resL resR.
  Proof using.
    unfold appr.
    intros.
    red in H1.
    destruct e;
      try solve [ specialize (H1 _ (fun _ => true) (fun _ => false));
                  inversion H1 ].
    compute in H1.
    specialize (H0 e2).
    specialize (H e1).
    destruct H0.
    { destruct H0. setoid_rewrite H0 in H1.
      destruct H.
      { destruct H. setoid_rewrite H in H1.
        do 4 eexists. split; [ reflexivity | ]. split; eauto.
        split; eauto. symmetry; eapply (H1 _ (fun x => x) (fun _ => res)). }
      { setoid_rewrite H in H1.
        specialize (H1 _ (fun _ => true) (fun _ => false)); inversion H1. } }
    { setoid_rewrite H0 in H1.
      specialize (H1 _ (fun _ => true) (fun _ => false)); inversion H1. }
  Qed.

  Lemma Succeeds_appl
    : forall (T U : Type)
             (a : ptrn (expr typ func) (T -> U)) (b : ptrn (expr typ func) T)
             (e : expr typ func) (res : U),
      ptrn_ok a ->
      ptrn_ok b ->
      Succeeds e (appl b a) res ->
      exists resL resR, exists l r : expr typ func,
          e = App l r /\ Succeeds r a resL /\ Succeeds l b resR /\
          res = resL resR.
  Proof using.
    unfold appl.
    intros.
    red in H1.
    destruct e;
      try solve [ specialize (H1 _ (fun _ => true) (fun _ => false));
                  inversion H1 ].
    compute in H1.
    specialize (H0 e1).
    specialize (H e2).
    destruct H0.
    { destruct H0. setoid_rewrite H0 in H1.
      destruct H.
      { destruct H. setoid_rewrite H in H1.
        do 4 eexists. split; [ reflexivity | ]. split; eauto.
        split; eauto. symmetry; eapply (H1 _ (fun x => x) (fun _ => res)). }
      { setoid_rewrite H in H1.
        specialize (H1 _ (fun _ => true) (fun _ => false)); inversion H1. } }
    { setoid_rewrite H0 in H1.
      specialize (H1 _ (fun _ => true) (fun _ => false)); inversion H1. }
  Qed.

  Global Instance SucceedsE_appl (T U : Type)
           (a : ptrn (expr typ func) (T -> U)) (b : ptrn (expr typ func) T)
           (e : expr typ func) (res : U) (pok_a : ptrn_ok a) (pok_b : ptrn_ok b)
  : SucceedsE e (appl b a) res :=
  { s_result := exists resL resR, exists l r : expr typ func,
          e = App l r /\ Succeeds r a resL /\ Succeeds l b resR /\
          res = resL resR
  ; s_elim := @Succeeds_appl T U a b e res _ _ }.

  Global Instance SucceedsE_appr (T U : Type)
           (a : ptrn (expr typ func) (T -> U)) (b : ptrn (expr typ func) T)
           (e : expr typ func) (res : U) (pok_a : ptrn_ok a) (pok_b : ptrn_ok b)
  : SucceedsE e (appr a b) res :=
  { s_result := _
  ; s_elim := @Succeeds_appr T U a b e res _ _ }.

  Global Existing Instance Typ2_App.
  Global Existing Instance Typ1_App.
  Global Existing Instance Typ0_term.
  Global Existing Instance MirrorCore.ExprI.Applicative_exprT.

  Require Import MirrorCore.Util.Compat.
  Require Import Coq.Classes.Morphisms.

  Theorem exprT_App_castR tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)
          (e1 : exprT tus tvs (RFun T U))
          (e2 : exprT tus tvs (typD (@typ0 _ _ T _))) P
          (H : P (castR (exprT tus tvs) U (Applicative.ap e1 (castD (exprT tus tvs) T e2)))) :
    P (@AbsAppI.exprT_App typ _ Typ2_Fun tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _)
                  (castR (exprT tus tvs) _ e1) e2).
  Proof.
    revert H. clear.
    unfold AbsAppI.exprT_App; simpl.
    repeat (unfold castR, castD; simpl).
    autorewrite_with_eq_rw.
    generalize dependent (typ0_cast (F:=T)).
    generalize dependent (typ0_cast (F:=U)).
    generalize dependent (typ0 (F:=U)).
    generalize dependent (typ0 (F:=T)).
    intros. revert H. destruct e. destruct e0. simpl.
    generalize dependent (typ2_cast t t0).
    generalize dependent (typD (typ2 t t0)).
    do 2 intro; subst.
    simpl. exact (fun x => x).
  Qed.

  Theorem exprT_App_castR2 tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)
          (e1 : exprT tus tvs (typD (tyArr (@typ0 _ _ T _) (@typ0 _ _ U _))))
          (e2 : exprT tus tvs T) (P : _ -> Prop)
          (H : P (castR (exprT tus tvs) U (Applicative.ap (castD (exprT tus tvs) (RFun T U) e1) e2)))
  : P (@AbsAppI.exprT_App typ _ Typ2_Fun tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _)
                          e1 (castR (exprT tus tvs) _ e2)).
  Proof.
    revert H. clear.
    unfold AbsAppI.exprT_App; simpl.
    repeat (unfold castR, castD; simpl).
    generalize dependent (typ0_cast (F:=T)).
    generalize dependent (typ0_cast (F:=U)).
    generalize dependent (typ0 (F:=T)).
    generalize dependent (typ0 (F:=U)).
    intros. revert H. destruct e; destruct e0; simpl.
    generalize dependent (typ2_cast t0 t).
    intro.
    rewrite @Eq.eq_sym_eq.
    generalize (eq_sym e).
    clear. unfold tyArr in *.
    generalize dependent (@typD typ RType_typD (@typ2 typ RType_typD RFun Typ2_Fun t0 t)).
    intros. destruct e. assumption.
  Qed.

 Theorem exprT_App_castD tus tvs T U (T0 : Typ0 _ T) (U0 : Typ0 _ U)
          (e1 : exprT tus tvs (typD (@typ2 _ _ RFun _ (@typ0 _ _ T _) (@typ0 _ _ U _))))
          (e2 : exprT tus tvs (typD (@typ0 _ _ T _))) P
          (H : P (Applicative.ap (castD (exprT tus tvs) (RFun T U) e1)
                                 (castD (exprT tus tvs) T e2))) :
   P (castD (exprT tus tvs) U
            (@AbsAppI.exprT_App typ _ Typ2_Fun tus tvs (@typ0 _ _ T _) (@typ0 _ _ U _)
                        e1 e2)).
  Proof.
    revert H. clear.
    unfold AbsAppI.exprT_App; simpl.
    repeat (unfold castR, castD; simpl).
    autorewrite_with_eq_rw.
    generalize dependent (typ0_cast (F:=T)).
    generalize dependent (typ0_cast (F:=U)).
    generalize dependent (typ0 (F:=U)).
    generalize dependent (typ0 (F:=T)).
    intros. destruct e. destruct e0. simpl in *.
    generalize dependent (typ2_cast t t0).
    generalize dependent (typD (typ2 t t0)).
    do 3 intro; subst.
    simpl. exact (fun x => x).
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

  Lemma run_tptrn_id_sound tus tvs t p e val (p_ok : ptrn_ok p)
        (H : ExprDsimul.ExprDenote.lambda_exprD tus tvs t e = Some val)
        (HSucceeds : forall e', Succeeds e p e' ->
                                ExprDsimul.ExprDenote.lambda_exprD tus tvs t e' = Some val) :
    ExprDsimul.ExprDenote.lambda_exprD tus tvs t
                                 (run_ptrn p e e) = Some val.
  Proof.
    unfold run_ptrn.
    destruct (p_ok e).
    { destruct H0.
      specialize (HSucceeds _ H0).
      unfold Succeeds in *.
      setoid_rewrite H0. eauto. }
    { red in H0. setoid_rewrite H0. eauto. }
  Qed.

End setoid.

Hint Opaque app appr appl inj abs var uvar : typeclass_instances.

Ltac destruct_prod :=
  repeat match goal with
         | p : ?A * ?B |- _ => destruct p
         | _ => idtac
         end.

Ltac force_apply lem :=
  let L := fresh "L" in
  pose proof lem as L; simpl in L; apply L; clear L.

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
    | |- context [ExprDsimul.ExprDenote.lambda_exprD ?tus ?tvs ?t (Red.beta ?e)] =>
      apply (@lambda_exprD_beta _ _ _ _ _ _ _ _ tus tvs e t);
        eexists; split; [exprDI | try reflexivity]
    | _ => try eassumption
    | _ => try reflexivity
  end.

Ltac ptrnE :=
  ptrn_elim; destruct_prod; simpl in *; subst; inv_all; repeat subst;
  repeat symAsE.

Ltac solve_denotation :=
  ptrnE; repeat exprDI; repeat exprT_App_red.


(* NOTE: These introduce universe problems!
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
