Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
(*
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ}.
*)

  Definition M p t := forall T, (t -> T) -> (p -> T) -> T.

  Definition ret {p t} (v : t) : M p t :=
    fun _ good _ => good v.

  Definition fail {p t} (v : p) : M p t :=
    fun _ _ bad => bad v.

  Definition prod {p t u} (ma : M p t) (mb : M p u)
  : M p (t * u) :=
    fun _T good bad =>
      @ma _T (fun t => @mb _T (fun u => good (t,u)) bad) bad.

  Definition ptrn (X : Type) (t : Type) : Type :=
    X -> M X t.

  Definition Mt t := forall T, (t -> T) -> T.

  Definition tptrn X (t : Type) : Type :=
    X -> Mt t.


  Definition por {X t} (l r : ptrn X t) : ptrn X t :=
    fun e T good bad =>
      l e T good (fun x => r x T good bad).

  Definition pmap {X t u} (f : t -> u) (p : ptrn X t) : ptrn X u :=
    fun e T good bad =>
      p e T (fun x => good (f x)) bad.

  Definition get {X} : ptrn X X :=
    fun e _ good _ => good e.

  Definition ignore {X} : ptrn X unit :=
    fun e _ good _ => good tt.

  Definition pret {X t} (v : t) : ptrn X t :=
    fun e _ good _ => good v.

  Definition ptret {X t} (v : t) : tptrn X t :=
    fun e _ good => good v.

  Definition pfail {X} : ptrn X Empty_set :=
    fun e _ _ bad => bad e.

  Definition app {T U} (f : ptrn (expr typ func) T) (g : ptrn (expr typ func) U) : ptrn (expr typ func) (T * U) :=
    fun e _T good bad =>
      match e with
      | App l r => f l _T (fun f => g r _T (fun x => good (f,x)) (fun x => bad (App l x))) (fun x => bad (App x r))
      | Abs a b => bad (Abs a b)
      | UVar a => bad (UVar a)
      | Var a => bad (Var a)
      | Inj a => bad (Inj a)
      end%type.

  Require Import ExtLib.Data.HList.

  Fixpoint appN {T} {Ts : list Type} (f : ptrn (expr typ func) T) (args : hlist (ptrn (expr typ func)) Ts)
  : ptrn (expr typ func) (T * hlist (fun x => x) Ts) :=
    match args in hlist _ Ts
          return ptrn (expr typ func) (T * hlist (fun x => x) Ts)
    with
    | Hnil => pmap (fun x => (x,Hnil)) f
    | Hcons p ps => pmap (fun a => let '(a,b,c) := a in
                                   (a, Hcons b c)) (appN (app f p) ps)
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
      end%type.

  Fixpoint exact_nat (n : nat) : ptrn nat unit :=
    fun n' _T good bad =>
      match n , n' with
      | 0 , 0 => good tt
      | S n , S n' => @exact_nat n n' _T good (fun x => bad (S x))
      | _ , 0 => bad 0
      | _ , S n => bad (S n)
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
      | Inj i1 , Inj i2 =>
        bad (Inj i2)
      | _ , App a b => bad (App a b)
      | _ , Abs a b => bad (Abs a b)
      | _ , Inj a => bad (Inj a)
      | _ , Var a => bad (Var a)
      | _ , UVar a => bad (UVar a)
      end.

  Definition pdefault {X T} (p : ptrn X T) (d : T) : tptrn X T :=
    fun e _T good => p e _T good (fun _ => good d).

  Require Import ExtLib.Relations.TransitiveClosure.

  Theorem get_sound_syn : forall {T} (P : T -> M T T -> Prop) e,
      P e (ret e) ->
      P e (get e).
  Proof. clear. intros. apply H. Qed.

  Theorem fail_sound_syn : forall {T} (P : T -> M T _ -> Prop) e,
      P e (fail e) ->
      P e (pfail e).
  Proof. clear. intros. apply H. Qed.

  Definition MR {T U} : relation (M T U) :=
    (fun a b => forall x, ((eq ==> eq) ==> (eq ==> eq) ==> eq) (a x) (b x))%signature.

  Definition ptrnR {T U} : relation (ptrn T U) :=
    (eq ==> MR)%signature.

  Definition MtR {T} : relation (Mt T) :=
    (fun a b => forall x, ((eq ==> eq) ==> eq) (a x) (b x))%signature.

  Definition tptrnR {T U} : relation (tptrn T U) :=
    (eq ==> MtR)%signature.

  Definition Succeeds {X T} e (m : ptrn X T) val : Prop :=
    forall T good bad, m e T good bad = good val.

  Definition Fails {X T} e (m : ptrn X T) : Prop :=
    forall T good bad, m e T good bad = bad e.

  Definition ptrn_ok {A B} (p : ptrn A B) : Prop :=
    forall x,
      (exists y, Succeeds x p y) \/
      (Fails x p).

  Definition Mrebuild {X Y T} (f : X -> Y) (m : M X T) : M Y T :=
    fun _T good bad => m _T good (fun x => bad (f x)).

  Definition Mbind {X T U} (m1 : M X T) (m2 : T -> M X U)
  : M X U :=
    fun _T good bad =>
      m1 _T (fun x => m2 x _T good bad) bad.

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

  Require Import MirrorCore.Lambda.AppN.

  Theorem Succeeds_pmap : forall {X T U} (f : T -> U) p (x : X) res,
      ptrn_ok p ->
      Succeeds x (pmap f p) res ->
      exists y, Succeeds x p y /\ res = f y.
  Proof.
    clear.
    intros. red in H0. unfold pmap in H0.
    destruct (H x).
    { destruct H1. exists x0. split; auto.
      red in H1.
      setoid_rewrite H1 in H0.
      symmetry. eapply (H0 _ (fun x => x)).
      eauto. }
    { red in H1. setoid_rewrite H1 in H0.
      exfalso. specialize (H0 _ (fun _ => true) (fun _ => false)); inversion H0. }
  Qed.

  Theorem Succeeds_por : forall {X T} p1 p2 (x : X) (res : T),
      ptrn_ok p1 -> ptrn_ok p2 ->
      Succeeds x (por p1 p2) res ->
      Succeeds x p1 res \/ Succeeds x p2 res.
  Proof.
    clear. intros.
    destruct (H x) as [ [ ? ? ] | ].
    { left. unfold Succeeds in *.
      intros. setoid_rewrite H2 in H1.
      rewrite H2. eauto. }
    { right.
      unfold Succeeds, Fails in *. unfold por in H1.
      setoid_rewrite H2 in H1.
      eauto. }
  Qed.

  Definition run_tptrn {X T} (p : tptrn X T) (x : X) : T := p x T (fun x => x).

  Theorem pdefault_sound
  : forall X T (P : X -> _ -> Prop) (p : ptrn X T) (d : T) x
           (Hpokp : ptrn_ok p),
      (Proper (eq ==> MtR ==> iff) P) ->
      (forall r, Succeeds x p r -> P x (ptret r x)) ->
      P x (ptret d x) ->
      P x (pdefault p d x).
  Proof.
    intros.
    destruct (Hpokp x).
    { destruct H2.
      eapply H; [ reflexivity | | eapply H0 ]; eauto.
      compute. intros.
      red in H2. erewrite <- H3; try reflexivity.
      eapply H2. }
    { eapply H; [ reflexivity | | eapply H1 ].
      compute; intros.
      erewrite <- H3; try reflexivity.
      eapply H2. }
  Qed.

  Theorem Succeeds_get : forall {X} (x res : X),
      Succeeds x get res ->
      x = res.
  Proof.
    clear. compute. intros.
    eapply (H _ (fun x => x)); eauto.
  Qed.

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

  Existing Class ptrn_ok.
  Instance ptrn_ok_por
  : forall {X T} (p1 : ptrn X T) (p2 : ptrn X T),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (por p1 p2).
  Proof.
    clear.
    intros. red. intros.
    destruct (H x).
    { left. destruct H1. exists x0. revert H1. compute.
      intros. rewrite H1. auto. }
    { destruct (H0 x).
      { left. destruct H2. exists x0.
        unfold Succeeds, Fails in *.
        intros. unfold por. rewrite H1. eauto. }
      { right. unfold por, Fails in *.
        intros. rewrite H1. apply H2. } }
  Qed.
  Instance ptrn_ok_pmap
  : forall {X T U} (p1 : ptrn X T) (f : T -> U),
      ptrn_ok p1 -> ptrn_ok (pmap f p1).
  Proof.
    clear. unfold pmap.
    red; intros.
    destruct (H x).
    { destruct H0. unfold Succeeds, Fails in *.
      setoid_rewrite H0. eauto. }
    { unfold Succeeds, Fails in *.
      setoid_rewrite H0; eauto. }
  Qed.
  Instance ptrn_ok_get : forall {X}, ptrn_ok (@get X).
  Proof.
    left. exists x. compute. reflexivity.
  Qed.
  Instance ptrn_ok_fail : forall {X}, ptrn_ok (@pfail X).
  Proof.
    right. compute. reflexivity.
  Qed.
  Instance ptrn_ok_app
  : forall {T U} (p1 : ptrn _ T) (p2 : ptrn _ U),
      ptrn_ok p1 -> ptrn_ok p2 -> ptrn_ok (app p1 p2).
  Proof.
    clear; compute.
    destruct x; eauto.
    destruct (H x1) as [ [ ? ? ] | ? ]; setoid_rewrite H1; eauto.
    destruct (H0 x2) as [ [ ? ? ] | ? ]; setoid_rewrite H2; eauto.
  Qed.
  Instance ptrn_ok_inj
  : forall {T} (p1 : ptrn _ T), ptrn_ok p1 -> ptrn_ok (inj p1).
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
    destruct (H f) as [ [ ? ? ] | ? ]; setoid_rewrite H0; eauto.
  Qed.
  Instance ptrn_ok_var : ptrn_ok var.
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
  Qed.
  Instance ptrn_ok_uvar : ptrn_ok uvar.
  Proof.
    clear. compute.
    destruct x; simpl; eauto.
  Qed.
  Instance ptrn_ok_abs
  : forall {T U} (p1 : ptrn _ T) (p2 : _ -> ptrn _ U),
      ptrn_ok p1 -> (forall x, ptrn_ok (p2 x)) -> ptrn_ok (abs p1 p2).
  Proof.
    clear; compute; destruct x; eauto.
    destruct (H t) as [ [ ? ? ] | ? ] ; setoid_rewrite H1; eauto.
    destruct (H0 x0 x) as [ [ ? ? ] | ? ] ; setoid_rewrite H2; eauto.
  Qed.

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

  Instance Injective_Succeeds_por {X T} p1 p2 x res : ptrn_ok p1 -> ptrn_ok p2 -> Injective (Succeeds x (por p1 p2) res) :=
  { result := _
  ; injection := @Succeeds_por X T _ _ _ _ _ _ }.

  Instance Injective_Succeeds_pmap {X T U} f p x res : ptrn_ok p -> Injective (Succeeds x (pmap f p) res) :=
  { result := _
  ; injection := @Succeeds_pmap X T U _ _ _ _ _ }.

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

  Instance Injective_Succeeds_get X x res : Injective (Succeeds x (@get X) res) :=
  { result := _
  ; injection := @Succeeds_get _ _ _ }.


(*
  Ltac drive_Succeeds :=
    let tc := eauto 100 with typeclass_instances in
    repeat match goal with
           | H : Succeeds _ (por _ _) _ |- _ =>
             eapply Succeeds_por in H ; [ destruct H | clear H ; tc | clear H ; tc ]
           | H : Succeeds _ (pmap _ _) _ |- _ =>
             eapply Succeeds_pmap in H ; [ destruct H as [ ? [ ? ? ] ] ; subst | clear H ; tc ]
           | H : Succeeds _ (inj _) _ |- _ =>
             eapply Succeeds_inj in H ; [ destruct H as [ ? [ ? ? ] ] ; subst | clear H ; tc ]
           | H : Succeeds _ (app _ _) ?X |- _ =>
             eapply Succeeds_app in H ;
               [ destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ] ; subst ;
                 try (is_var X; destruct X; simpl in * )
               | clear H ; tc
               | clear H ; tc ]
           | H : Succeeds _ get _ |- _ =>
             eapply Succeeds_get in H ; subst
           end.
*)

  (** Demo *)
  Parameter s_cons : forall {T} (p : ptrn typ T), ptrn func T.
  Parameter s_nil : forall {T} (p : ptrn typ T), ptrn func T.

  Instance ptrn_ok_s_cons : forall {T} (p : ptrn _ T), ptrn_ok p -> ptrn_ok (s_cons p).
  Admitted.
  Instance ptrn_ok_s_nil : forall {T} (p : ptrn _ T), ptrn_ok p -> ptrn_ok (s_nil p).
  Admitted.

  Definition list_case {T} (t : ptrn typ T)
             {P:Type}
             (f_nil : T -> P)
             (f_cons : T -> expr typ func -> expr typ func -> P)
             (f_default : P)
  : expr typ func -> P :=
    run_tptrn (pdefault (por (pmap (fun t => f_nil t) (inj (s_nil t)))
                             (pmap (fun xy =>
                                      match xy with
                                      | ((t,x),y) => f_cons t x y
                                      end) (app (app (inj (s_cons t)) get) get)))
                        f_default).

  Theorem list_case_sound : forall {T U}
           (P : expr typ func -> U -> Prop) do_default do_nil do_cons t e
      (Hpok : ptrn_ok t),
      (forall f res,
          Succeeds f (s_nil t) res ->
          P (Inj f) (do_nil res)) ->
      (forall f res ea eb,
          Succeeds f (s_cons t) res ->
          (leftTrans (@expr_acc _ _)) ea e ->
          (leftTrans (@expr_acc _ _)) eb e ->
          P (App (App (Inj f) ea) eb) (do_cons res ea eb)) ->
      P e (do_default) ->
      P e (@list_case T t U do_nil do_cons do_default e).
  Proof.
    intros.
    change @list_case
      with (fun T t P (f_nil : T -> P) f_cons f_default =>
              run_tptrn (pdefault (por (pmap (fun t => f_nil t) (inj (s_nil t)))
                                       (pmap (fun xy =>
                                                match xy with
                                                | ((t,x),y) => f_cons t x y
                                                end) (app (app (inj (s_cons t)) get) get)))
                        f_default)).
    simpl.
    unfold run_tptrn.
    eapply pdefault_sound.
    { eauto 14 with typeclass_instances. }
    { compute.
      intros; subst.
      split; intros.
      { erewrite <- H3. eassumption.
        intros; eassumption. }
      { erewrite H3. eassumption.
        intros; eassumption. } }
    { intros.
      inv_all. destruct H2; inv_all; subst.
      { eapply H. eauto. }
      { unfold ptret. destruct x. simpl in *. destruct p. simpl in *.
        eapply H0; eauto.
        { eauto using LTStep, LTFin, acc_App_l, acc_App_r, acc_Abs. }
        { eauto using LTStep, LTFin, acc_App_l, acc_App_r, acc_Abs. } } }
    { eapply H1. }
  Qed.

End setoid.

(*
  Print list_case.

  Eval compute in por (pmap (fun _ => 1) (app get get))
                      (pmap (fun _ => 2) (var)).

Require Import MirrorCore.Util.Nat.
Check lt_rem.

  Definition under (n : nat) : ptrn nat :=
    fun e _T good bad =>
      match e with
      | Var v => match lt_rem v n with
                 | None => bad
                 | Some v => good v
                 end
      | _ => bad
      end.
*)