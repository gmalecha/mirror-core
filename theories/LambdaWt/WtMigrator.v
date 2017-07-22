Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.
Require Import MirrorCore.LambdaWt.WtType.
Require Import MirrorCore.LambdaWt.WtExpr.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_inj_impl
    : forall  t ts
         (Ts : hlist F (t :: ts)) (Us : hlist G (t :: ts)),
      hlist_Forall2 P Ts Us ->
      P (hlist_hd Ts) (hlist_hd Us) /\
      hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us).
  Proof.
    clear.
    intros.
    Print hlist_Forall2.
    refine
      match H in @hlist_Forall2 _ _ _ _ ts xs ys
            return match ts as ts return hlist F ts -> hlist G ts -> Prop with
                   | nil => fun _ _ => True
                   | t :: ts => fun Ts Us => P (hlist_hd Ts) (hlist_hd Us) /\ hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us)
                   end xs ys
      with
      | hlist_Forall2_nil _ => I
      | hlist_Forall2_cons _ _ _ _ _ => conj _ _
      end.
    assumption. assumption.
  Defined.

  Lemma hlist_Forall2_inj
    : forall  t ts
         (Ts : hlist F (t :: ts)) (Us : hlist G (t :: ts)),
      hlist_Forall2 P Ts Us <->
      P (hlist_hd Ts) (hlist_hd Us) /\
      hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us).
  Proof.
    split. eapply hlist_Forall2_inj_impl.
    intro.
    rewrite (hlist_eta Ts). rewrite (hlist_eta Us).
    destruct H; constructor; auto.
  Defined.

End hlist.

Section hlist'.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_hlist_map_l
  : forall F' (f : forall t, F' t -> F t) ts (xs : hlist _ ts) ys,
      hlist_Forall2 P (hlist_map f xs) ys <->
      hlist_Forall2 (fun t x y => P (f _ x) y) xs ys.
  Proof.
    induction xs; intros.
    { rewrite (hlist_eta ys). simpl. split; constructor. }
    { rewrite hlist_Forall2_inj. rewrite IHxs.
      rewrite hlist_Forall2_inj. reflexivity. }
  Defined.

  Lemma hlist_Forall2_hlist_map_swap
  : forall ts (xs : hlist _ ts) ys,
      hlist_Forall2 P xs ys <->
      hlist_Forall2 (fun t x y => P y x) ys xs.
  Proof.
    induction xs; intros.
    { rewrite (hlist_eta ys). simpl. split; constructor. }
    { rewrite hlist_Forall2_inj. rewrite IHxs.
      rewrite hlist_Forall2_inj. reflexivity. }
  Defined.

End hlist'.

Section hlist'''.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_hlist_map_r
  : forall G' (f : forall t, G' t -> G t) ts (xs : hlist _ ts) ys,
      hlist_Forall2 P xs (hlist_map f ys) <->
      hlist_Forall2 (fun t x y => P x (f _ y)) xs ys.
  Proof.
    intros. rewrite hlist_Forall2_hlist_map_swap.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_swap.
    reflexivity.
  Defined.

End hlist'''.

Section hlist''.

  Variables (T : Type) (F : T -> Type) (P : forall (t : T), F t -> F t -> Prop).

  Lemma hlist_Forall2_hlist_Forall
  : forall ts (xs : hlist _ ts),
      hlist_Forall (fun t x => P x x) xs <->
      hlist_Forall2 P xs xs.
  Proof.
    split.
    { induction 1; constructor; auto. }
    { induction xs; intros.
      - constructor.
      - apply hlist_Forall2_inj_impl in H. destruct H; constructor; auto. }
  Defined.

End hlist''.

(* This is the universe of the reified language *)
Universe Urefl.

Section SimpleCat.
  Variable I : Type.
  
  (** Category *)
  Class SCat (arr : I -> I -> Type) : Type :=
  { rel : forall {i i'}, arr i i' -> arr i i' -> Prop
  ; id : forall i, arr i i
  ; compose : forall {i i' i''}, arr i' i'' -> arr i i' -> arr i i''
  ; Reflexive_rel :> forall {i i'}, Reflexive (@rel i i')
  ; Transitive_rel :> forall {i i'}, Transitive (@rel i i')
  ; id_compose : forall i i' (m : arr i i'), rel (compose (@id _) m) m
  ; compose_id : forall i i' (m : arr i i'), rel (compose m (@id _)) m
  ; compose_compose : forall i i' i'' i''' (a : arr i i') (b : arr i' i'') (c : arr i'' i'''),
      rel (compose c (compose b a)) (compose (compose c b) a)
  }.

  Arguments rel [_] {_ _} _.
  Arguments id {_ _} {_}.
  Arguments compose {_ _} {_ _ _} _ _.

  (** Functor *)
  Class SFunctor (arr1 arr2 : I -> I -> Type) (SC1 : SCat arr1) (SC2 : SCat arr2)
  : Type :=
  { apply : forall {i i'}, arr1 i i' -> arr2 i i'
  ; apply_id : forall {i}, rel i (apply (@id _ SC1 i)) (@id _ _ _)
  ; apply_compose : forall i i' i'' (a : arr1 i' i'') (b : arr1 i i'),
      rel _ (apply (compose a b)) (compose (apply a) (apply b))
  }.

End SimpleCat.

Section subst_is_cat.
  Variable Tsymbol : Type.
  Variable Esymbol : type Tsymbol -> Type.

  Variable tus : list (Tuvar Tsymbol).

  Definition Vmigrator (tvs tvs' : list (type Tsymbol)) : Type :=
    hlist (wtexpr Esymbol tus tvs') tvs.

  Definition Vmigrator_id {tvs} : Vmigrator tvs tvs :=
    hlist_map (fun t m => wtVar m) (members tvs).

  Definition Vmigrator_compose {tvs tvs' tvs''}
             (g : Vmigrator tvs' tvs'')
  : Vmigrator tvs tvs' -> Vmigrator tvs tvs'' :=
    hlist_map (fun t e => subst g e).

  Variable Rexpr : forall tvs t, wtexpr Esymbol tus tvs t -> wtexpr Esymbol tus tvs t -> Prop.

  Definition RVmigrator (tvs tvs' : list (type Tsymbol))
             : Vmigrator tvs tvs' -> Vmigrator tvs tvs' -> Prop :=
    @hlist_Forall2 _ _ _ (fun _ e1 e2 => Rexpr e1 e2) _.

  Variable Refl_Rexpr : forall tvs t, Reflexive (@Rexpr tvs t).
  Variable Trans_Rexpr : forall tvs t, Transitive (@Rexpr tvs t).

  Theorem Refl_RVmigrator : forall tvs tvs', Reflexive (@RVmigrator tvs tvs').
  Proof.
    red. red.
    induction x; constructor.
    - reflexivity.
    - assumption.
  Defined.

  Theorem Trans_RVmigrator : forall tvs tvs', Transitive (@RVmigrator tvs tvs').
  Proof.
    red. red.
    induction 1.
    - rewrite (hlist_eta z). constructor.
    - intro. eapply hlist_Forall2_inj in H1.
      rewrite (hlist_eta z). destruct H1. constructor; auto. etransitivity; eassumption.
  Defined.

  Lemma subst_id : forall tvs ts t (e : wtexpr Esymbol tus (ts ++ tvs) t),
      subst Vmigrator_id e = e.
  Proof.
    intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    - unfold Vmigrator_id. rewrite hlist_get_hlist_map.
      rewrite hlist_get_members. reflexivity.
    - f_equal; eauto.
    - f_equal.
      etransitivity; [ | eapply H ].
      f_equal. unfold Vmigrator_id. simpl.
      repeat rewrite hlist_map_hlist_map.
      reflexivity.
    - f_equal. clear - H.
      induction H; simpl; auto.
      f_equal; eauto.
  Defined.

  Theorem Vmigrator_id_compose : forall i i' (m : Vmigrator i i'),
      RVmigrator (Vmigrator_compose (@Vmigrator_id _) m) m.
  Proof.
    red.
    unfold Vmigrator_compose; intros.
    eapply hlist_Forall2_hlist_map_l.
    eapply hlist_Forall2_hlist_Forall.
    induction m; constructor; eauto.
    generalize (@subst_id _ nil _ f). simpl.
    intro H; rewrite H. reflexivity.
  Defined.

  Lemma hlist_Forall2_members_l:
    forall (T : Type) (i : list T) (T0 : T -> Type) (m : hlist T0 i)
      (P : forall t : T, member t i -> T0 t -> Prop) 
      ,
      hlist_Forall (fun (t : T) (mem : member t i) => P t mem (hlist_get mem m)) (members i) ->
      hlist_Forall2 P (members i) m.
  Proof.
    clear. induction m; intros.
    - constructor.
    - simpl in *.
      constructor; eauto.
      Focus 2. rewrite hlist_Forall2_hlist_map_l.
      eapply IHm.
      admit.
      admit.
  Admitted.
      

  Theorem Vmigrator_compose_id : forall i i' (m : Vmigrator i i'),
      RVmigrator (Vmigrator_compose m (@Vmigrator_id _)) m.
  Proof.
    red.
    unfold Vmigrator_compose; intros.
    eapply hlist_Forall2_hlist_map_l.
    unfold Vmigrator_id.
    eapply hlist_Forall2_hlist_map_l.
    simpl.
    eapply hlist_Forall2_members_l.
    admit.
  Admitted.

  Lemma hlist_Forall_pure : forall T (F : T -> Type) (P : forall t, F t -> Prop) ls (hs : hlist F ls),
      (forall t x, P t x) ->
      hlist_Forall P hs.
  Proof.
    clear.
    induction hs; constructor; eauto.
  Defined.

  Definition Vmigrator_weaken_pre i i' ts
  : Vmigrator i i' -> Vmigrator i (ts ++ i') :=
    hlist_map (fun t e => wtexpr_lift ts nil e).
  Definition Vmigrator_weaken_post i i' ts
  : Vmigrator i i' -> Vmigrator i (i' ++ ts) :=
    let mig :=
        match app_nil_r_trans i' in _ = X , app_nil_r_trans ts in _ = Y
              return forall t, wtexpr _ _ X t -> wtexpr _ _ (_ ++ Y) t
        with
        | eq_refl , eq_refl => @wtexpr_lift _ _ _ _ ts i'
        end
    in hlist_map mig.

  Definition Vmigrator_par a b d
  : Vmigrator a d -> Vmigrator b d -> Vmigrator (a ++ b) d :=
    @hlist_app _ _ _ _.

  Theorem Vmigrator_par_compose : forall i i' i'' i''' a b d,
      RVmigrator (Vmigrator_compose d (@Vmigrator_par i i' i'' a b))
                 ((@Vmigrator_par i i' i''' (Vmigrator_compose d a) (Vmigrator_compose d b))).
  Proof.
    clear - Refl_Rexpr.
    unfold Vmigrator_compose, Vmigrator_par, RVmigrator. simpl.
    intros. rewrite <- hlist_app_hlist_map.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    apply hlist_Forall2_hlist_Forall.
    apply hlist_Forall_pure.
    intros; reflexivity.
  Defined.



  Lemma subst_subst:
    forall (i' : list (type Tsymbol))
      ts (t : type Tsymbol) (x : wtexpr Esymbol tus (ts ++ i') t)
      i'' i'''  (c : Vmigrator i'' i''') (b : Vmigrator (ts ++ i') i'') ,
      subst c (subst b x) =
      subst (hlist_map (fun (t0 : type Tsymbol) (e : wtexpr Esymbol tus i'' t0) => subst c e) b) x.
  Proof.
    clear. intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    { rewrite hlist_get_hlist_map. reflexivity. }
    { f_equal; eauto. }
    { f_equal. rewrite hlist_map_hlist_map.
      rewrite H; clear H. simpl.
      rewrite hlist_map_hlist_map.
      f_equal. f_equal.
      eapply hlist_map_ext.
      intros.
      generalize (@subst_wtexpr_lift _ Esymbol tus nil _ _ t (d :: nil)
                                     _ Hnil (Hcons (wtVar (MZ d i''')) Hnil)
                                     (hlist_map (fun (t0 : type Tsymbol) (e : wtexpr Esymbol tus i''' t0) => wtexpr_lift (d :: nil) nil e)
                                                c0)).
      simpl. intro H.
      change_rewrite H; clear H.
      clear.
      Check wtexpr_lift.
      change (subst (@Vmigrator_lift _ _ (d :: nil) c0) t = wtexpr_lift (d :: nil) nil (subst c0 t)).

      Lemma wtexpr_lift_subst:
        forall (i'' : list (type Tsymbol))
          ts (x : type Tsymbol) (t : wtexpr Esymbol tus (ts ++ i'') x)
          i'''
          (c0 : Vmigrator (ts ++ i'') i''') z,
          subst (Vmigrator_lift z c0) t = wtexpr_lift z nil (subst c0 t).
      Proof.
        unfold Vmigrator_lift.
        intro.
        refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
        { rewrite hlist_get_hlist_map. reflexivity. }
        { f_equal; eauto. }
        { f_equal. rewrite hlist_map_hlist_map.


  Theorem Vmigrator_compose_compose
  : forall i i' i'' i''' (a : Vmigrator i i') (b : Vmigrator i' i'') (c : Vmigrator i'' i'''),
      RVmigrator (Vmigrator_compose c (Vmigrator_compose b a))
                 (Vmigrator_compose (Vmigrator_compose c b) a).
  Proof.
    unfold Vmigrator_compose. intros.
    rewrite hlist_map_hlist_map.
    red.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    eapply hlist_Forall2_hlist_Forall.
    eapply hlist_Forall_pure.
    intros.

      



Section Migrator.
  Variable I : Type.
  Variable T : I -> Type.

  Variable m : 

  Class Migrator (m : I -> I -> Type)
        (Rm : forall i i', m i i' -> m i i' -> Prop)
        (Rt : forall i, T i -> T i -> Prop)
  : Type :=
  { migrate : forall i i', m i i' -> T i -> T i'
  ; Proper_migrate : forall i i',
      Proper (@Rm i i' ==> Rt i ==> Rt i') (@migrate i i')
  }.



  Context {SC : SCat m}.

End Migrator.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.

  (** Instantiation **)
  Definition migrator (tus tus' : list (Tuvar Tsymbol)) : Type :=
    hlist (fun tst => wtexpr Esymbol tus' (fst tst) (snd tst)) tus.

  Definition migrator_tl
  : forall {a b c} (mig : migrator (b :: c) a),
      migrator c a := fun _ => @hlist_tl _ _.

  Section class.
    Variable T : list (Tuvar Tsymbol) -> list (type Tsymbol) -> Type.
    Class Migrate : Type :=
    { migrate : forall {tus tus'}, migrator tus tus' ->
                                   forall tvs, T tus tvs -> T tus'  tvs }.
  End class.

  Definition migrate_env {tus tus'}
             (mig : migrator tus' tus) (e : Uenv TsymbolD tus)
  : Uenv TsymbolD tus' := Eval cbv beta in
    hlist_map (fun _ val => wtexprD EsymbolD val e) mig.

  Section migrate_expr.
    Context {tus tus'} (mig : migrator tus tus').

    Fixpoint migrate_expr {tvs t}
             (e : wtexpr Esymbol tus tvs t)
    : wtexpr Esymbol tus' tvs t :=
      match e in wtexpr _ _ _ t
            return wtexpr _ tus' tvs t
      with
      | wtVar v => wtVar v
      | wtInj v => wtInj v
      | wtApp f x => wtApp (migrate_expr f) (migrate_expr x)
      | wtAbs e => wtAbs (migrate_expr e)
      | wtUVar u vs => subst (hlist_map (@migrate_expr tvs) vs) (hlist_get u mig)
      end.
  End migrate_expr.

  Global Instance Migrate_wtexpr t
  : Migrate (fun tus tvs => wtexpr Esymbol tus tvs t) :=
  { migrate := fun tus tus' mig tvs => @migrate_expr _ _ mig _ t }.

  Definition migrator_compose {tus tus' tus''}
           (mig : migrator tus tus')
           (mig' : migrator tus' tus'')
  : migrator tus tus'' :=
    hlist_map (fun t e => migrate_expr mig' e) mig.



  Lemma wtexpr_lift_migrate_expr'
  : forall (tus' tus'' : list (Tuvar Tsymbol)) (mig' : migrator tus' tus'')
           (d tvs0 d' : list (type Tsymbol))
           (x : type Tsymbol) (e : wtexpr Esymbol tus' (d' ++ tvs0) x),
      wtexpr_lift d d' (migrate_expr mig' e) =
      migrate_expr mig' (wtexpr_lift d d' e).
  Proof using.
    do 5 intro.
    eapply wtexpr_ind_app; simpl; intros; eauto.
    { rewrite H. rewrite H0. reflexivity. }
    { rewrite H. reflexivity. }
    { generalize (hlist_get u mig'); simpl; intros.
      rewrite hlist_map_hlist_map.

      SearchAbout wtexpr_lift.
      admit. }
  Admitted.


  Lemma wtexpr_lift_migrate_expr
  : forall (tus' tus'' : list (Tuvar Tsymbol)) (mig' : migrator tus' tus'')
           (d tvs0 d' : list (type Tsymbol))
           (x : type Tsymbol) (t : wtexpr Esymbol tus' (d' ++ tvs0) x),
      wtexpr_lift d d' (migrate_expr mig' t) =
      migrate_expr mig' (wtexpr_lift d d' t).
  Proof using.
    do 5 intro.
    eapply wtexpr_ind_app; simpl; intros; eauto.
    { rewrite H. rewrite H0. reflexivity. }
    { rewrite H. reflexivity. }
    { (** TODO(gmalecha): Here I need to have some information about the result
       ** of looking up any unification variable in mig'. In particular, I need
       ** to know that subst commutes with wtexpr_lift.
       ** If tus'' is smaller than tus', then i can do induction on the number
       ** of unification variables, but if not, then I'm in trouble.
       ** An alternative could be induction on the number of instantiations since
       ** I know that these variables do not exist in the result, but I guess that
       ** is not captured in the above types. In particular, I need a acyclic
       ** property to justify structural recursion.
       **)

 generalize (hlist_get u mig'); simpl; intros.
      rewrite hlist_map_hlist_map.

          Lemma member_lift_nil:
            forall (T : Type) (tvs' tvs : list T) (t : T) (m : member t (tvs ++ tvs')),
              member_lift tvs' nil tvs m = m.
          Proof.
            clear.
            induction tvs; simpl.
            { reflexivity. }
            { intros. destruct (member_case m) as [ [ ? ? ] | [ ? ? ] ].
              { subst. reflexivity. }
              { subst. f_equal; auto. } }
          Defined.
          Lemma wtexpr_lift_nil:
            forall (tus : list (Tuvar Tsymbol)) (tvs' ts : list (type Tsymbol))
                   (x : type Tsymbol) (t : wtexpr Esymbol tus (ts ++ tvs') x),
              @wtexpr_lift _ _ tus tvs' x nil ts t = t.
          Proof.
            do 2 intro.
            refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
            { f_equal.
              apply member_lift_nil. }
            { f_equal; assumption. }
            { f_equal; auto. }
            { f_equal. clear - H.
              induction H; simpl; auto.
              f_equal; auto. }
          Defined.


      Check wtexpr_lift.
      Lemma wtexpr_lift_subst:
        forall (tus : list (Tuvar Tsymbol))
          (tvs tvs' tvs'' ts : list (type Tsymbol)) (t : type Tsymbol)
          (w : wtexpr Esymbol tus (ts ++ tvs) t)
          (xs : hlist (wtexpr Esymbol tus (ts ++ tvs')) (ts ++ tvs)),
          @wtexpr_lift _ _ tus _ t _ _ (subst xs w) =
          subst
            (hlist_map
               (fun (t : type Tsymbol) (e : wtexpr Esymbol tus _ t) =>
                  @wtexpr_lift _ _ tus _ t tvs'' _ e) xs) w.
      Proof.
        do 4 intro.
        refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
        { rewrite hlist_get_hlist_map. reflexivity. }
        { f_equal; eauto. }
        { f_equal. rewrite hlist_map_hlist_map.
          specialize (fun xs => H (Hcons (wtVar (MZ d (tvs0 ++ tvs'))) xs)).
          simpl in H. rewrite H. f_equal. f_equal.
          rewrite hlist_map_hlist_map. eapply hlist_map_ext. intros.
          clear.
          Check (wtexpr_lift (d :: nil) nil t).
          Check (wtexpr_lift tvs'' tvs0 t).
           Print subst.


          revert t. revert x. revert tvs0.
          refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; try f_equal; eauto.
          { SearchAbout wtexpr_lift.


          Lemma wtexpr_lift_wtexpr_lift:
            forall (tus : list (Tuvar Tsymbol)) (tvs' tvs'' tvs0 : list (type Tsymbol))
                   d (x : type Tsymbol) (t : wtexpr Esymbol tus (tvs0 ++ tvs') x),
              wtexpr_lift tvs'' (d :: tvs0) (wtexpr_lift (d :: nil) nil t) =
              wtexpr_lift (d :: nil) nil (wtexpr_lift tvs'' tvs0 t).
          Proof.

            intros.
            Set Printing Implicit.
            Print wtexpr_lift.
            Check wtexpr_lift tvs'' (d :: tvs0) (wtexpr_lift (d :: nil) nil t).
            Check wtexpr_lift (d :: nil) nil (wtexpr_lift tvs'' tvs0 t).




      Print migrate_expr.
      SearchAbout subst wtexpr_lift.
      admit. }
  Admitted.

  Lemma subst_subst'
  : forall tus tvs' tvs'' tvs Z t (e : wtexpr Esymbol tus (Z ++ tvs) t)
           (X : hlist (fun t => wtexpr Esymbol tus (Z ++ tvs'') t) tvs')
           (Y : hlist (fun t => wtexpr Esymbol tus (Z ++ tvs') t) tvs)
           P Q,
      subst (hlist_app Q X) (subst (hlist_app P Y) e) =
      subst (hlist_map (fun t e => subst (hlist_app Q X) e) (hlist_app P Y)) e.
  Proof using.
    clear.
    do 7 intro.
    eapply wtexpr_ind_app with (tus:=tus) (tvs:=tvs) (e:=e);
      try solve [ simpl; intros; auto ].
    { simpl; intros. rewrite hlist_get_hlist_map. reflexivity. }
    { simpl; intros; rewrite <- H. rewrite <- H0. reflexivity. }
    { intros.
      simpl.
      specialize (H (hlist_map (fun t e => wtexpr_lift (d::nil) nil e) X)
                    (hlist_map (fun t e => wtexpr_lift (d::nil) nil e) Y)
                    (Hcons (wtVar (MZ d _))
                           (hlist_map (fun t e => wtexpr_lift (d::nil) nil e) P))
                    (Hcons (wtVar (MZ d _))
                           (hlist_map (fun t e => wtexpr_lift (d::nil) nil e) Q))).
      simpl in H.
      f_equal.
      repeat rewrite hlist_app_hlist_map in H.
      repeat rewrite hlist_app_hlist_map.
      etransitivity; [ eapply H | clear H ].
      f_equal. f_equal.
      f_equal.
      { repeat rewrite hlist_map_hlist_map.
        eapply hlist_map_ext. intros.
        SearchAbout subst wtexpr_lift.


        admit. }
      admit. }
  Admitted.

  Lemma migrate_expr_migrator_compose
  : forall tus tus' tus'' tvs t
           (mig : migrator tus tus') (mig' : migrator tus' tus'')
           (e : wtexpr Esymbol _ tvs t),
      migrate_expr (migrator_compose mig mig') e =
      migrate_expr mig' (migrate_expr mig e).
  Proof.
    induction e; simpl; auto.
    { rewrite IHe1. rewrite IHe2. reflexivity. }
    { rewrite IHe. reflexivity. }
    { unfold migrator_compose at 2.
      rewrite hlist_get_hlist_map.
      transitivity (subst
                      (hlist_map (fun t e => migrate_expr mig' e) (hlist_map (@migrate_expr _ _ mig _) xs))
                      (migrate_expr mig' (hlist_get u mig))).
      { f_equal. clear - H.
        induction H; simpl; auto.
        { rewrite H. rewrite IHhlist_Forall. reflexivity. } }
      { clear H.
        generalize (hlist_map (@migrate_expr tus tus' mig tvs) xs).
        clear. generalize dependent tvs.
        generalize (hlist_get u mig).
        simpl; clear.
        (** LEMMA **)
        induction w; intros; simpl; auto.
        { repeat rewrite hlist_get_hlist_map.
          reflexivity. }
        { rewrite IHw1. rewrite IHw2. reflexivity. }
        { specialize (fun h => IHw (d::tvs0) (@Hcons _ _ _ _ (wtVar (MZ d tvs0)) h)).
          specialize (IHw (hlist_map (fun t e => wtexpr_lift (d::nil) nil e) h)).
          simpl in IHw.
          revert IHw.
          match goal with
          | |- _ = ?X -> _ = wtAbs ?Y =>
            change X with Y; generalize Y
          end; intros; subst.
          repeat rewrite hlist_map_hlist_map.
          f_equal.
          f_equal. f_equal.
          eapply hlist_map_ext.
          intros. rewrite wtexpr_lift_migrate_expr. reflexivity. }
        { rewrite hlist_map_hlist_map.
          intros.
          admit. }
  Admitted.

  Theorem migrate_env_migrate_expr
  : forall tus tus' tvs t (mig : migrator tus tus')
           (e : wtexpr Esymbol tus tvs t),
      forall us vs,
        wtexprD EsymbolD (migrate_expr mig e) us vs =
        wtexprD EsymbolD e (migrate_env mig us) vs.
  Proof.
    induction e.
    { simpl. unfold Var_exprT. reflexivity. }
    { simpl. unfold Pure_exprT. reflexivity. }
    { simpl. unfold Ap_exprT. intros.
      rewrite IHe1. rewrite IHe2. reflexivity. }
    { simpl. unfold Abs_exprT. intros.
      eapply FunctionalExtensionality.functional_extensionality.
      intros. eapply IHe. }
    { simpl. intros. unfold UVar_exprT.
      unfold migrate_env at 1.
      rewrite hlist_get_hlist_map.
      generalize (hlist_get u mig); simpl.
      rewrite hlist_map_hlist_map.
      intros. rewrite wtexprD_subst.
      rewrite hlist_map_hlist_map.
      f_equal.
      clear - H.
      induction H; simpl.
      - reflexivity.
      - f_equal; eauto. }
  Qed.

  Section mid.
    Variable T : Tuvar Tsymbol -> Type.

    Local Fixpoint migrator_id' (tus : list (Tuvar Tsymbol)) {struct tus}
    : (forall ts t, member (ts,t) tus -> T (ts,t)) ->
      hlist T tus :=
      match tus as tus
            return (forall ts t, member (ts,t) tus -> T (ts,t)) ->
                   hlist T tus
      with
      | nil => fun _ => Hnil
      | (ts,t) :: tus => fun mk =>
                           Hcons (@mk _ _ (@MZ _ _ _))
                                 (migrator_id' (fun ts t z => @mk ts t (MN _ z)))
      end.
  End mid.

  Local Fixpoint vars_id {tus} tvs
  : hlist (wtexpr Esymbol tus tvs) tvs :=
    match tvs as tvs
          return hlist (wtexpr Esymbol tus tvs) tvs
    with
    | nil => Hnil
    | t :: ts =>
      Hcons (wtVar (MZ t ts))
            (hlist_map
               (fun t' : type Tsymbol => wtexpr_lift (t :: nil) nil)
               (vars_id ts))
    end.

  Definition migrator_id tus : migrator tus tus :=
    @migrator_id' _ tus (fun ts t x => wtUVar x (vars_id ts)).
  Arguments migrator_id {tus} : rename.

  Lemma hlist_get_migrator_id'
  : forall T ts t tus mk (m : member (ts,t) tus),
      hlist_get m (@migrator_id' T tus mk) = mk _ _ m.
  Proof.
    induction m; simpl; auto.
    destruct l. simpl. rewrite IHm. reflexivity.
  Qed.

  Lemma hlist_get_migrator_id
  : forall ts t tus (m : member (ts,t) tus),
      hlist_get m (migrator_id (tus:=tus)) = wtUVar m (vars_id _).
  Proof.
    intros. unfold migrator_id.
    rewrite hlist_get_migrator_id'. reflexivity.
  Qed.

  Theorem migrate_expr_migrator_id
  : forall tus tvs t (e : wtexpr _ tus tvs t),
      migrate_expr migrator_id e = e.
  Proof.
    induction e; simpl; intros; auto.
    { rewrite IHe1. rewrite IHe2. reflexivity. }
    { rewrite IHe. reflexivity. }
    { rewrite hlist_get_migrator_id. simpl.
      f_equal.
      clear - H.
      induction H; simpl; auto.
      f_equal; eauto.
      etransitivity; [ | eassumption ].
      rewrite hlist_map_hlist_map.
      eapply hlist_map_ext.
      intros.
      rewrite <- IHhlist_Forall.
      rewrite hlist_map_hlist_map.
      eapply (fun Z => @subst_wtexpr_lift _ _ tus nil _ _ t0 (t :: nil) _
                                          Hnil (Hcons Z Hnil)). }
  Qed.

  Lemma hlist_map_vars_id_id
  : forall (p : _) (x : Venv TsymbolD p)
           (l : list (Tuvar Tsymbol))
           (h : hlist
                  (fun tst : Tuvar Tsymbol =>
                     hlist (typeD TsymbolD) (fst tst) ->
                     typeD TsymbolD (snd tst)) l),
      hlist_map
        (fun (x0 : type Tsymbol) (x1 : wtexpr Esymbol l p x0) =>
           wtexprD EsymbolD x1 h x) (vars_id p) = x.
  Proof.
    induction x; simpl; auto.
    { intros. f_equal. rewrite hlist_map_hlist_map.
      etransitivity; [ | eapply IHx ].
      eapply hlist_map_ext.
      intros.
      erewrite wtexprD_wtexpr_lift
      with (vs'':=Hnil) (vs':=Hcons f Hnil) (vs:=x).
      reflexivity. }
  Qed.

  (** TODO(gmalecha): Move to ExtLib.Data.HList *)
  Lemma hlist_ext : forall T (F : T -> Type) (ls : list T)
                           (a b : hlist F ls),
      (forall t (m : member t ls), hlist_get m a = hlist_get m b) ->
      a = b.
  Proof using.
    clear.
    induction a; intros.
    { rewrite (hlist_eta b). reflexivity. }
    { rewrite (hlist_eta b).
      f_equal.
      { eapply (H _ (MZ _ _)). }
      { eapply IHa.
        intros. eapply (H _ (MN _ _)). } }
  Defined.

  Lemma migrate_env_migrator_id
  : forall tus (e : Uenv TsymbolD tus),
      migrate_env migrator_id e = e.
  Proof using.
    intros.
    eapply hlist_ext; intros.
    unfold migrate_env.
    rewrite hlist_get_hlist_map.
    destruct t.
    rewrite hlist_get_migrator_id with (m:=m).
    simpl. unfold UVar_exprT.
    eapply FunctionalExtensionality.functional_extensionality; intros.
    rewrite hlist_map_hlist_map.
    rewrite hlist_map_vars_id_id.
    reflexivity.
  Qed.

  Definition migrator_fresh t tus
  : migrator tus (tus ++ t :: nil) :=
    Eval simpl in
    migrator_id'
      (fun tst : Tuvar Tsymbol =>
         wtexpr Esymbol (tus ++ t :: nil) (fst tst) (snd tst))
      (fun (ts : list (type Tsymbol)) (t0 : type Tsymbol)
           (X : member (ts, t0) tus) =>
         wtUVar
           (member_lift nil (t :: nil) tus
                        (match eq_sym (app_nil_r_trans tus) in _ = X
                               return member _ X
                         with
                         | eq_refl => X
                         end)) (vars_id _)).

End simple_dep_types.

Arguments migrator {_} _ _ _.
Arguments migrator_id {_ _ tus}.
Arguments migrator_fresh {_ _} _ _.q_eq