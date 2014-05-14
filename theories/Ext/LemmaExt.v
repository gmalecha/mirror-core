Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: This file is probably dead **)
Section with_expr.
  Variable ts : types.
  Variable func : Type.
  Variable conclusion : Type.
  Variable conclusionD
  : forall us vs : list typ,
      conclusion ->
      option (hlist (typD ts nil) us -> hlist (typD ts nil) vs -> Prop).
  Hypothesis conclusionD_weaken : forall us tvs c val,
    conclusionD us tvs c = Some val ->
    forall us' tvs',
      exists val',
        conclusionD (us ++ us') (tvs ++ tvs') c = Some val' /\
        forall u u' x y,
          val u x = val' (hlist_app u u') (hlist_app x y).

  Record lemma : Type :=
  { vars : list typ
  ; premises : list (expr func)
  ; concl : conclusion
  }.

  Global Instance Injective_lemma a b c d e f
  : Injective ({| vars := a ; premises := b ; concl := c |} =
               {| vars := d ; premises := e ; concl := f |}) :=
  { result := a = d /\ b = e /\ c = f }.
  Proof. abstract (inversion 1; auto). Defined.

  Fixpoint foralls (ls : list typ) : (hlist (typD ts nil) ls -> Prop) -> Prop :=
    match ls as ls return (hlist (typD ts nil) ls -> Prop) -> Prop with
      | nil => fun P => P Hnil
      | l :: ls => fun P => forall x : typD ts nil l,
                              foralls (fun z => P (Hcons x z))
    end.

  Fixpoint impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> impls ls P
    end.

  Lemma foralls_sem : forall ls P,
    foralls (ls := ls) P <-> forall h, P h.
  Proof.
    clear.
    induction ls; simpl; intros.
    { intuition; rewrite hlist_eta; auto. }
    { intuition.
      { rewrite hlist_eta.
        specialize (H (hlist_hd h)).
        rewrite IHls in H. eauto. }
      { rewrite IHls. intuition. } }
  Qed.

  Lemma impls_sem : forall ps x,
    impls ps x <->
    (Forall (fun x => x) ps -> x).
  Proof.
    induction ps; simpl; intuition.
    { inversion H0; clear H0; subst.
      eapply IHps; auto. }
    { eapply IHps. intros. eapply H. constructor; auto. }
  Qed.

  Variable RSym_func : RSym (typD ts) func.

  Definition lemmaD (us vs : env (typD ts)) (l : lemma) : Prop :=
    let (tvs,vs) := split_env vs in
    let (tus,us) := split_env us in
    match mapT (fun e =>
                  ExprD.exprD' tus (l.(vars) ++ tvs) e tyProp ) l.(premises)
        , conclusionD tus (l.(vars) ++ tvs) l.(concl)
    with
      | Some prems , Some concl =>
        @foralls l.(vars) (fun h =>
          let h := hlist_app h vs in
          impls (List.map (fun x => x us h) prems)
            (concl us h))
      | _ , _ => False
    end.

  Lemma mapT_compose
  : forall (T U V : Type)
           (EQ : V -> V -> Prop)
           (f : T -> option V)
           (pre : T -> option U) (post : U -> V),
      (forall x, match f x , (Functor.fmap post) (pre x) with
                   | Some a , Some b => EQ a b
                   | None ,  None => True
                   | _ , _ => False
                 end) ->
      forall (ls : list T),
        match mapT f ls
            , Applicative.ap (Applicative.pure (Functor.fmap post)) (mapT pre ls)
        with
          | Some a , Some b => Forall2 EQ a b
          | None , None => True
          | _ , _ => False
        end.
  Proof.
    induction ls.
    { simpl. constructor. }
    { simpl.
      specialize (H a).
      destruct (f a); simpl in *; forward.
      inv_all; subst.
      unfold mapT in IHls; simpl in *.
      repeat match goal with
               | H : context [ match ?X with _ => _ end ]
               |- context [ ?Y ] =>
                 change Y with X; destruct X
             end; auto.
      { simpl. constructor; auto. } }
  Qed.

Lemma mapT_compose'
  : forall (T U V : Type)
           (EQ : V -> V -> Prop)
           (f : T -> option V)
           (pre : T -> option U) (post : U -> V),
      (forall x, match f x , (Functor.fmap post) (pre x) with
                   | Some a , Some b => EQ a b
                   | _ , None => True
                   | _ , _ => False
                 end) ->
      forall (ls : list T),
        match mapT f ls
            , Applicative.ap (Applicative.pure (Functor.fmap post)) (mapT pre ls)
        with
          | Some a , Some b => Forall2 EQ a b
          | _ , None => True
          | _ , _ => False
        end.
  Proof.
    induction ls.
    { simpl. constructor. }
    { simpl.
      specialize (H a).
      destruct (f a); simpl in *; forward.
      inv_all; subst.
      unfold mapT in IHls; simpl in *.
      repeat match goal with
               | H : context [ match ?X with _ => _ end ]
               |- context [ ?Y ] =>
                 change Y with X; destruct X
             end; auto. 
      { simpl. constructor; auto. } }
  Qed.

  Lemma trans_rel T U
  : Transitive (fun (a b : T -> U -> Prop) => forall x y, a x y -> b x y).
  Proof.
    clear. red. intros. eauto.
  Qed.

  Lemma lemmaD_weaken : forall us vs l us' vs',
    lemmaD us vs l ->
    lemmaD (us ++ us') (vs ++ vs') l.
  Proof.
    Opaque mapT foralls impls Monad.liftM.
    unfold lemmaD; destruct l; simpl.
    intros.
    repeat rewrite split_env_app.
    destruct (split_env vs). destruct (split_env vs').
    destruct (split_env us). destruct (split_env us').
    generalize (@mapT_compose' _ _ _ (fun (a b : _ -> _ -> Prop) => forall x y, a x y -> b x y)
                              (fun e : expr func => exprD' (x1 ++ x2) (vars0 ++ x ++ x0) e tyProp)
         (fun e : expr func => exprD' x1 (vars0 ++ x) e tyProp)
         (fun e : hlist (typD ts nil) x1 -> hlist (typD ts nil) (vars0 ++ x) -> Prop =>
                    fun a b =>
                      let (a,_) := @hlist_split _ _ _ _ a in
                      let (b',b'') := @hlist_split _ _ _ _ b in
                      let (b'',_) := @hlist_split _ _ _ _ b'' in
                      e a (hlist_app b' b''))).
    simpl in *; intros.
    match goal with
      | H : ?X -> _ |- _ =>
        let H' := fresh in
        assert (H' : X); [ | specialize (H H'); clear H' ]
    end.
    { clear; intros.
      match goal with
        | |- match ?X with _ => _ end => consider X; intros
      end; forward.
      { inv_all. subst.
        change exprD' with (@ExprI.exprD' _ _ _ (@Expr_expr _ _ _)) in H0.
        simpl in H0.
        eapply exprD'_weaken with (tus' := x2) (tvs' := x0) (t := tyProp) in H0.
        destruct H0 as [ ? [ ? ? ] ].
        forward. erewrite H2.
        instantiate (1 := h4).
        instantiate (1 := h0).
        rewrite hlist_app_assoc; eauto with typeclass_instances.
        assert (y = hlist_app h1 (hlist_app h3 h4)).
        { cutrewrite (hlist_app h3 h4 = h2).
          change h1 with (fst (h1, h2)).
          rewrite <- H4.
          change h2 with (snd (h1, h2)).
          rewrite <- H4.
          symmetry; apply hlist_app_hlist_split.
          change h3 with (fst (h3,h4)).
          rewrite <- H5.
          change h4 with (snd (h3,h4)).
          rewrite <- H5.
          apply hlist_app_hlist_split. }
        assert (x4 = hlist_app h h0).
        { change h with (fst (h,h0)).
          rewrite <- H3.
          change h0 with (snd (h,h0)).
          rewrite <- H3.
          symmetry; apply hlist_app_hlist_split. }
        subst. clear - H1 H H0.
        revert H1.
        match goal with
          | |- _ _ ?X -> _ _ match _ with eq_refl => ?Y end =>
            change X with Y; generalize dependent Y
        end.
        generalize dependent t; generalize dependent x5.
        generalize (eq_sym (app_ass_trans vars0 x x0)).
        rewrite app_ass. uip_all'.
        simpl in *. rewrite H0 in H. inv_all; subst; auto. }
      { clear - H0 H.
        change exprD' with (@ExprI.exprD' _ _ _ (@Expr_expr _ _ _)) in H0.
        simpl in H0.
        eapply exprD'_weaken with (tus' := x2) (tvs' := x0) (t := tyProp) in H0; eauto using ExprOk_expr.
        destruct H0 as [ ? [ ? ? ] ].
        clear - H0 H.
        rewrite <- app_ass in H. simpl in *. congruence. } }
    { specialize (H0 premises0).
      match goal with
        | H : match ?X with _ => _ end
          |- context [ ?Y ] => change Y with X ; destruct X
      end; simpl in *; auto.
      { forward.
        eapply conclusionD_weaken with (us' := x2) (tvs' := x0) in H0.
        destruct H0.
        intuition.
        match goal with
          | |- match ?X with _ => _ end => consider X; intros
        end.
        { rewrite foralls_sem. intro.
          rewrite foralls_sem in H2.
          specialize (H2 h3).
          revert H2. clear H.
          match goal with
            | _ : Forall2 _ _ ?X |- _ => remember X
          end.
          generalize dependent l0.
          induction H1.
          { destruct l0; inversion 1. clear Heql1.
            Transparent impls. simpl. Opaque impls.
            erewrite H4.
            instantiate (1 := h0). instantiate (1 := h2).
            clear - H3 H0.
            rewrite hlist_app_assoc; eauto with typeclass_instances.
            generalize dependent x3. generalize dependent P0.
            uip_all.
            revert H2.
            match goal with
              | |- _ _ match _ with eq_refl => ?X end -> _ _ ?Y =>
                change Y with X; generalize dependent X
            end.
            generalize dependent x3. generalize dependent P0.
            revert e. rewrite <- app_ass.
            uip_all'. rewrite H0 in H3. inv_all; subst. auto. }
          { destruct l0.
            { intro. exfalso. inversion Heql1. }
            { simpl. Transparent impls Monad.liftM. simpl.
              intros.
              inversion Heql1; clear Heql1.
              eapply IHForall2; eauto.
              eapply H8.
              eapply H2; clear H2.
              subst.
              specialize (H (hlist_app h1 h2) (hlist_app h3 (hlist_app h h0))).
              repeat rewrite hlist_split_hlist_app in H. eauto. } } }
        { clear - H3 H0.
          rewrite <- app_ass in H0. congruence. } }
      { forward. } }
  Qed.

End with_expr.

(*
Section demo.
  Notation funcForall := 1%positive.
  Notation funcImpl := 2%positive.

  Local Notation "'FORALL' t , x" :=
    (App (Func funcForall (t :: nil)) (Abs t x)) (at level 60).
  Local Notation "x ==> y" :=
    (App (App (Func funcImpl nil) x) y) (at level 50).


  Let lem_x_impl_x : @lemma expr :=
  {| vars := tvProp :: nil
   ; premises := Var 0 :: nil
   ; concl := Var 0
  |}.

  Let Plus x y := App (App (Func 1%positive nil) x) y.

  Let lem_plus_comm : @lemma expr :=
  {| vars := tvType 0 :: tvType 0 :: nil
   ; premises := nil
   ; concl := Equal (tvType 0)
                    (Plus (Var 0) (Var 1))
                    (Plus (Var 1) (Var 0))
  |}.

  Let lem_mp : @lemma expr :=
  {| vars := tvProp :: tvProp :: nil
   ; premises := Var 0 :: (Var 0 ==> Var 1) :: nil
   ; concl := Var 1
  |}.

  Let t_nat : type :=
    {| Impl := nat
     ; Eqb := fun _ _ => None
     ; Eqb_correct := fun _ _ => I
     |}.

  Let ts : types := t_nat :: nil.

  Let f_plus : function ts :=
    @F ts 0 (tvArr (tvType 0) (tvArr (tvType 0) (tvType 0)))
       plus.

  Let fs : functions ts := from_list (f_plus :: nil).

  Goal @lemmaD ts fs expr
       (fun us vs e =>
          @ExprD.exprD' ts fs us vs e tvProp) nil nil lem_plus_comm.
  Proof.
    unfold lemmaD; simpl; clear. eapply Plus.plus_comm.
  Qed.

End demo.
*)