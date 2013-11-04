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
Require Import MirrorCore.Ext.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section with_expr.
  Variable ts : types.
  Variable fs : functions ts.
  Variable conclusion : Type.
  Variable conclusionD : env (typD ts) -> forall vs : list typ,
                                            conclusion ->
                                            option (hlist (typD ts nil) vs -> Prop).
  Hypothesis conclusionD_weaken : forall us tvs c val,
    conclusionD us tvs c = Some val ->
    forall us' tvs',
      exists val',
        conclusionD (us ++ us') (tvs ++ tvs') c = Some val' /\
        forall x y,
          val x = val' (hlist_app x y).

  Record lemma : Type :=
  { vars : list typ
  ; premises : list expr
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

  Definition lemmaD (us vs : env (typD ts)) (l : lemma) : Prop :=
    let (tvs,vs) := split_env vs in
    match mapT (fun e =>
                  ExprD.exprD' fs us (l.(vars) ++ tvs) e tvProp) l.(premises)
        , conclusionD us (l.(vars) ++ tvs) l.(concl)
    with
      | Some prems , Some concl =>
        @foralls l.(vars) (fun h =>
          let h := hlist_app h vs in
          List.fold_right
            (fun (x : hlist (typD ts nil) (l.(vars) ++ tvs) -> Prop) (y : Prop) =>
               (x h) -> y)
            (concl h)
            prems)

      | _ , _ => False
    end.

  Lemma lemmaD_weaken : forall us vs l us' vs',
    lemmaD us vs l ->
    lemmaD (us ++ us') (vs ++ vs') l.
  Proof.
    unfold lemmaD; destruct l; simpl.
    intros. rewrite split_env_app. destruct (split_env vs).
    destruct (split_env vs'). clear - H conclusionD_weaken.
    forward.
    match goal with
      | |- match ?X with _ => _ end =>
        assert (exists l',
                  X = Some l' /\
                  forall (z : hlist (typD ts nil) (vars0 ++ x))
                         (z'' : hlist (typD ts nil) x0),
                    Forall2 (fun (g : _ -> Prop) (f : _ -> Prop) =>
                               f (match @app_ass _ vars0 x x0 in _ = t
                                        return hlist _ t
                                  with
                                    | eq_refl => hlist_app z z''
                                  end) ->
                               g z) l l')
    end.
    { clear - H. revert H.
      assert (forall (z : hlist (typD ts nil) (vars0 ++ x))
        (z'' : hlist (typD ts nil) x0),
      Forall2
        (fun (g : hlist (typD ts nil) (vars0 ++ x) -> Prop)
             (x1 : hlist (typD ts nil) (vars0 ++ x ++ x0) -> Prop) =>
         x1 (match @app_ass _ vars0 x x0 in _ = t
                   return hlist _ t
             with
               | eq_refl => hlist_app z z''
             end) -> g z) nil nil) by intuition.
      match goal with
        | _ : forall x z,
                Forall2 _ _ ?A
                |- context [ Some ?B ] =>
          change B with A ; generalize dependent A
      end.
      do 2 intro.
      match goal with
        | _ : forall x z,
                Forall2 _ ?A _
                |- context [ Some ?B ] =>
          change B with A ; generalize dependent A
      end.
      revert l l0.
      induction premises0; simpl; intros.
      { inv_all; subst.
        eexists; split; try reflexivity. intuition. }
      { forward. inv_all; subst.
        eapply IHpremises0 in H1; clear IHpremises0; eauto. clear H.
        destruct H1; intuition.
        generalize (exprD'_weaken fs us x0 us' a tvProp (vars0 ++ x)).
        forward. inv_all. subst.
        generalize dependent vars0. intro vars0.
        generalize (app_assoc_reverse vars0 x x0).
        rewrite <- app_ass.
        intros.
        rewrite H3. eexists; split; eauto.
        intros. constructor; eauto.
        rewrite (UIP_refl _).
        rewrite <- H4. auto. } }
    { destruct H2. intuition.
      Cases.rewrite_all.
      eapply conclusionD_weaken with (us' := us') (tvs' := x0) in H0.
      destruct H0; intuition.
      clear H3 H.
      consider (conclusionD (us ++ us') (vars0 ++ x ++ x0) concl0).
      { intros.
        assert (forall a b c,
                  x2 (hlist_app (hlist_app a b) c) =
                  P0 (hlist_app a (hlist_app b c))).
        { clear - H2 H.
          intros. rewrite hlist_app_assoc'; eauto with typeclass_instances.
          generalize (hlist_app a b).
          generalize (app_assoc_reverse vars0 x x0).
          generalize dependent x2. generalize dependent P0.
          rewrite <- app_ass. intuition.
          rewrite H in *. inv_all; subst.
          uip_all. reflexivity. }
        { rewrite foralls_sem in H1.
          eapply foralls_sem.
          intro. specialize (H1 h1).
          specialize (H0 h1 h h0).
          specialize (H5 (hlist_app h1 h) h0).
          specialize (H4 (hlist_app h1 h) h0).
          repeat match goal with
                   | H : _ = ?X |- fold_right _ ?Y _ =>
                     change Y with X ; rewrite <- H ; clear H
                 end.
          generalize dependent (P (hlist_app h1 h)).
          clear - H4. induction H4; simpl; auto.
          { intros.
            generalize dependent (app_assoc_reverse vars0 x x0).
            uip_all. eapply IHForall2.
            eapply H1. eapply H.
            revert H0. rewrite hlist_app_assoc'; eauto with typeclass_instances.
            clear. generalize (app_assoc_reverse vars0 x x0).
            generalize e. do 2 intro.
            match goal with
              | |- _ ?X -> _ ?Y =>
                replace X with Y; try reflexivity
            end.
            intro X; apply X.
            generalize e0. generalize e1.
            rewrite <- e1. intros. uip_all. reflexivity. } } }
      { clear - H2. rewrite <- app_ass.
        rewrite H2. congruence. } }
  Qed.

End with_expr.

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