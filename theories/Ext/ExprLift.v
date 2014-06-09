(** Lifting and lowering expressions for binder manipulation.
 **)
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprT.
Require Import MirrorCore.Ext.ExprTactics.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable ts : types.
  Variable func : Type.

  (** NOTE: This is a local definition, you should avoid using it directly **)
  Fixpoint lift' (s l : nat) (e : expr func) : expr func :=
    match e with
      | Var v =>
        if NPeano.ltb v s then e
        else Var (v + l)
      | Inj _ => e
      | App e e' => App (lift' s l e) (lift' s l e')
      | Abs t e => Abs t (lift' (S s) l e)
      | UVar u => e
    end.

  (** [lift s l e]
   ** skips [s] variables, and adds [l] new binders.
   **   us , vs ++ vs'' ===> us , vs ++ vs' ++ vs''
   ** where [length vs = s] and [length vs' = l]
   **)
  Definition lift (s l : nat) : expr func -> expr func :=
    match l with
      | 0 => fun x => x
      | _ => lift' s l
    end.

  (** NOTE: This is a local definition, you should avoid using it directly **)
  Fixpoint lower' (s l : nat) (e : expr func) : option (expr func) :=
    match e with
      | Var v =>
        if NPeano.ltb v s then Some e
        else if NPeano.ltb (v - s) l then None
             else Some (Var (v - l))
      | Inj _ => Some e
      | App e e' =>
        match lower' s l e , lower' s l e' with
          | Some e , Some e' => Some (App e e')
          | _ , _ => None
        end
      | Abs t e =>
        match lower' (S s) l e with
          | None => None
          | Some e => Some (Abs t e)
        end
      | UVar u => Some e
    end.

  (** [lower s l e]
   ** forgets binders and fails if they are mentioned
   **   us , vs ++ vs' ++ vs'' ===> us , vs ++ vs''
   ** where [length vs = s] and [length vs' = l]
   **)
  Definition lower s l : expr func -> option (expr func) :=
    match l with
      | 0 => @Some _
      | _ => lower' s l
    end.

  Theorem lower_lower' : forall e s l,
                           lower s l e = lower' s l e.
  Proof.
    unfold lower. destruct l; simpl; auto.
    clear; revert s.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ => rewrite <- H
           end; auto.
    rewrite <- Minus.minus_n_O. destruct (NPeano.ltb v s); reflexivity.
  Qed.

  Lemma lift'_0 : forall e s, lift' s 0 e = e.
  Proof.
    induction e; simpl; intros;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end; auto.
    { consider (NPeano.ltb v s); auto. }
  Qed.

  Lemma lift_lift' : forall s l e, lift s l e = lift' s l e.
  Proof.
    destruct l; simpl; intros; auto using lift'_0.
  Qed.

  Lemma lift'_lift' : forall e a b d,
    lift' a b (lift' a d e) = lift' a (b + d) e.
  Proof.
    induction e; simpl; intros; Cases.rewrite_all_goal; eauto.
    { remember (NPeano.ltb v a). destruct b0.
      { simpl. rewrite <- Heqb0. reflexivity. }
      { simpl.
        consider (NPeano.ltb v a); try congruence; intros.
        consider (NPeano.ltb (v + d) a); intros.
        { exfalso. omega. }
        { f_equal; omega. } } }
  Qed.

  Theorem lift_lift : forall e a b d,
    lift a b (lift a d e) = lift a (b + d) e.
  Proof.
    clear. unfold lift.
    destruct b; destruct d; simpl in *; auto.
    f_equal. omega.
    rewrite lift'_lift'.
    f_equal.
  Qed.

  Theorem lift_lift_1 : forall a b c t,
    lift a (b + c) t = lift (a + b) c (lift a b t).
  Proof.
    intros; repeat rewrite lift_lift'.
    revert a b c.
    induction t; simpl; intros; auto.
    { consider (NPeano.ltb v a); simpl; intros.
      { consider (NPeano.ltb v (a + b)); auto. intros. exfalso; omega. }
      { consider (NPeano.ltb (v + b) (a + b)); intros.
        exfalso; omega.
        f_equal. omega. } }
    { rewrite IHt1. rewrite IHt2. reflexivity. }
    { rewrite IHt. reflexivity. }
  Qed.

  Theorem lift_lower : forall e s l,
                         lower s l (lift s l e) = Some e.
  Proof.
    clear; intros.
    rewrite lower_lower'. rewrite lift_lift'.
    generalize dependent s. revert l.
    induction e; simpl; intros;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
           end;
    inv_all; subst; auto.
    { case_eq (NPeano.ltb v s); simpl; intros.
      { rewrite H. reflexivity. }
      { consider (NPeano.ltb v s); try congruence; intros.
        consider (NPeano.ltb (v + l) s); intros; try solve [ exfalso; omega ].
        consider (NPeano.ltb (v + l - s) l); intros; try solve [ exfalso; omega ].
        f_equal. f_equal.
        rewrite NPeano.Nat.add_sub. auto. } }
  Qed.

  Theorem lower_lift : forall e e' s l,
                         lower s l e = Some e' ->
                         e = lift s l e'.
  Proof.
    intros.
    rewrite lower_lower' in H. rewrite lift_lift'.
    generalize dependent s. revert l.
    revert e'.
    induction e; simpl; intros;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
           end;
    inv_all; subst; auto.
    consider (NPeano.ltb v s); intros.
    { inv_all. subst. simpl. consider (NPeano.ltb v s); intros; auto.
      exfalso; omega. }
    { consider (NPeano.ltb (v - s) l); try congruence; intros.
      inv_all; subst. simpl. consider (NPeano.ltb (v - l) s); intros.
      exfalso. omega. f_equal. rewrite NPeano.Nat.sub_add. auto. omega. }
  Qed.

  Variable RSym_func : RSym (typD ts) func.
  Let Expr_expr : Expr (typD ts) (expr func) := Expr_expr _.
  Local Existing Instance Expr_expr.

  Lemma typeof_expr_lift : forall us vs vs' vs'' e,
    ExprT.typeof_expr us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) =
    ExprT.typeof_expr us (vs ++ vs'') e.
  Proof.
    clear. intros. rewrite lift_lift'.
    revert vs.
    induction e; simpl; intros;
    repeat match goal with
             | H : _ |- _ =>
               erewrite H
           end; auto.
    { consider (NPeano.ltb v (length vs)); simpl; intros;
      repeat ((rewrite nth_error_app_L by omega) ||
                                                 (rewrite nth_error_app_R by omega)); auto.
      f_equal. omega. }
    { change (t :: vs ++ vs' ++ vs'') with
      ((t :: vs) ++ vs' ++ vs'').
      rewrite IHe. auto. }
  Qed.


  Theorem typeof_expr_lower : forall (us : EnvI.tenv typ)
                                     (e : expr func)
     (vs vs' vs'' : list typ)
     (e1 : expr func),
   lower (length vs) (length vs') e = Some e1 ->
   ExprT.typeof_expr us (vs ++ vs' ++ vs'') e =
   ExprT.typeof_expr us (vs ++ vs'') e1.
  Proof.
    clear.
    do 6 intro. rewrite lower_lower'.
    revert e1 vs vs' vs''.
    induction e; simpl in *; intros; inv_all; subst; simpl;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
             | |- _ => progress (inv_all; subst)
           end; auto.
    { consider (NPeano.ltb v (length vs)); intros.
      inv_all; subst; simpl. repeat rewrite nth_error_app_L by auto. reflexivity.
      consider (NPeano.ltb (v - length vs) (length vs')); intros; inv_all; subst;
      try congruence. simpl.
      repeat rewrite nth_error_app_R by omega. f_equal. omega. }
    { consider (lower' (S (length vs)) (length vs') e); try congruence; intros.
      inv_all; subst.
      change (t :: vs ++ vs' ++ vs'') with ((t :: vs) ++ vs' ++ vs'').
      erewrite IHe by eauto. reflexivity. }
  Qed.

  Lemma nth_error_length_lt
  : forall {T} (ls : list T) n val,
      nth_error ls n = Some val ->
      n < length ls.
  Proof.
    induction ls; destruct n; simpl; intros; auto.
    { inversion H. }
    { inversion H. }
    { omega. }
    { apply Lt.lt_n_S. eauto. }
  Qed.

  Lemma exprD'_lower
  : forall us vs vs' vs'' e e0 t,
      lower (length vs) (length vs') e = Some e0 ->
      match exprD' us (vs ++ vs' ++ vs'') e t
          , exprD' us (vs ++ vs'') e0 t
      with
        | None , None => True
        | Some l , Some r =>
          forall US VS VS' VS'',
            l US (hlist_app VS (hlist_app VS' VS'')) =
            r US (hlist_app VS VS'')
        | _ , _ => False
      end.
  Proof.
    Opaque exprD exprD'.
    intros us vs vs' vs'' e e0 t H.
    rewrite lower_lower' in H.
    revert H; revert t; revert e0; revert vs; revert vs'.
    induction e; simpl; intros; autorewrite with exprD_rw in *;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
             | |- _ => progress (inv_all; subst)
             | |- _ => progress ( autorewrite with exprD_rw in * )
           end; auto.
    { repeat match goal with
               | _ : match ?X with _ => _ end = _ |- _ =>
                 consider X; intros; inv_all; subst; try congruence
             end;
      try rewrite exprD'_Var.
      { assert (nth_error (vs ++ vs' ++ vs'') v = nth_error (vs ++ vs'') v).
        { repeat rewrite nth_error_app_L by auto. auto. }
        symmetry in H0.
        assert (forall a b c, hlist_nth (hlist_app a (hlist_app b c)) v =
                              match H0 in _ = z return match z with
                                                         | None => unit
                                                         | Some v => typD ts nil v
                                                       end
                              with
                                | eq_refl => hlist_nth (hlist_app a c) v
                              end).
        { intros.
          generalize dependent (hlist_app b c). intros.
          generalize dependent (vs' ++ vs''). intros.
          repeat rewrite hlist_nth_hlist_app; eauto with typeclass_instances.
          generalize (cast2 vs vs'' v).
          generalize (cast1 vs vs'' v).
          generalize (cast2 vs l v).
          generalize (cast1 vs l v).
          gen_refl.
          repeat match goal with
                   | |- appcontext [ @hlist_nth ?X ?Y ?Z ?A ?B ] =>
                     generalize (@hlist_nth X Y Z A B)
                 end.
          remember (nth_error vs v); destruct e; intros.
          { uip_all. clear.
            generalize e4. generalize e6. rewrite <- e4.
            intros. uip_all. auto. }
          { exfalso. clear - H Heqe.
            symmetry in Heqe. apply nth_error_length_ge in Heqe.
            omega. } }
        generalize H.
        eapply nth_error_get_hlist_nth_appL with (F := typD ts nil) (tvs' := vs'') in H; eauto with typeclass_instances.
        intro.
        eapply nth_error_get_hlist_nth_appL with (F := typD ts nil) (tvs' := vs' ++ vs'') in H2; eauto with typeclass_instances.

        forward_reason.
        repeat match goal with
                 | H : ?X = _ |- context [ ?Y ] =>
                   change Y with X ; rewrite H
                 | H : ?X = _ , H' : ?Y = _ |- _ =>
                   change Y with X in H' ; rewrite H in H'
               end.
        forward. simpl in *. inv_all; subst.
        forward. f_equal.
        rewrite H6. apply H7. }
      { assert (v >= length vs) by omega.
        assert (v - length vs' >= length vs) by omega.
        match goal with
          | |- match match ?X with _ => _ end with _ => _ end =>
            consider X ; intros
        end.
        { eapply nth_error_get_hlist_nth_appR with (tvs' := vs' ++ vs'') in H1; eauto with typeclass_instances.
          match goal with
            | |- context [ @EnvI.nth_error_get_hlist_nth ?A ?B ?C ?D ] =>
              consider (@EnvI.nth_error_get_hlist_nth A B C D); intros
          end.
          { eapply nth_error_get_hlist_nth_appR with (tvs' := vs'') in H2; eauto with typeclass_instances.
            assert (v - length vs' >= length vs) by omega.
            eapply nth_error_get_hlist_nth_appR with (tvs' := vs'') in H5; eauto with typeclass_instances.
            assert (v - length vs >= length vs') by omega.
            forward_reason.
            eapply nth_error_get_hlist_nth_appR with (tvs' := vs'') in H6; eauto with typeclass_instances.
            replace (v - length vs - length vs') with (v - length vs' - length vs) in * by omega.
            forward_reason.
            forward. simpl in *. subst.
            repeat match goal with
                     | H : ?X = _ , H' : ?Y = _ |- _ =>
                       change Y with X in H' ; rewrite H in H'
                   end.
            inv_all; subst. forward.
            f_equal. Cases.rewrite_all_goal. reflexivity. }
          { apply EnvI.nth_error_get_hlist_nth_None in H4.
            apply EnvI.nth_error_get_hlist_nth_Some in H3.
            exfalso.
            apply nth_error_length_ge in H4. rewrite app_length in H4.
            destruct H3. clear H3 H1.
            apply nth_error_length_lt in x.
            repeat rewrite app_length in x. omega. } }
        { apply EnvI.nth_error_get_hlist_nth_None in H3.
          apply nth_error_length_ge in H3.
          repeat rewrite app_length in H3.
          match goal with
            | |- context [ @EnvI.nth_error_get_hlist_nth ?A ?B ?C ?D ] =>
              consider (@EnvI.nth_error_get_hlist_nth A B C D); intros
          end; auto.
          exfalso.
          apply EnvI.nth_error_get_hlist_nth_Some in H4.
          destruct H4. clear H4.
          apply nth_error_length_lt in x.
          rewrite app_length in x. omega. } } }
    { forward. }
    { erewrite typeof_expr_lower by (rewrite lower_lower'; eassumption).
      repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
             end.
      specialize (IHe1 _ _ _ (tyArr t0_1 t0_2) H).
      specialize (IHe2 _ _ _ t0_1 H0).
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X
             end; destruct (typ_cast_typ ts nil t0_2 t); auto.
      intros.
      f_equal. rewrite IHe1. f_equal. auto. }
    { destruct t0; auto.
      repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
             end.
      specialize (IHe vs' (t :: vs) _ t0_2 H).
      simpl in *.
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X
             end; auto.
      intros.
      apply functional_extensionality; intros.
      simpl in *.
      apply (IHe US (Hcons (F := typD ts nil) (p (fun x => x) x) VS) VS' VS''). }
    { forward. }
    Transparent exprD exprD'.
  Qed.

  Theorem exprD_lower : forall us vs vs' vs'' e e0 t,
                         lower (length vs) (length vs') e = Some e0 ->
                         exprD us (vs ++ vs' ++ vs'') e t =
                         exprD us (vs ++ vs'') e0 t.
  Proof.
    unfold exprD. intros.
    repeat rewrite EnvI.split_env_app.
    repeat match goal with
             | |- context [ EnvI.split_env ?X ] =>
               consider (EnvI.split_env X); intros
           end.
    cutrewrite (length vs = length x0) in H.
    cutrewrite (length vs' = length x1) in H.
    specialize (@exprD'_lower x x0 x1 x2 e e0 t H).
    intros.
    unfold ExprI.exprD'. simpl.
    repeat match goal with
             | _ : match ?X with _ => _ end |- _ =>
               destruct X
           end; intuition try congruence.
    f_equal. eauto.
    rewrite EnvI.split_env_length. rewrite H2. reflexivity.
    rewrite EnvI.split_env_length. rewrite H1. reflexivity.
  Qed.

  Lemma exprD'_lift : forall us vs vs' vs'' e t,
    match exprD' us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) t
        , exprD' us (vs ++ vs'') e t
    with
      | None , None => True
      | Some l , Some r =>
        forall US VS VS' VS'',
          l US (hlist_app VS (hlist_app VS' VS'')) =
          r US (hlist_app VS VS'')
      | _ , _ => False
    end.
  Proof.
    Opaque exprD exprD'.
    intros us vs vs' vs'' e t.
    rewrite lift_lift'.
    revert t; revert vs; revert vs'.
    induction e; simpl; intros; autorewrite with exprD_rw in *;
    repeat match goal with
             | H : match ?X with _ => _ end = _ |- _ =>
               (consider X; try congruence); [ intros ]
             | H : _ |- _ => erewrite H by eauto
             | |- _ => progress (inv_all; subst)
             | |- _ => progress ( autorewrite with exprD_rw in * )
           end.
    { consider (NPeano.ltb v (length vs)); intros.
      { autorewrite with exprD_rw.
        generalize H.
        intro.
        eapply nth_error_get_hlist_nth_appL with (tvs' := vs' ++ vs'') (F := typD ts nil) in H; eauto with typeclass_instances.
        eapply nth_error_get_hlist_nth_appL with (tvs' := vs'') (F := typD ts nil) in H0; eauto with typeclass_instances.
        forward_reason.
        repeat match goal with
                 | H : ?X = _ , H' : ?Y = _ |- _ =>
                   change Y with X in H' ; rewrite H in H'
                 | H : ?X = _ |- context [ ?Y ] =>
                   change Y with X ; rewrite H
               end.
        forward; inv_all; subst. simpl in *. subst.
        forward. f_equal.
        Cases.rewrite_all_goal. reflexivity. }
      { autorewrite with exprD_rw.
        match goal with
          | |- match match ?X with _ => _ end with _ => _ end =>
            consider X; intros
        end.
        { assert (v >= length vs) by omega.
          match goal with
            | |- context [ @EnvI.nth_error_get_hlist_nth ?A ?B ?C ?D ] =>
              consider (@EnvI.nth_error_get_hlist_nth A B C D); intros
          end.
          { eapply nth_error_get_hlist_nth_appR in H1; eauto with typeclass_instances.
            eapply nth_error_get_hlist_nth_appR in H0; eauto with typeclass_instances.
            2: omega.
            forward_reason.
            eapply nth_error_get_hlist_nth_appR in H0; eauto with typeclass_instances.
            2: omega.
            eapply nth_error_get_hlist_nth_appR in H2; eauto with typeclass_instances.
            2: omega.
            forward_reason. simpl in *. forward.
            simpl in *; subst.
            replace (v + length vs' - length vs - length vs') with (v - length vs) in * by omega.
            repeat match goal with
                     | H : ?X = _ , H' : ?Y = _ |- _ =>
                       change Y with X in H' ; rewrite H in H'
                     | H : ?X = _ |- context [ ?Y ] =>
                       change Y with X ; rewrite H
                   end.
            inv_all; subst.
            forward. f_equal. Cases.rewrite_all_goal. reflexivity. }
          { exfalso.
            apply EnvI.nth_error_get_hlist_nth_Some in H0.
            destruct H0. clear H0.
            apply EnvI.nth_error_get_hlist_nth_None in H2.
            apply nth_error_length_lt in x.
            apply nth_error_length_ge in H2.
            repeat rewrite app_length in *.
            omega. } }
        { forward.
          apply EnvI.nth_error_get_hlist_nth_None in H0.
          apply EnvI.nth_error_get_hlist_nth_Some in H2.
          destruct H2.
          clear - x0 H0 H.
          apply nth_error_length_ge in H0.
          apply nth_error_length_lt in x0.
          repeat rewrite app_length in *.
          omega. } } }
    { repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
               | |- match match ?x with _ => _ end with _ => _ end =>
                 solve [ destruct x; auto ]
             end. }
    { rewrite <- lift_lift'.
      rewrite typeof_expr_lift.
      repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
               | |- match match ?x with _ => _ end with _ => _ end =>
                 solve [ destruct x; auto ]
             end.
      specialize (IHe1 vs' vs (tyArr t0_1 t0_2)).
      specialize (IHe2 vs' vs t0_1).
      simpl in *. rewrite lift_lift' in *.
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X; intuition
             end; eauto.
      destruct (typ_cast_typ ts nil t0_2 t); auto.
      intros. rewrite IHe1. rewrite IHe2. reflexivity. }
    { repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
               | |- match match ?x with _ => _ end with _ => _ end =>
                 solve [ destruct x; auto ]
             end.
      specialize (IHe vs' (t :: vs) t0_2).
      simpl in *.
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X; intuition
             end; eauto.
      eapply functional_extensionality.
      intros. eapply (IHe US (Hcons (F := typD ts nil) (p (fun x=>x) x) VS)). }
    { repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
               | |- match match ?x with _ => _ end with _ => _ end =>
                 solve [ destruct x; auto ]
             end. }
    Transparent exprD exprD'.
  Qed.

  Theorem exprD_lift : forall us vs vs' vs'' e t,
    exprD us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) t =
    exprD us (vs ++ vs'') e t.
  Proof.
    unfold exprD. intros.
    repeat rewrite EnvI.split_env_app.
    repeat match goal with
             | |- context [ EnvI.split_env ?X ] =>
               consider (EnvI.split_env X); intros
           end.
    cutrewrite (length vs = length x0).
    cutrewrite (length vs' = length x1).
    specialize (@exprD'_lift x x0 x1 x2 e t).
    intros.
    unfold ExprI.exprD'; simpl.
    repeat match goal with
             | _ : match ?X with _ => _ end |- _ =>
               destruct X
           end; intuition try congruence.
    f_equal. eauto.
    rewrite EnvI.split_env_length. rewrite H1. reflexivity.
    rewrite EnvI.split_env_length. rewrite H0. reflexivity.
  Qed.

End typed.

Section vars_to_uvars.
  Require Import MirrorCore.EnvI.
  Variable ts : types.
  Variable func : Type.

  Fixpoint vars_to_uvars (e : expr func) (skip add : nat) : expr func :=
    match e with
      | Var v =>
        if v ?[ lt ] skip then Var v
        else UVar (v - skip + add)
      | UVar _
      | Inj _ => e
      | App l r => App (vars_to_uvars l skip add) (vars_to_uvars r skip add)
      | Abs t e => Abs t (vars_to_uvars e (S skip) add)
    end.

  Theorem vars_to_uvars_typeof_expr (Z : SymI.RSym (typD ts) func)
  : forall tus e tvs tvs' t,
      typeof_expr tus (tvs ++ tvs') e = Some t ->
      typeof_expr (tus ++ tvs') tvs (vars_to_uvars e (length tvs) (length tus))
      = Some t.
  Proof.
    clear. induction e; simpl; intros; auto.
    { consider (v ?[ lt ] length tvs); intros.
      { simpl. rewrite ListNth.nth_error_app_L in H; auto. }
      { simpl. rewrite ListNth.nth_error_app_R in H; auto. 2: omega.
        rewrite ListNth.nth_error_app_R; try omega.
        replace (v - length tvs + length tus - length tus) with (v - length tvs)
          by omega.
        auto. } }
    { forward. erewrite IHe1; eauto. erewrite IHe2; eauto. }
    { forward. eapply (IHe (t :: tvs) tvs') in H.
      simpl in *.
      rewrite H in *. auto. }
    { apply ListNth.nth_error_weaken; auto. }
  Qed.

  Lemma nth_error_get_hlist_nth_rwR
  : forall {T} (F : T -> _) tus tvs' n,
      n >= length tus ->
      match nth_error_get_hlist_nth F tvs' (n - length tus) with
        | None => True
        | Some (existT t v) =>
          exists val,
          nth_error_get_hlist_nth F (tus ++ tvs') n = Some (@existT _ _ t val) /\
          forall a b,
            v a = val (hlist_app b a)
      end.
  Proof.
    clear. intros.
    forward. subst.
    consider (nth_error_get_hlist_nth F (tus ++ tvs') n).
    { intros.
      eapply nth_error_get_hlist_nth_appR in H; eauto.
      destruct s. simpl in *. rewrite H1 in *.
      destruct H as [ ? [ ? ? ] ]. inv_all; subst.
      eexists; split; eauto. }
    { intros.
      exfalso.
      eapply nth_error_get_hlist_nth_Some in H1.
      eapply nth_error_get_hlist_nth_None in H0.
      forward_reason. simpl in *.
      eapply ListNth.nth_error_length_ge in H0.
      clear H1. eapply nth_error_length_lt in x0.
      rewrite app_length in H0. omega. }
  Qed.

  Theorem vars_to_uvars_exprD' (Z : SymI.RSym (typD ts) func)
  : forall tus e tvs t tvs' val,
      exprD' tus (tvs ++ tvs') e t = Some val ->
      exists val',
        exprD' (tus ++ tvs') tvs (vars_to_uvars e (length tvs) (length tus)) t = Some val' /\
        forall us vs' vs, val us (HList.hlist_app vs vs') =
                          val' (HList.hlist_app us vs') vs.
  Proof.
    clear. induction e; simpl; intros.
    { consider (v ?[ lt ] length tvs); intros.
      { generalize (@exprD'_Var_App_L _ _ _ tus tvs' t tvs v H0).
        rewrite H. intros; forward.
        red_exprD. forward.
        eexists; split; eauto.
        inv_all; subst. eauto. }
      { red_exprD.
        forward. inv_all; subst.
        eapply nth_error_get_hlist_nth_appR in H1; [ | omega ].
        simpl in H1.
        forward_reason.
        assert (v - length tvs + length tus >= length tus) by omega.
        eapply nth_error_get_hlist_nth_rwR
        with (F := typD ts nil) in H2.
        replace (v - length tvs + length tus - length tus)
        with (v - length tvs) in H2 by omega.
        revert H2. instantiate (1 := tvs').
        match goal with
          | H : ?X = _ |- context [ ?Y ] =>
            change Y with X; rewrite H
        end.
        destruct 1 as [ ? [ ? ? ] ].
        match goal with
          | H : ?X = _ |- context [ ?Y ] =>
            change Y with X; rewrite H
        end.
        rewrite typ_cast_typ_refl.
        eexists; split; eauto. simpl.
        intros. rewrite H1. auto. } }
    { red_exprD.
      forward.
      inv_all; subst.
      eexists; split; eauto. }
    { red_exprD.
      forward. inv_all; subst.
      eapply vars_to_uvars_typeof_expr in H0.
      eapply IHe1 in H1.
      eapply IHe2 in H2. forward_reason.
      Cases.rewrite_all_goal.
      rewrite typ_cast_typ_refl.
      eexists; split; eauto.
      intros.
      rewrite H2. rewrite H3. reflexivity. }
    { red_exprD.
      forward. inv_all; subst.
      destruct (IHe (t :: tvs) _ _ _ H1) as [ ? [ ? ? ] ].
      simpl in *. rewrite H.
      eexists; eauto; split; eauto.
      intros. simpl.
      eapply functional_extensionality. intros.
      rewrite <- H0. simpl. reflexivity. }
    { red_exprD.
      forward. inv_all; subst.
      eapply nth_error_get_hlist_nth_weaken in H0.
      simpl in *. forward_reason.
      rewrite H. rewrite typ_cast_typ_refl.
      eexists; split; eauto. intros. apply H0. }
  Qed.

End vars_to_uvars.