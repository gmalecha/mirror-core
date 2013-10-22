Require Import List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.EqDep.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.

(** TODO : Temporary **)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable ts : types.
  Variable func : Type.

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

  Definition lift (s l : nat) : expr func -> expr func :=
    match l with
      | 0 => fun x => x
      | _ => lift' s l
    end.

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

  Fixpoint mentionsU (u : nat) (e : expr func) {struct e} : bool :=
    match e with
      | Var _
      | Inj _ => false
      | UVar u' => EqNat.beq_nat u u'
      | App f e => if mentionsU u f then true else mentionsU u e
      | Abs _ e => mentionsU u e
    end.

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

  Variable RFunc_func : RFunc (typD ts) func.

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

  Lemma typeof_env_app : forall (a b : EnvI.env (typD ts)),
    EnvI.typeof_env (a ++ b) = EnvI.typeof_env a ++ EnvI.typeof_env b.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_app. reflexivity.
  Qed.
  Lemma typeof_env_length : forall (a : EnvI.env (typD ts)),
    length (EnvI.typeof_env a) = length a.
  Proof.
    unfold EnvI.typeof_env; intros.
    rewrite map_length. reflexivity.
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

  Lemma exprD'_lower : forall us vs vs' vs'' e e0 t,
                         lower (length vs) (length vs') e = Some e0 ->
                         match exprD' us (vs ++ vs' ++ vs'') e t
                             , exprD' us (vs ++ vs'') e0 t
                         with
                           | None , None => True
                           | Some l , Some r =>
                             forall VS VS' VS'',
                               l (hlist_app VS (hlist_app VS' VS'')) =
                               r (hlist_app VS VS'')
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
        revert H0 H1. clear.
        change (
            let zzz e := hlist_nth e v in
            let zzz' e := hlist_nth e v in
            forall H0 : nth_error (vs ++ vs'') v = nth_error (vs ++ vs' ++ vs'') v,
              (forall (a : hlist (typD ts nil) vs) (b : hlist (typD ts nil) vs')
                      (c : hlist (typD ts nil) vs''),
                 zzz (hlist_app a (hlist_app b c)) =
                 match
                   H0 in (_ = z)
                   return match z with
                            | Some v0 => typD ts nil v0
                            | None => unit
                          end
                 with
                   | eq_refl => zzz' (hlist_app a c)
                 end) ->
            match
              match
                nth_error (vs ++ vs' ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some
                          (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t0 => typD ts nil t0
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (zzz e))
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
              end eq_refl
            with
              | Some l =>
                match
                  match
                    nth_error (vs ++ vs'') v as z
                    return
                    (z = nth_error (vs ++ vs'') v ->
                     option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
                  with
                    | Some z =>
                      fun pf : Some z = nth_error (vs ++ vs'') v =>
                        match typ_cast_typ ts (fun x : Type => x) nil z t with
                          | Some cast =>
                            Some
                              (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                                 match
                                   pf in (_ = t'')
                                   return
                                   (match t'' with
                                      | Some t0 => typD ts nil t0
                                      | None => unit
                                    end -> typD ts nil t)
                                 with
                                   | eq_refl => fun x : typD ts nil z => cast x
                                 end (zzz' e))
                          | None => None
                        end
                    | None => fun _ : None = nth_error (vs ++ vs'') v => None
                  end eq_refl
                with
                  | Some r =>
                    forall (VS : hlist (typD ts nil) vs)
                           (VS' : hlist (typD ts nil) vs')
                           (VS'' : hlist (typD ts nil) vs''),
                      l (hlist_app VS (hlist_app VS' VS'')) = r (hlist_app VS VS'')
                  | None => False
                end
              | None =>
                match
                  match
                    nth_error (vs ++ vs'') v as z
                    return
                    (z = nth_error (vs ++ vs'') v ->
                     option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
                  with
                    | Some z =>
                      fun pf : Some z = nth_error (vs ++ vs'') v =>
                        match typ_cast_typ ts (fun x : Type => x) nil z t with
                          | Some cast =>
                            Some
                              (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                                 match
                                   pf in (_ = t'')
                                   return
                                   (match t'' with
                                      | Some t0 => typD ts nil t0
                                      | None => unit
                                    end -> typD ts nil t)
                                 with
                                   | eq_refl => fun x : typD ts nil z => cast x
                                 end (zzz' e))
                          | None => None
                        end
                    | None => fun _ : None = nth_error (vs ++ vs'') v => None
                  end eq_refl
                with
                  | Some _ => False
                  | None => True
                end
            end).
        gen_refl.
        intros. clearbody zzz. clearbody zzz'.
        destruct (nth_error (vs ++ vs'') v);
        destruct (nth_error (vs ++ vs' ++ vs'') v); try congruence; auto.
        inv_all; subst.  inversion H0. subst.
        destruct (typ_cast_typ ts (fun x => x) nil t1 t); auto.
        intros. uip_all. specialize (H VS VS' VS'').
        f_equal. etransitivity. eapply H.
        uip_all. reflexivity. }
      { assert (nth_error (vs ++ vs' ++ vs'') v = nth_error (vs ++ vs'') (v - length vs')).
        { repeat rewrite nth_error_app_R by omega. f_equal. omega. }
        symmetry in H1.
        assert (forall a b c, hlist_nth (hlist_app a (hlist_app b c)) v =
                              match H1 in _ = z return match z with
                                                         | None => unit
                                                         | Some v => typD ts nil v
                                                       end
                              with
                                | eq_refl => hlist_nth (hlist_app a c) (v - length vs')
                              end).
        { intros.
          repeat rewrite hlist_nth_hlist_app; eauto with typeclass_instances.
          repeat match goal with
                   | |- appcontext [ cast2 ?X ?Y ?Z ] =>
                     generalize dependent (cast2 X Y Z)
                   | |- appcontext [ cast1 ?X ?Y ?Z ] =>
                     generalize dependent (cast1 X Y Z)
                 end.
          assert (v - length vs - length vs' = v - length vs' - length vs).
          { omega. }
          repeat match goal with
                   | |- appcontext [ @hlist_nth ?X ?Y ?Z ?A ] =>
                     generalize (@hlist_nth X Y Z A)
                 end.
          rewrite H2. intros.
          generalize (y (v - length vs' - length vs)).
          gen_refl.
          generalize (y1 v).
          generalize (y0 (v - length vs)).
          generalize (y1 (v - length vs')).
          clear H2 y y0 y1.
          remember (nth_error vs v). destruct e5.
          { exfalso.
            clear - Heqe5 H. rewrite nth_error_past_end in Heqe5.
            congruence. omega. }
          { intros. generalize (e4 e6).
            clear - H H0. generalize H1. rewrite <- H1.
            uip_all. gen_refl. revert y0.
            remember (nth_error vs' (v - length vs)).
            destruct e4.
            { exfalso. clear - H H0 Heqe4.
              rewrite <- (app_nil_r vs') in Heqe4.
              rewrite nth_error_app_R in Heqe4. rewrite nth_error_nil in *. congruence.
              omega. }
            { intros.
              remember (nth_error vs (v - length vs')).
              destruct e8.
              { exfalso. clear - Heqe8 H0 H.
                rewrite <- (app_nil_r vs) in Heqe8.
                rewrite nth_error_app_R in Heqe8 by omega.
                rewrite nth_error_nil in Heqe8. congruence. }
              { generalize (e2 e4).
                uip_all. clear.
                generalize e8. generalize e9.
                generalize y2. rewrite e8. intros.
                uip_all. auto. } } } }
        { do 2 match goal with
                 | |- match ?X with _ => _ end =>
                   let z := fresh in
                   remember X as z; destruct z
               end; auto.
          { intros.
            revert HeqH0 HeqH3.
            gen_refl.
            intros.
            specialize (H2 VS VS' VS'').
            match goal with
              | _ : context [ ?X ] |- _ ?Z = _ =>
                change Z with X; generalize dependent X
            end; intros.
            match goal with
              | _ : context [ ?X ] |- _ = _ ?Z =>
                change Z with X; generalize dependent X
            end; intros.
            revert HeqH3 HeqH0. revert H2.
            change (
                let zzz e := hlist_nth e v in
                let zzz' e := hlist_nth e (v - length vs') in
                zzz h = match
                  H1 in (_ = z)
                  return match z with
                           | Some v0 => typD ts nil v0
                           | None => unit
                         end
                with
                  | eq_refl => zzz' h0
                end ->
                Some t0 =
                match
                  nth_error (vs ++ vs' ++ vs'') v as z
                  return
                  (z = nth_error (vs ++ vs' ++ vs'') v ->
                   option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some
                            (fun e1 : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t2 => typD ts nil t2
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (zzz e1))
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
                end e ->
                Some t1 =
                match
                  nth_error (vs ++ vs'') (v - length vs') as z
                  return
                  (z = nth_error (vs ++ vs'') (v - length vs') ->
                   option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs'') (v - length vs') =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some
                            (fun e1 : hlist (typD ts nil) (vs ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t2 => typD ts nil t2
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (zzz' e1))
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs'') (v - length vs') => None
                end e0 -> t0 h = t1 h0
              ).
            intros zzz zzz'.
            clearbody zzz zzz'.
            remember (nth_error (vs ++ vs' ++ vs'') v).
            destruct e1; try solve [ intros; congruence ].
            remember (nth_error (vs ++ vs'') (v - length vs')).
            destruct e1; try solve [ intros; congruence ].
            inversion H1. subst.
            destruct (typ_cast_typ ts (fun x : Type => x) nil t2 t); try congruence.
            intros; inv_all; subst. uip_all. auto. }
          { clear - HeqH3 HeqH0 H H0 H1.
            revert HeqH3 HeqH0.
            change (
                let XXX z (pf : Some z = nth_error (vs ++ vs' ++ vs'') v) cast := (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e v)) in
                let XXX' z (pf : Some z = nth_error (vs ++ vs'') (v - length vs'))  cast :=  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e (v - length vs'))) in
                Some t0 =
                match
                  nth_error (vs ++ vs' ++ vs'') v as z
                  return
                  (z = nth_error (vs ++ vs' ++ vs'') v ->
                   option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (XXX z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
                end eq_refl ->
                None =
                match
                  nth_error (vs ++ vs'') (v - length vs') as z
                  return
                  (z = nth_error (vs ++ vs'') (v - length vs') ->
                   option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs'') (v - length vs') =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (XXX' z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs'') (v - length vs') => None
                end eq_refl -> False).
            intros XXX XXX'; clearbody XXX XXX'; revert XXX XXX'.
            rewrite H1. gen_refl.
            intros.
            destruct (nth_error (vs ++ vs' ++ vs'') v); try congruence.
            destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence. }
          { clear - H1 HeqH3 HeqH0.
            revert HeqH3 HeqH0.
            change (
                let XXX z (pf : Some z = nth_error (vs ++ vs' ++ vs'') v) cast := (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e v)) in
                let XXX' z (pf : Some z = nth_error (vs ++ vs'') (v - length vs'))  cast :=  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                               match
                                 pf in (_ = t'')
                                 return
                                 (match t'' with
                                    | Some t1 => typD ts nil t1
                                    | None => unit
                                  end -> typD ts nil t)
                               with
                                 | eq_refl => fun x : typD ts nil z => cast x
                               end (hlist_nth e (v - length vs'))) in
                None =
                match
                  nth_error (vs ++ vs' ++ vs'') v as z
                  return
                  (z = nth_error (vs ++ vs' ++ vs'') v ->
                   option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (XXX z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
                end eq_refl ->
                Some t0 =
                match
                  nth_error (vs ++ vs'') (v - length vs') as z
                  return
                  (z = nth_error (vs ++ vs'') (v - length vs') ->
                   option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
                with
                  | Some z =>
                    fun pf : Some z = nth_error (vs ++ vs'') (v - length vs') =>
                      match typ_cast_typ ts (fun x : Type => x) nil z t with
                        | Some cast =>
                          Some (XXX' z pf cast)
                        | None => None
                      end
                  | None => fun _ : None = nth_error (vs ++ vs'') (v - length vs') => None
                end eq_refl -> False).
            intros XXX XXX'; clearbody XXX XXX'; revert XXX XXX'.
            rewrite H1.
            destruct (nth_error (vs ++ vs' ++ vs'') v); try congruence.
            destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence. } } } }
    { destruct (funcAs f t); auto. }
    { erewrite typeof_expr_lower by (rewrite lower_lower'; eassumption).
      repeat match goal with
               | |- match match ?x with _ => _ end with _ => _ end =>
                 (destruct x; auto); [ ]
             end.
      specialize (IHe1 _ _ _ (tvArr t0_1 t0_2) H).
      specialize (IHe2 _ _ _ t0_1 H0).
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X
             end; destruct (typ_cast_typ ts (fun x0 : Type => x0) nil t0_2 t); auto.
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
      apply (IHe (Hcons (p x) VS) VS' VS''). }
    { match goal with
        | |- match match ?x with _ => _ end with _ => _ end =>
          destruct x; auto
      end. }
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
    cutrewrite (length vs = length x) in H.
    cutrewrite (length vs' = length x0) in H.
    specialize (@exprD'_lower us x x0 x1 e e0 t H).
    intros.
    repeat match goal with
             | _ : match ?X with _ => _ end |- _ =>
               destruct X
           end; intuition try congruence.
    rewrite H3. reflexivity.
    rewrite EnvI.split_env_length. rewrite H1. reflexivity.
    rewrite EnvI.split_env_length. rewrite H0. reflexivity.
  Qed.

  Lemma exprD'_lift : forall us vs vs' vs'' e t,
    match exprD' us (vs ++ vs' ++ vs'') (lift (length vs) (length vs') e) t
        , exprD' us (vs ++ vs'') e t
    with
      | None , None => True
      | Some l , Some r =>
        forall VS VS' VS'',
          l (hlist_app VS (hlist_app VS' VS'')) =
          r (hlist_app VS VS'')
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
        do 2 match goal with
               | |- match ?X with _ => _ end =>
                 let z := fresh in
                 remember X as z ; destruct z
             end; auto.
        { intros.
          assert (nth_error (vs ++ vs' ++ vs'') v = nth_error (vs ++ vs'') v).
          { repeat rewrite nth_error_app_L by omega. auto. }
          revert HeqH1 HeqH0.
          change (
              let zzz e := hlist_nth e v in
              let zzz' e := hlist_nth e v in
              Some t1 =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some
                          (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t2 => typD ts nil t2
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (zzz e))
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl ->
              Some t0 =
              match
                nth_error (vs ++ vs' ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some
                          (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t2 => typD ts nil t2
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (zzz' e))
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
              end eq_refl ->
              t0 (hlist_app VS (hlist_app VS' VS'')) = t1 (hlist_app VS VS'')).
          intros zzz zzz'.
          symmetry in H0.
          assert (zzz' (hlist_app VS (hlist_app VS' VS'')) =
                  match H0 in _ = z return match z with
                                             | None => unit
                                             | Some t => typD ts nil t
                                           end
                  with
                    | eq_refl => zzz (hlist_app VS VS'')
                  end).
          { subst zzz zzz'; simpl.
            repeat rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
            gen_refl.
            repeat match goal with
                   | |- appcontext [ cast2 ?X ?Y ?Z ] =>
                     generalize dependent (cast2 X Y Z)
                   | |- appcontext [ cast1 ?X ?Y ?Z ] =>
                     generalize dependent (cast1 X Y Z)
                 end.
            rewrite <- H0.
            generalize dependent (hlist_nth VS v).
            remember (nth_error vs v). destruct e.
            { simpl. intros. uip_all. clear.
              generalize e9 e7. rewrite <- e9.
              uip_all. auto. }
            { exfalso. clear - Heqe H.
              symmetry in Heqe.
              apply nth_error_length_ge in Heqe. omega. } }
          { generalize dependent (hlist_app VS (hlist_app VS' VS'')).
            generalize dependent (hlist_app VS VS'').
            clearbody zzz zzz'. revert zzz zzz'.
            rewrite <- H0. gen_refl.
            remember (nth_error (vs ++ vs'') v). destruct e.
            { uip_all.
              destruct (typ_cast_typ ts (fun x : Type => x) nil t2 t); try congruence.
              inv_all. subst. uip_all. intuition. }
            { exfalso. clear - H Heqe.
              symmetry in Heqe.
              rewrite nth_error_app_L in Heqe by omega.
              apply nth_error_length_ge in Heqe. omega. } } }
        { revert HeqH1 HeqH0.
          change (
              let XXX z (pf : Some z = nth_error (vs ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t1 => typD ts nil t1
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (hlist_nth e v)) in
              let XXX' z (pf : Some z = nth_error (vs ++ vs' ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e v)) in
              None =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl ->
              Some t0 =
              match
                nth_error (vs ++ vs' ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX' z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
              end eq_refl -> False).
          intros XXX XXX'; clearbody XXX XXX'; revert XXX XXX'.
          repeat rewrite nth_error_app_L by omega.
          destruct (nth_error vs v); try congruence.
          destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence. }
        { revert HeqH1 HeqH0.
          change (
              let XXX z (pf : Some z = nth_error (vs ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t1 => typD ts nil t1
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (hlist_nth e v)) in
              let XXX' z (pf : Some z = nth_error (vs ++ vs' ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e v)) in
              Some t0 =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl ->
              None =
              match
                nth_error (vs ++ vs' ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX' z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs' ++ vs'') v => None
              end eq_refl -> False).
          intros XXX XXX'; clearbody XXX XXX'; revert XXX XXX'.
          repeat rewrite nth_error_app_L by omega.
          destruct (nth_error vs v); try congruence.
          destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence. } }
      { autorewrite with exprD_rw.
        do 2 match goal with
               | |- match ?X with _ => _ end =>
                 let z := fresh in
                 remember X as z ; destruct z
             end; auto.
        { intros. revert HeqH1 HeqH0.
          change (
              let zzz e := hlist_nth e v in
              let zzz' e := hlist_nth e (v + length vs') in
              Some t1 =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some
                          (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t2 => typD ts nil t2
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (zzz e))
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl ->
              Some t0 =
              match
                nth_error (vs ++ vs' ++ vs'') (v + length vs') as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') (v + length vs') ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') (v + length vs') =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some
                          (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                             match
                               pf in (_ = t'')
                               return
                               (match t'' with
                                  | Some t2 => typD ts nil t2
                                  | None => unit
                                end -> typD ts nil t)
                             with
                               | eq_refl => fun x : typD ts nil z => cast x
                             end (zzz' e))
                      | None => None
                    end
                | None =>
                  fun _ : None = nth_error (vs ++ vs' ++ vs'') (v + length vs') => None
              end eq_refl ->
              t0 (hlist_app VS (hlist_app VS' VS'')) = t1 (hlist_app VS VS'')).
          intros zzz zzz'.
          assert (nth_error (vs ++ vs' ++ vs'') (v + length vs') =
                  nth_error (vs ++ vs'') v).
          { repeat rewrite nth_error_app_R by omega.
            f_equal. omega. }
          assert (zzz (hlist_app VS VS'') =
                  match H0 in _ = t return match t with
                                             | None => unit
                                             | Some t => typD ts nil t
                                           end
                  with
                    | eq_refl => zzz' (hlist_app VS (hlist_app VS' VS''))
                  end).
          { subst zzz zzz'. simpl.
            repeat rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
            gen_refl. generalize H0.
            assert (v + length vs' - length vs - length vs' = v - length vs) by omega.
            repeat match goal with
                   | |- appcontext [ cast2 ?X ?Y ?Z ] =>
                     generalize dependent (cast2 X Y Z)
                   | |- appcontext [ cast1 ?X ?Y ?Z ] =>
                     generalize dependent (cast1 X Y Z)
                 end.
            rewrite H1. rewrite H0. clear - H.
            generalize dependent (hlist_nth VS'' (v - length vs)).
            repeat match goal with
                     | |- appcontext [ @hlist_nth ?A ?B ?C ?D ?E ] =>
                       generalize (@hlist_nth A B C D E)
                   end.
            remember (nth_error vs v). destruct e.
            { exfalso.
              rewrite <- (app_nil_r vs) in Heqe.
              rewrite nth_error_app_R in Heqe. rewrite nth_error_nil in Heqe.
              congruence.  omega. }
            { uip_all. generalize (e4 eq_refl). intros.
              clear - H. revert y y0 y2.
              generalize e8 e3 e2. rewrite e8.
              intros; uip_all. clear - H.
              revert y0. gen_refl.
              remember (nth_error vs (v + length vs')).
              destruct e1.
              { exfalso. clear - Heqe1 H.
                rewrite <- (app_nil_r vs) in Heqe1.
                rewrite nth_error_app_R in Heqe1 by omega.
                rewrite nth_error_nil in *. congruence. }
              { intros. revert y2 y.
                generalize (e4 e1). intro. generalize e3.
                gen_refl. clear - H e3. revert e5 e2.
                rewrite <- e3. clear e3.
                intros; uip_all.
                gen_refl.
                remember (nth_error vs' (v + length vs' - length vs)).
                destruct e0.
                { exfalso. clear - H Heqe0.
                  rewrite <- (app_nil_r vs') in Heqe0.
                  rewrite nth_error_app_R in Heqe0. rewrite nth_error_nil in Heqe0.
                  congruence.
                  rewrite app_nil_r. omega. }
                { intros. generalize (e5 e0). uip_all. auto. } } } }
          { clearbody zzz zzz'.
            generalize dependent (hlist_app VS VS'').
            generalize dependent (hlist_app VS (hlist_app VS' VS'')).
            revert zzz zzz'. generalize H0. rewrite H0.
            remember (nth_error (vs ++ vs'') v).
            destruct e.
            { intros; uip_all.
              destruct (typ_cast_typ ts (fun x : Type => x) nil t2 t); try congruence.
              inv_all. subst. rewrite H2. uip_all. auto. }
            { congruence. } } }
        { revert HeqH0 HeqH1.
          change (
              let XXX z (pf : Some z = nth_error (vs ++ vs' ++ vs'') (v + length vs')) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e (v + length vs'))) in
              let XXX' z (pf : Some z = nth_error (vs ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e v)) in
              Some t0 =
              match
                nth_error (vs ++ vs' ++ vs'') (v + length vs') as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') (v + length vs') ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') (v + length vs') =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX z pf cast)
                      | None => None
                    end
                | None =>
                  fun _ : None = nth_error (vs ++ vs' ++ vs'') (v + length vs') => None
              end eq_refl ->
              None =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX' z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl -> False).
          intros zzz zzz'; clearbody zzz zzz'; revert zzz zzz'.
          cutrewrite (nth_error (vs ++ vs' ++ vs'') (v + length vs') =
                      nth_error (vs ++ vs'') v).
          destruct (nth_error (vs ++ vs'') v); try congruence.
          destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence.
          repeat rewrite nth_error_app_R by omega. f_equal. omega. }
        { revert HeqH0 HeqH1.
          change (
              let XXX z (pf : Some z = nth_error (vs ++ vs' ++ vs'') (v + length vs')) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs' ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e (v + length vs'))) in
              let XXX' z (pf : Some z = nth_error (vs ++ vs'') v) cast :=
                  (fun e : hlist (typD ts nil) (vs ++ vs'') =>
                     match
                       pf in (_ = t'')
                       return
                       (match t'' with
                          | Some t1 => typD ts nil t1
                          | None => unit
                        end -> typD ts nil t)
                     with
                       | eq_refl => fun x : typD ts nil z => cast x
                     end (hlist_nth e v)) in
              None =
              match
                nth_error (vs ++ vs' ++ vs'') (v + length vs') as z
                return
                (z = nth_error (vs ++ vs' ++ vs'') (v + length vs') ->
                 option (hlist (typD ts nil) (vs ++ vs' ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs' ++ vs'') (v + length vs') =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX z pf cast)
                      | None => None
                    end
                | None =>
                  fun _ : None = nth_error (vs ++ vs' ++ vs'') (v + length vs') => None
              end eq_refl ->
              Some t0 =
              match
                nth_error (vs ++ vs'') v as z
                return
                (z = nth_error (vs ++ vs'') v ->
                 option (hlist (typD ts nil) (vs ++ vs'') -> typD ts nil t))
              with
                | Some z =>
                  fun pf : Some z = nth_error (vs ++ vs'') v =>
                    match typ_cast_typ ts (fun x : Type => x) nil z t with
                      | Some cast =>
                        Some (XXX' z pf cast)
                      | None => None
                    end
                | None => fun _ : None = nth_error (vs ++ vs'') v => None
              end eq_refl -> False).
          intros zzz zzz'; clearbody zzz zzz'; revert zzz zzz'.
          cutrewrite (nth_error (vs ++ vs' ++ vs'') (v + length vs') =
                      nth_error (vs ++ vs'') v).
          destruct (nth_error (vs ++ vs'') v); try congruence.
          destruct (typ_cast_typ ts (fun x : Type => x) nil t1 t); congruence.
          repeat rewrite nth_error_app_R by omega. f_equal. omega. } } }
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
      specialize (IHe1 vs' vs (tvArr t0_1 t0_2)).
      specialize (IHe2 vs' vs t0_1).
      simpl in *. rewrite lift_lift' in *.
      repeat match goal with
               | _ : match ?X with _ => _ end |- _ =>
                 destruct X; intuition
             end; eauto.
      destruct (typ_cast_typ ts (fun x : Type => x) nil t0_2 t); auto.
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
      intros. eapply (IHe (Hcons (p x) VS)). }
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
    cutrewrite (length vs = length x).
    cutrewrite (length vs' = length x0).
    specialize (@exprD'_lift us x x0 x1 e t).
    intros.
    repeat match goal with
             | _ : match ?X with _ => _ end |- _ =>
               destruct X
           end; intuition try congruence.
    rewrite H2. reflexivity.
    rewrite EnvI.split_env_length. rewrite H0. reflexivity.
    rewrite EnvI.split_env_length. rewrite H. reflexivity.
  Qed.

End typed.
