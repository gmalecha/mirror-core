Require Import List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExprCore.

Section semantic.
  Variable ts : types.

  Theorem split_env_app : forall (l l' : env ts), 
    split_env (l ++ l') =
    let (ts,vs) := split_env l in
    let (ts',vs') := split_env l' in
    existT _ (ts ++ ts') (hlist_app vs vs').
  Proof.
    induction l; simpl; intros.
    { destruct (split_env l'); reflexivity. }
    { destruct a. rewrite IHl.
      destruct (split_env l).
      destruct (split_env l'). reflexivity. }
  Qed.

  Variable fs : functions ts.
  Variable uenv : env ts.

  Theorem lookupAs_weaken : forall (a b : env ts) n t x, 
    lookupAs a n t = Some x ->
    lookupAs (a ++ b) n t = Some x.
  Proof.
    clear. unfold lookupAs. intros.
    consider (nth_error a t); intros; try congruence.
    erewrite nth_error_weaken by eassumption. auto.
  Qed.

  Theorem exprD_weaken : forall venv e t ue ve x, 
    exprD fs uenv venv e t = Some x ->
    exists y, exprD fs (uenv ++ ue) (venv ++ ve) e t = Some y /\
      equiv ts t x y.
  Proof.
(*
    unfold exprD; intros. rewrite split_env_app.
    destruct (split_env venv). destruct (split_env ve).
    consider (exprD' fs uenv x0 e t); 
    consider (exprD' fs (uenv ++ ue) (x0 ++ x1) e t); intros; try congruence.
    { inversion H1; clear H1; subst.
      generalize dependent x0; generalize dependent x1; generalize dependent t.
      clear ve venv. induction e; simpl; intros;
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 match type of X with
                   | typ => fail 1
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ _ : context [ match ?X with _ => _ end ] |- _ ] =>
                 match type of X with
                   | typ => fail 1
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; auto; try congruence.
      { eexists; split; eauto. reflexivity. }
      { repeat match goal with
                 | [ H : context [ @refl_equal ?A ?B ] |- _ ] =>
                   generalize dependent (@refl_equal A B)
               end.
        pattern (nth_error x0 v) at 2 3.
        destruct (nth_error x0 v); try congruence.
        intros. generalize dependent e.
        generalize (nth_error_weaken x1 x0 _ e0); intro.
        pattern (nth_error (x0 ++ x1) v) at 2 3.
        rewrite H. intros.
        consider (typ_eq_odec t2 t); intros; try congruence.
        inversion H1; clear H1; inversion H2; clear H2; subst.
        eexists; split; eauto.
        Require Import ExtLib.Tactics.EqDep.
        uip_all. clear.
        About hlist_nth.
        SearchAbout nth_error.
        Theorem nth_error_length_ge : forall T (ls : list T) n,
          nth_error ls n = None -> length ls <= n.
        Admitted.
        Definition cast1 T (l l' : list T) n v := 
          (fun pf : nth_error l n = Some v => eq_sym (nth_error_weaken l' l n pf)).
        Definition cast2 T (l l' : list T) n :=
          (fun pf : nth_error l n = None => eq_sym (@nth_error_app_R _ l l' _ (nth_error_length_ge _ _ _ pf))).

        Theorem uip_refl : forall (t : option typ) e, e = eq_refl t. 
        Admitted.

        Theorem hlist_nth_hlist_app : forall T (F : T -> Type) l l' (h : hlist F l) (h' : hlist F l') n,
          hlist_nth (hlist_app h h') n = 
          match nth_error l n as k
            return nth_error l n = k ->
                   match nth_error (l ++ l') n with
                     | None => unit
                     | Some t => F t
                   end
            with
            | Some _ => fun pf => 
              match cast1 _ _ _ _ _ pf in _ = z ,
                eq_sym pf in _ = w 
                return match w with
                         | None => unit
                         | Some t => F t
                       end ->
                       match z with
                         | None => unit
                         | Some t => F t
                       end
                with
                | eq_refl , eq_refl => fun x => x
              end (hlist_nth h n)
            | None => fun pf => 
              match cast2 _ _ _ _ pf in _ = z 
                return match z with
                         | Some t => F t
                         | None => unit
                       end
                with 
                | eq_refl => hlist_nth h' (n - length l)
              end
          end eq_refl.
        Proof.
          induction h; simpl; intros.
          { destruct n; simpl. simpl in *. uip_all.
            simpl in *. admit. 
            admit. }
          { destruct n; simpl.
            admit.
            rewrite IHh. simpl. admit. } 
        Qed.
        rewrite hlist_nth_hlist_app.
        generalize (cast1 typ x0 x1 v).
        generalize (cast2 typ x0 x1 v).
        uip_all.
        repeat match goal with
                 | |- context [ @eq_refl ?A ?B ] =>
                   generalize (@eq_refl A B)
               end.
        intros. clear. simpl in *.
        change ((fun z => Types.equiv ts t
     (match
        e2 in (_ = t'')
        return
          (match t'' with
           | Some t0 => typD ts nil t0
           | None => unit
           end -> typD ts nil t)
      with
      | eq_refl => fun x : typD ts nil t => x
      end z)
     (match
        e1 in (_ = t'')
        return
          (match t'' with
           | Some t0 => typD ts nil t0
           | None => unit
           end -> typD ts nil t)
      with
      | eq_refl => fun x : typD ts nil t => x
      end
        (match
           nth_error x0 v as k
           return
             (nth_error x0 v = k ->
              match nth_error (x0 ++ x1) v with
              | Some t0 => typD ts nil t0
              | None => unit
              end)
         with
         | Some t0 =>
             fun pf : nth_error x0 v = Some t0 =>
             match e0 t0 pf in (_ = z)
               return
                 (match nth_error x0 v with
                  | Some t1 => typD ts nil t1
                  | None => unit
                  end ->
                  match z with
                  | Some t1 => typD ts nil t1
                  | None => unit
                  end)
             with
             | eq_refl =>
                 match
                   eq_sym pf in (_ = w)
                   return
                     (match w with
                      | Some t1 => typD ts nil t1
                      | None => unit
                      end -> typD ts nil t0)
                 with
                 | eq_refl => fun x : typD ts nil t0 => x
                 end
             end z
         | None =>
             fun pf : nth_error x0 v = None =>
             match e pf
               in (_ = z)
               return
                 match z with
                 | Some t0 => typD ts nil t0
                 | None => unit
                 end
             with
             | eq_refl => hlist_nth h0 (v - length x0)
             end
         end e3))) (hlist_nth h v)).
        generalize (hlist_nth h v); clear.
        revert e. revert e0. revert e3. generalize e2.
        rewrite <- e2.
        intros.
        rewrite (uip_refl _ e0).
        rewrite (uip_refl _ e3).
        uip_all.
        rewrite (uip_refl _ e5).
        clear.
        generalize dependent (nth_error (x0 ++ x1) v).
        intros; subst.
        rewrite (uip_refl _ e6).
        reflexivity. }
      { eexists; split; eauto. clear.
        generalize dependent (instantiate_typ (rev ts0) (ftype f0)). reflexivity. }
      { specialize (@IHe _ _ _ _ _ _ H4 _ H2).

admit. }
      { eexists; split; eauto.
        destruct t0; try congruence.
        consider (exprD' fs uenv (t0_1 :: x0) e t0_2); intros; try congruence.
        consider (exprD' fs (uenv ++ ue) (t0_1 :: x0 ++ x1) e t0_2); intros; try congruence.
        inversion H1; clear H1; subst.
        inversion H2; clear H2; subst.
        change (t0_1 :: x0 ++ x1) with ((t0_1 :: x0) ++ x1) in *.
        simpl. intro.
        specialize (IHe t0_2 x1 h0 (t0_1 :: x0) (Hcons a h) t3 H t0 H0).
        inversion IHe. intuition. inversion H2; clear H2; subst.
        destruct t0_2; auto. }
      { consider (lookupAs uenv t v); intros; try congruence.
        erewrite lookupAs_weaken in H by eassumption.
        inversion H1; clear H1; inversion H; clear H; subst.
        eexists; split; eauto. subst; reflexivity. } }
    { exfalso.
*)
  Admitted.

End semantic.