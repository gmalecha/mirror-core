Require Import List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

(** This is a temporary thing **)
Require Import FunctionalExtensionality.

Section weaken_types.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Theorem typeof_expr_weaken : forall (e : expr func) uenv venv t,
    typeof_expr uenv venv e = Some t ->
    forall ue ve,
    typeof_expr (uenv ++ ue) (venv ++ ve) e = Some t.
  Proof.
    induction e; simpl; intros; forward; inv_all; subst; Cases.rewrite_all ;
      eauto using nth_error_weaken.
    { specialize (IHe uenv (t :: venv) t1).
      simpl in *.
      Cases.rewrite_all. auto. }
  Qed.

  Theorem WellTyped_expr_weaken_onlyU : forall us us' vs e t,
    WellTyped_expr us vs e t ->
    WellTyped_expr (us ++ us') vs e t.
  Proof.
    unfold WellTyped_expr; intros.
    rewrite <- (app_nil_r vs); eauto using typeof_expr_weaken.
  Qed.

  Theorem WellTyped_expr_weaken_onlyV : forall us vs vs' e t,
    WellTyped_expr us vs e t ->
    WellTyped_expr us (vs ++ vs') e t.
  Proof.
    unfold WellTyped_expr; intros.
    rewrite <- (app_nil_r us); eauto using typeof_expr_weaken.
  Qed.

  Theorem WellTyped_expr_weaken : forall us us' vs vs' e t,
    WellTyped_expr us vs e t ->
    WellTyped_expr (us ++ us') (vs ++ vs') e t.
  Proof.
    unfold WellTyped_expr; intros.
    eauto using typeof_expr_weaken.
  Qed.

(*
  Theorem exprD'_weaken_Some : forall ue ve e t venv x y,
    exprD' fs uenv venv e t = Some x ->
    exprD' fs (uenv ++ ue) (venv ++ ve) e t = Some y ->
    forall h he, x h = y (hlist_app h he).
  Proof.
*)
(*
    induction e; simpl; intros;
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 match type of X with
                   | typ =>
                     (destruct X; try congruence); [ ]
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ _ : context [ match ?X with _ => _ end ] |- _ ] =>
                 match type of X with
                   | typ =>
                     (destruct X; try congruence); [ ]
                   | _ => match X with
                            | match _ with _ => _ end => fail 1
                            | _ => consider X; intros; subst
                          end
                 end
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; auto; try congruence; try reflexivity.
      { repeat match goal with
                 | [ H : context [ @refl_equal ?A ?B ] |- _ ] =>
                   generalize dependent (@refl_equal A B)
               end.
        pattern (nth_error venv v) at 1 3.
        destruct (nth_error venv v); try congruence.
        intros. generalize dependent e0.
        generalize (nth_error_weaken ve venv _ (sym_eq e)); intro.
        pattern (nth_error (venv ++ ve) v) at 1 3.
        rewrite H0. intros.
        destruct (typ_cast_typ types (fun x => x) nil t0 t); try congruence.
        inv_all; subst.
        unfold tenv in *.
        rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
=======
*)
End weaken_types.

Section weaken_denote.
  Variable types : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD types) func.
  Variable uenv : env (typD types).

  Lemma exprD'_weaken : forall ve ue e t venv,
    match exprD' uenv venv e t
        , exprD' (uenv ++ ue) (venv ++ ve) e t
    with
      | Some l , Some r =>
        forall venve vs,
          l vs = r (hlist_app vs venve)
      | None , _ => True
      | Some _ , None => False
    end.
  Proof.
    induction e; simpl; intros; autorewrite with exprD_rw; forward;
      inv_all; subst; auto.
    { gen_refl.
      change (
          let zzz z (pf : Some z = nth_error venv v)
                  (cast : forall F : Type -> Type, F (typD types nil z) -> F (typD types nil t))  :=
              (fun e1 : hlist (typD types nil) venv =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t1 => typD types nil t1
                      | None => unit
                    end -> typD types nil t)
                 with
                   | eq_refl => fun x : typD types nil z =>
                                  cast (fun x : Type => x) x
                 end (hlist_nth e1 v))
          in
          let zzz' z (pf : Some z = nth_error (venv ++ ve) v)
                   (cast : forall F : Type -> Type, F (typD types nil z) -> F (typD types nil t)) :=
              (fun e1 : hlist (typD types nil) (venv ++ ve) =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t1 => typD types nil t1
                      | None => unit
                    end -> typD types nil t)
                 with
                   | eq_refl => fun x : typD types nil z =>
                                  cast (fun x : Type => x) x
                 end (hlist_nth e1 v))
          in
          forall (e : nth_error (venv ++ ve) v = nth_error (venv ++ ve) v)
                 (e0 : nth_error venv v = nth_error venv v),
            match
              nth_error venv v as z
              return
              (z = nth_error venv v ->
               option (hlist (typD types nil) venv -> typD types nil t))
            with
              | Some z =>
                fun pf : Some z = nth_error venv v =>
                  match typ_cast_typ types nil z t with
                    | Some cast =>
                      Some (zzz z pf cast)
                    | None => None
                  end
              | None => fun _ : None = nth_error venv v => None
            end e0 = Some t0 ->
            match
              match
                nth_error (venv ++ ve) v as z
                return
                (z = nth_error (venv ++ ve) v ->
                 option (hlist (typD types nil) (venv ++ ve) -> typD types nil t))
              with
                | Some z =>
         fun pf : Some z = nth_error (venv ++ ve) v =>
         match typ_cast_typ types nil z t with
         | Some cast =>
             Some (zzz' z pf cast)
         | None => None
         end
     | None => fun _ : None = nth_error (venv ++ ve) v => None
     end e
   with
   | Some r =>
       forall (venve : hlist (typD types nil) ve)
         (vs : hlist (typD types nil) venv), t0 vs = r (hlist_app vs venve)
   | None => False
   end).
      intros zzz zzz'.
      assert (forall a b cast (c : hlist (typD types nil) venv) d e,
                zzz a b cast c =
                zzz' a e cast (hlist_app c d)).
      { subst zzz zzz'; simpl.
        intros. rewrite hlist_nth_hlist_app by eauto with typeclass_instances.
        gen_refl.
        match goal with
          | |- forall x, _ ?X = @?G x =>
            match G with
              | context [ @hlist_nth ?A ?B ?C ?D ?E ] =>
                change (@hlist_nth A B C D E) with X ;
                  generalize X
            end
        end.
        generalize (cast1 venv ve v).
        generalize (cast2 venv ve v).
        generalize b. simpl in *.
        rewrite <- b; intros.
        generalize (e1 _ e2).
        rewrite <- e.
        uip_all. reflexivity. }
      { clearbody zzz zzz'.
        revert H; revert zzz; revert zzz'.
        consider (nth_error venv v); try congruence.
        { intros. forward.
          inv_all; subst.
          assert (nth_error (venv ++ ve) v = Some t1).
          { eapply nth_error_weaken; eauto. }
          generalize dependent (nth_error (venv ++ ve) v).
          intros; subst.
          match goal with
            | H : ?X = _ |- context [ match ?Y with _ => _ end ] =>
              change Y with X; rewrite H
          end.
          eauto. } } }
     { repeat rewrite typeof_env_app.
      erewrite typeof_expr_weaken by eauto. simpl.
      specialize (IHe1 (tyArr t2 t3) venv).
      specialize (IHe2 t2 venv).
      forward. }
    { specialize (IHe t2 (t :: venv)).
      simpl in *. forward.
      inv_all; subst.
      eapply functional_extensionality; intros.
      apply (IHe venve (Hcons (F := typD types nil) (p (fun x : Type => x) x) vs)). }
    { erewrite lookupAs_weaken; eauto. }
  Qed.

  Theorem exprD_weaken : forall venv ue ve e t x,
    exprD uenv venv e t = Some x ->
    exprD (uenv ++ ue) (venv ++ ve) e t = Some x.
  Proof.
    unfold exprD.
    intros; rewrite split_env_app.
    destruct (split_env venv).
    destruct (split_env ve).
    generalize (exprD'_weaken x1 ue e t x0).
    forward.
    inv_all; subst.
    f_equal; eauto.
  Qed.

  Theorem exprD_weaken_onlyU : forall venv ue e t x,
    exprD uenv venv e t = Some x ->
    exprD (uenv ++ ue) venv e t = Some x.
  Proof.
    intros.
    rewrite <- (app_nil_r venv).
    eauto using exprD_weaken.
  Qed.

  Theorem exprD_weaken_onlyV : forall venv ve e t x,
    exprD uenv venv e t = Some x ->
    exprD uenv (venv ++ ve) e t = Some x.
  Proof.
    intros.
    rewrite <- (app_nil_r uenv).
    eauto using exprD_weaken.
  Qed.

End weaken_denote.
