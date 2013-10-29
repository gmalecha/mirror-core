Require Import List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Injection.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

(** This is a temporary thing **)
Require Import FunctionalExtensionality.

Section weaken_types.

  Theorem typeof_expr_weaken : forall tfs e uenv venv t,
    typeof_expr tfs uenv venv e = Some t ->
    forall ue ve,
    typeof_expr tfs (uenv ++ ue) (venv ++ ve) e = Some t.
  Proof.
    induction e; simpl; intros; forward; inv_all; subst; Cases.rewrite_all ;
      eauto using nth_error_weaken.
    { specialize (IHe uenv (t :: venv) t1).
      simpl in *.
      Cases.rewrite_all. auto. }
    { rewrite RelDec.rel_dec_eq_true by eauto with typeclass_instances.
      reflexivity. }
  Qed.

  Theorem WellTyped_expr_weaken_onlyU : forall tfs us us' vs e t,
    WellTyped_expr tfs us vs e t ->
    WellTyped_expr tfs (us ++ us') vs e t.
  Proof.
    unfold WellTyped_expr; intros.
    rewrite <- (app_nil_r vs); eauto using typeof_expr_weaken.
  Qed.

  Theorem WellTyped_expr_weaken_onlyV : forall tfs us vs vs' e t,
    WellTyped_expr tfs us vs e t ->
    WellTyped_expr tfs us (vs ++ vs') e t.
  Proof.
    unfold WellTyped_expr; intros.
    rewrite <- (app_nil_r us); eauto using typeof_expr_weaken.
  Qed.

  Theorem WellTyped_expr_weaken : forall tfs us us' vs vs' e t,
    WellTyped_expr tfs us vs e t ->
    WellTyped_expr tfs (us ++ us') (vs ++ vs') e t.
  Proof.
    unfold WellTyped_expr; intros.
    eauto using typeof_expr_weaken.
  Qed.

End weaken_types.

Section weaken_denote.
  Variable types : types.

  Variable fs : functions types.
  Variable uenv : env (typD types).

  Lemma exprD'_weaken : forall ve ue e t venv,
    match exprD' fs uenv venv e t
        , exprD' fs (uenv ++ ue) (venv ++ ve) e t
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
          let zzz z (pf : Some z = nth_error venv v) cast :=
              (fun e1 : hlist (typD types nil) venv =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t1 => typD types nil t1
                      | None => unit
                    end -> typD types nil t)
                 with
                   | eq_refl => fun x : typD types nil z => cast x
                 end (hlist_nth e1 v))
          in
          let zzz' z (pf : Some z = nth_error (venv ++ ve) v) cast := 
              (fun e1 : hlist (typD types nil) (venv ++ ve) =>
                 match
                   pf in (_ = t'')
                   return
                   (match t'' with
                      | Some t1 => typD types nil t1
                      | None => unit
                    end -> typD types nil t)
                 with
                   | eq_refl => fun x : typD types nil z => cast x
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
                  match typ_cast_typ types (fun x : Type => x) nil z t with
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
         match typ_cast_typ types (fun x : Type => x) nil z t with
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
      specialize (IHe1 (tvArr t2 t3) venv).
      specialize (IHe2 t2 venv).
      forward. }
    { specialize (IHe t2 (t :: venv)).
      simpl in *. forward.
      inv_all; subst.
      eapply functional_extensionality; intros.
      apply (IHe venve (Hcons (p x) vs)). }
    { erewrite lookupAs_weaken; eauto. }
    { specialize (IHe1 t venv).
      specialize (IHe2 t venv).
      forward. }
    { specialize (IHe tvProp venv).
      forward. }
  Qed.

  Theorem exprD_weaken : forall venv ue ve e t x,
    exprD fs uenv venv e t = Some x ->
    exprD fs (uenv ++ ue) (venv ++ ve) e t = Some x.
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
    exprD fs uenv venv e t = Some x ->
    exprD fs (uenv ++ ue) venv e t = Some x.
  Proof.
    intros.
    rewrite <- (app_nil_r venv).
    eauto using exprD_weaken.
  Qed.

  Theorem exprD_weaken_onlyV : forall venv ve e t x,
    exprD fs uenv venv e t = Some x ->
    exprD fs uenv (venv ++ ve) e t = Some x.
  Proof.
    intros.
    rewrite <- (app_nil_r uenv).
    eauto using exprD_weaken.
  Qed.

End weaken_denote.
