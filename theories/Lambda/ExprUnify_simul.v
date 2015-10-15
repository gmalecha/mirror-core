Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.UnifyI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprUnify_common.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Compat.

Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable subst : Type.
  Variable typ : Type.
  Variable func : Type.
  Context {RType_typ : RType typ}.
  Context {RTypeOk : RTypeOk}.
  Context {RSym_func : RSym func}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Local Existing Instance Expr_expr.
  Context {Typ2_arr : Typ2 _ RFun}.
  Context {Typ2Ok_arr : Typ2Ok Typ2_arr}.
  Context {Subst_subst : Subst subst (expr typ func)}.
  Context {SubstUpdate_subst : SubstUpdate subst (expr typ func)}.
  Context {SubstOk_subst : SubstOk subst typ (expr typ func)}.
  Context {SubstUpdateOk_subst : SubstUpdateOk subst typ (expr typ func)}.

  Local Instance RelDec_Rty : RelDec Rty :=
  { rel_dec := fun a b => match type_cast a b with
                            | Some _ => true
                            | None => false
                          end }.

  Section nested.
    (** n is the number of binders that we have gone under **)
    Variable exprUnify : unifier typ (expr typ func) subst.


    Fixpoint exprUnify' (us vs : tenv typ) (n : nat)
             (e1 e2 : expr typ func) (t : typ) (s : subst) {struct e1}
    : option subst :=
      match e1 , e2 with
        | UVar u1 , UVar u2 =>
          if EqNat.beq_nat u1 u2 then Some s
          else
            match subst_lookup u1 s , subst_lookup u2 s with
              | None , None =>
                match subst_set u1 (UVar u2) s with
                  | None =>
                    subst_set u2 (UVar u1) s
                  | Some s => Some s
                end
              | Some e1' , None =>
                subst_set u2 e1' s
              | None , Some e2' =>
                subst_set u1 e2' s
              | Some e1' , Some e2' =>
                exprUnify us vs n (lift 0 n e1') (lift 0 n e2') t s
            end
        | UVar u1 , _ =>
          match subst_lookup u1 s with
            | None =>
              match lower 0 n e2 with
                | None => None
                | Some e2 => subst_set u1 e2 s
              end
            | Some e1' => exprUnify us vs n (lift 0 n e1') e2 t s
          end
        | _ , UVar u2 =>
          match subst_lookup u2 s with
            | None =>
              match lower 0 n e1 with
                | None => None
                | Some e1 => subst_set u2 e1 s
              end
            | Some e2' => exprUnify us vs n e1 (lift 0 n e2') t s
          end
        | Var v1 , Var v2 =>
          if EqNat.beq_nat v1 v2 then Some s else None
        | Inj f1 , Inj f2 =>
          match sym_eqb f1 f2 with
            | Some true => Some s
            | _ => None
          end
        | App e1 e1' , App e2 e2' =>
          match exprUnify_simul' us vs n e1 e2 s with
            | Some (tarr,s') =>
              typ2_match (fun _ => option _) tarr
                         (fun d _ => exprUnify' us vs n e1' e2' d s')
                         None
            | None => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          (* t1 = t2 since both terms have the same type *)
          typ2_match (F := Fun) (fun _ => _) t
                     (fun _ t =>
                        exprUnify' us (t1 :: vs) (S n) e1 e2 t s)
                     None
        | _ , _ => None
      end
    with exprUnify_simul' (tus tvs : tenv typ) (n : nat)
                          (e1 e2 : expr typ func) (s : subst) {struct e1}
    : option (typ * subst) :=
      match e1 , e2 return option (typ * subst) with
        | UVar u1 , UVar u2 =>
          if EqNat.beq_nat u1 u2 then
            match nth_error tus u1 with
              | None => None
              | Some t => Some (t,s)
            end
          else
            match typeof_expr tus tvs (UVar u1)
                , typeof_expr tus tvs (UVar u2)
            with
              | Some t1 , Some t2 =>
                if t1 ?[ Rty ] t2 then
                  match
                    match subst_lookup u1 s , subst_lookup u2 s with
                      | None , None =>
                        match subst_set u1 (UVar u2) s with
                          | None =>
                            subst_set u2 (UVar u1) s
                          | Some s => Some s
                        end
                      | Some e1' , None =>
                        subst_set u2 e1' s
                      | None , Some e2' =>
                        subst_set u1 e2' s
                      | Some e1' , Some e2' =>
                        exprUnify tus tvs n (lift 0 n e1') (lift 0 n e2') t1 s
                    end
                  with
                    | Some s => Some (t1,s)
                    | None => None
                  end
                else
                  None
              | _ , _ => None
            end
        | UVar u1 , _ =>
          match subst_lookup u1 s with
            | None =>
              match lower 0 n e2 with
                | None => None
                | Some e2' =>
                  match typeof_expr tus tvs (UVar u1)
                      , typeof_expr tus tvs e2
                  with
                    | Some t1 , Some t2 =>
                      if t1 ?[ Rty ] t2 then
                        match subst_set u1 e2' s with
                          | Some s => Some (t1, s)
                          | None => None
                        end
                      else
                        None
                    | _ , _ => None
                  end
              end
            | Some e1' =>
              match typeof_expr tus tvs (UVar u1)
                  , typeof_expr tus tvs e2
              with
                | Some t1 , Some t2 =>
                  if t1 ?[ Rty ] t2 then
                    match exprUnify tus tvs n (lift 0 n e1') e2 t1 s with
                      | Some s => Some (t1, s)
                      | None => None
                    end
                  else
                    None
                | _ , _ => None
              end
          end
        | _ , UVar u2 =>
          match subst_lookup u2 s with
            | None =>
              match lower 0 n e1 with
                | None => None
                | Some e1' =>
                  match typeof_expr tus tvs e1
                      , typeof_expr tus tvs (UVar u2)
                  with
                    | Some t1 , Some t2 =>
                      if t1 ?[ Rty ] t2 then
                        match subst_set u2 e1' s with
                          | Some s => Some (t1, s)
                          | None => None
                        end
                      else None
                    | _ , _ => None
                  end
              end
            | Some e2' =>
              match typeof_expr tus tvs e1
                  , typeof_expr tus tvs (UVar u2)
              with
                | Some t1 , Some t2 =>
                  if t1 ?[ Rty ] t2 then
                    match exprUnify tus tvs n e1 (lift 0 n e2') t1 s with
                      | Some s => Some (t1, s)
                      | _ => None
                    end
                  else
                    None
                | _ , _ => None
              end
          end
        | Var v1 , Var v2 =>
          if EqNat.beq_nat v1 v2 then
            match typeof_expr tus tvs (Var v1)
                , typeof_expr tus tvs (Var v2)
            with
              | Some t1 , Some t2 =>
                if t1 ?[ Rty ] t2 then Some (t1,s) else None
              | _ , _ => None
            end
          else
            None
        | Inj f1 , Inj f2 =>
          match sym_eqb f1 f2 with
            | Some true =>
              match typeof_sym f1 with
                | Some t => Some (t,s)
                | None => None
              end
            | _ => None
          end
        | App e1 e1' , App e2 e2' =>
          match exprUnify_simul' tus tvs n e1 e2 s with
            | Some (t,s) =>
              typ2_match (fun _ => option (typ * subst)) t
                         (fun d r =>
                            match exprUnify' tus tvs n e1' e2' d s with
                              | Some s' => Some (r,s')
                              | None => None
                            end)
                         None
            | None => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          if t1 ?[ Rty ] t2 then
            match exprUnify_simul' tus (t1 :: tvs) (S n) e1 e2 s with
              | Some (t,s) => Some (typ2 t1 t, s)
              | _ => None
            end
          else
            None
        | _ , _ => None
      end%bool.

  End nested.

  Section exprUnify.

    (** Delaying the recursion is important **)
    Fixpoint exprUnify (fuel : nat)
             (us vs : tenv typ) (under : nat)
             (e1 e2 : expr typ func) (t : typ) (s : subst) : option subst :=
      match fuel with
        | 0 => None
        | S fuel =>
          exprUnify' (fun tus tvs => exprUnify fuel tus tvs)
                     us vs under e1 e2 t s
      end.
  End exprUnify.

  Existing Instance SubstUpdate_subst.
  Existing Instance SubstOk_subst.

  Definition unify_sound_mutual
    (unify : unifier typ (expr typ func) subst) : Prop :=
    unify_sound unify ->
    forall tu tv e1 e2 s s' t tv',
      (exprUnify' unify tu (tv' ++ tv) (length tv') e1 e2 t s = Some s' ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) t e1 = Some v1 ->
        exprD' tu (tv' ++ tv) t e2 = Some v2 ->
        substD tu tv s = Some sD ->
        exists sD',
             substD (expr := expr typ func) tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)) /\
      (exprUnify_simul' unify tu (tv' ++ tv) (length tv') e1 e2 s = Some (t,s') ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) t e1 = Some v1 ->
        exprD' tu (tv' ++ tv) t e2 = Some v2 ->
        substD tu tv s = Some sD ->
        exists sD',
             substD (expr := expr typ func) tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)).

  Ltac forward_reason :=
    repeat match goal with
             | H : exists x, _ |- _ =>
               destruct H
             | H : _ /\ _ |- _ => destruct H
             | H' : ?X , H : ?X -> ?Y |- _ =>
               match type of X with
                 | Prop => specialize (H H')
               end
             | H : ?X -> ?Y |- _ =>
               match type of X with
                 | Prop =>
                   let H' := fresh in
                   assert (H' : X) by eauto ;
                   specialize (H H') ;
                   clear H'
               end
           end.


  Lemma exprD_from_subst : forall tus tvs tvs' s e u t sD eD,
    WellFormed_subst s ->
    substD tus tvs s = Some sD ->
    subst_lookup u s = Some e ->
    exprD' tus (tvs' ++ tvs) t (UVar u) = Some eD ->
    exists eD',
      exprD' tus (tvs' ++ tvs) t (lift 0 (length tvs') e) = Some eD' /\
      forall us vs vs',
        sD us vs ->
        eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).
  Proof using RSymOk_func Typ2Ok_arr RTypeOk SubstOk_subst.
    intros.
    autorewrite with exprD_rw in H2. simpl in H2.
    forward. inv_all; subst.
    destruct r.
    eapply substD_lookup in H1; eauto.
    forward_reason.
    change_rewrite H3 in H1.
    inv_all; subst.
    generalize (exprD'_lift tus e nil tvs' tvs x).
    simpl. change_rewrite H2.
    intro.
    forwardy. eexists; split; eauto.
    intros.
    etransitivity; [ eapply H5; eauto | eapply (H6 us Hnil vs' vs) ].
  Qed.

  (** NOTE: The exact statement of exprUnify_simul' prevents Coq from
   ** reducing it with [simpl]
   **)
  Lemma exprUnify_simul'_eq
  : forall u tus tvs n s e1 e2,
      exprUnify_simul' u tus tvs n e1 e2 s =
      match e1 , e2 return option (typ * subst) with
        | UVar u1 , UVar u2 =>
          if EqNat.beq_nat u1 u2 then
            match nth_error tus u1 with
              | None => None
              | Some t => Some (t,s)
            end
          else
            match typeof_expr tus tvs (UVar u1)
                  , typeof_expr tus tvs (UVar u2)
            with
              | Some t1 , Some t2 =>
                if t1 ?[ Rty ] t2 then
                  match
                    match subst_lookup u1 s , subst_lookup u2 s with
                      | None , None =>
                        match subst_set u1 (UVar u2) s with
                          | None =>
                            subst_set u2 (UVar u1) s
                          | Some s => Some s
                        end
                      | Some e1' , None =>
                        subst_set u2 e1' s
                      | None , Some e2' =>
                        subst_set u1 e2' s
                      | Some e1' , Some e2' =>
                        u tus tvs n (lift 0 n e1') (lift 0 n e2') t1 s
                    end
                  with
                    | Some s => Some (t1,s)
                    | None => None
                  end
                else
                  None
              | _ , _ => None
            end
        | UVar u1 , _ =>
          match subst_lookup u1 s with
            | None =>
              match lower 0 n e2 with
                | None => None
                | Some e2' =>
                  match typeof_expr tus tvs (UVar u1)
                      , typeof_expr tus tvs e2
                  with
                    | Some t1 , Some t2 =>
                      if t1 ?[ Rty ] t2 then
                        match subst_set u1 e2' s with
                          | Some s => Some (t1, s)
                          | None => None
                        end
                      else
                        None
                    | _ , _ => None
                  end
              end
            | Some e1' =>
              match typeof_expr tus tvs (UVar u1)
                  , typeof_expr tus tvs e2
              with
                | Some t1 , Some t2 =>
                  if t1 ?[ Rty ] t2 then
                    match u tus tvs n (lift 0 n e1') e2 t1 s with
                      | Some s => Some (t1, s)
                      | None => None
                    end
                  else
                    None
                | _ , _ => None
              end
          end
        | _ , UVar u2 =>
          match subst_lookup u2 s with
            | None =>
              match lower 0 n e1 with
                | None => None
                | Some e1' =>
                  match typeof_expr tus tvs e1
                      , typeof_expr tus tvs (UVar u2)
                  with
                    | Some t1 , Some t2 =>
                      if t1 ?[ Rty ] t2 then
                        match subst_set u2 e1' s with
                          | Some s => Some (t1, s)
                          | None => None
                        end
                      else None
                    | _ , _ => None
                  end
              end
            | Some e2' =>
              match typeof_expr tus tvs e1
                  , typeof_expr tus tvs (UVar u2)
              with
                | Some t1 , Some t2 =>
                  if t1 ?[ Rty ] t2 then
                    match u tus tvs n e1 (lift 0 n e2') t1 s with
                      | Some s => Some (t1, s)
                      | _ => None
                    end
                  else
                    None
                | _ , _ => None
              end
          end
        | Var v1 , Var v2 =>
          if EqNat.beq_nat v1 v2 then
            match typeof_expr tus tvs (Var v1)
                  , typeof_expr tus tvs (Var v2)
            with
              | Some t1 , Some t2 =>
                if t1 ?[ Rty ] t2 then Some (t1,s) else None
              | _ , _ => None
            end
          else
            None
        | Inj f1 , Inj f2 =>
          match sym_eqb f1 f2 with
            | Some true =>
              match typeof_sym f1 with
                | Some t => Some (t,s)
                | None => None
              end
            | _ => None
          end
        | App e1 e1' , App e2 e2' =>
          match exprUnify_simul' u tus tvs n e1 e2 s with
            | Some (t,s) =>
              typ2_match (fun _ => option (typ * subst)) t
                         (fun d r =>
                            match exprUnify' u tus tvs n e1' e2' d s with
                              | Some s' => Some (r,s')
                              | None => None
                            end)
                         None
            | None => None
          end
        | Abs t1 e1 , Abs t2 e2 =>
          if t1 ?[ Rty ] t2 then
            match exprUnify_simul' u tus (t1 :: tvs) (S n) e1 e2 s with
              | Some (t,s) => Some (typ2 t1 t, s)
              | _ => None
            end
          else
            None
        | _ , _ => None
      end%bool.
  Proof using.
    destruct e1; try reflexivity.
  Defined.

  Lemma Open_App_equal
  : forall tus tvs t u f f' x x' A B,
      f A B = f' A B ->
      x A B = x' A B ->
      @AbsAppI.exprT_App typ _ _ tus tvs t u f x A B =
      @AbsAppI.exprT_App typ _ _ tus tvs t u f' x' A B.
  Proof using.
    unfold AbsAppI.exprT_App.
    intros.
    intros.
    autorewrite_with_eq_rw.
    rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma handle_uvar_simul
  : forall u s s' t (e : expr typ func) tv tu tv' unify
           (unifyOk : unify_sound unify),
      match subst_lookup u s with
        | Some e2' =>
          match typeof_expr tu (tv' ++ tv) e with
            | Some t1 =>
              match typeof_expr tu (tv' ++ tv) (UVar u) with
                | Some t2 =>
                  if t1 ?[ Rty ] t2
                  then
                    match
                      unify tu (tv' ++ tv) (length tv')
                            e (lift 0 (length tv') e2') t1 s
                    with
                      | Some s0 => Some (t1, s0)
                      | None => None
                    end
                  else None
                | None => None
              end
            | None => None
          end
        | None =>
          match lower 0 (length tv') e with
            | Some e' =>
              match typeof_expr tu (tv' ++ tv) e with
                | Some t1 =>
                  match typeof_expr tu (tv' ++ tv) (UVar u) with
                    | Some t2 =>
                      if t1 ?[ Rty ] t2
                      then
                        match subst_set u e' s with
                          | Some s0 => Some (t1, s0)
                          | None => None
                        end
                      else None
                    | None => None
                  end
                | None => None
              end
            | None => None
          end
      end = Some (t, s') ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      (forall sD : hlist typD tu -> hlist typD tv -> Prop,
         typeof_expr tu (tv' ++ tv) e <> None ->
         typeof_expr tu (tv' ++ tv) (UVar u) <> None ->
         substD tu tv s = Some sD ->
         exists v1 v2 : exprT tu (tv' ++ tv) (typD t),
           exprD' tu (tv' ++ tv) t e = Some v1 /\
           exprD' tu (tv' ++ tv) t (UVar u) = Some v2 /\
           (exists sD' : hlist typD tu -> hlist typD tv -> Prop,
              substR tu tv s s' /\
              substD tu tv s' = Some sD' /\
              (forall (us : hlist typD tu) (vs : hlist typD tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist typD tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs))))).
  Proof using RTypeOk RSymOk_func Typ2Ok_arr.
    intros.
    do 3 match goal with
           | H : match _ with
                   | Some _ => match ?X with _ => _ end
                   | None => match _ with Some _ => match ?Y with _ => _ end | None => _ end
                 end = _
             |- _ =>
             change Y with X in H ; consider X; intros; forward
         end.
    generalize (fun e => handle_uvar unifyOk tu tv e u s).
    consider (subst_lookup u s); intros.
    { forwardy.
      generalize dependent (UVar (typ:=typ) (func:=func) u).
      intros.
      inv_all. subst.
      destruct H2.
      eapply H5 in H4; eauto; clear H5.
      forward_reason; split; auto.
      intros.
      eapply ExprFacts.typeof_expr_exprD' in H; eauto.
      eapply ExprFacts.typeof_expr_exprD' in H1; eauto.
      forward_reason.
      do 2 eexists; split; eauto. }
    { specialize (H5 e s' t1 tv').
      forwardy.
      generalize dependent (UVar (typ:=typ) (func:=func) u).
      intros.
      inv_all; subst.
      change_rewrite H4 in H5.
      forward_reason.
      split; eauto.
      intros.
      eapply ExprFacts.typeof_expr_exprD' in H1; eauto.
      eapply ExprFacts.typeof_expr_exprD' in H; eauto.
      forward_reason.
      destruct H2.
      do 2 eexists.
      split; eauto. }
  Qed.

  Lemma handle_uvar_simul'
  : forall u s s' t (e : expr typ func) tv tu tv' unify
           (unifyOk : unify_sound unify),
      match subst_lookup u s with
        | Some e2' =>
          match typeof_expr tu (tv' ++ tv) (UVar u) with
            | Some t1 =>
              match typeof_expr tu (tv' ++ tv) e with
                | Some t2 =>
                  if t1 ?[ Rty ] t2
                  then
                    match
                      unify tu (tv' ++ tv) (length tv')
                            (lift 0 (length tv') e2') e t1 s
                    with
                      | Some s0 => Some (t1, s0)
                      | None => None
                    end
                  else None
                | None => None
              end
            | None => None
          end
        | None =>
          match lower 0 (length tv') e with
            | Some e' =>
              match typeof_expr tu (tv' ++ tv) (UVar u) with
                | Some t1 =>
                  match typeof_expr tu (tv' ++ tv) e with
                    | Some t2 =>
                      if t1 ?[ Rty ] t2
                      then
                        match subst_set u e' s with
                          | Some s0 => Some (t1, s0)
                          | None => None
                        end
                      else None
                    | None => None
                  end
                | None => None
              end
            | None => None
          end
      end = Some (t, s') ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      (forall sD : hlist typD tu -> hlist typD tv -> Prop,
         typeof_expr tu (tv' ++ tv) (UVar u) <> None ->
         typeof_expr tu (tv' ++ tv) e <> None ->
         substD tu tv s = Some sD ->
         exists v1 v2 : exprT tu (tv' ++ tv) (typD t),
           exprD' tu (tv' ++ tv) t (UVar u) = Some v1 /\
           exprD' tu (tv' ++ tv) t e = Some v2 /\
           (exists sD' : hlist typD tu -> hlist typD tv -> Prop,
              substR tu tv s s' /\
              substD tu tv s' = Some sD' /\
              (forall (us : hlist typD tu) (vs : hlist typD tv),
                 sD' us vs ->
                 sD us vs /\
                 (forall vs' : hlist typD tv',
                    v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs))))).
  Proof using RTypeOk RSymOk_func Typ2Ok_arr.
    intros.
    do 3 match goal with
           | H : match _ with
                 | Some _ => match ?X with _ => _ end
                 | None => match _ with
                           | Some _ =>
                             match ?Y with _ => _ end
                           | None => _
                           end
                 end = _
             |- _ =>
             change Y with X in H ; consider X; intros; forward
         end.
    generalize (fun e => handle_uvar' unifyOk tu tv e u s).
    consider (subst_lookup u s); intros.
    { forwardy.
      generalize dependent (UVar (typ:=typ) (func:=func) u).
      intros.
      inv_all. subst.
      destruct H2.
      eapply H5 in H4; eauto; clear H5.
      forward_reason; split; auto.
      intros.
      eapply ExprFacts.typeof_expr_exprD' in H; eauto.
      eapply ExprFacts.typeof_expr_exprD' in H1; eauto.
      forward_reason.
      do 2 eexists; split; eauto. }
    { specialize (H5 e s' t1 tv').
      forwardy.
      generalize dependent (UVar (typ:=typ) (func:=func) u).
      intros.
      inv_all; subst.
      change_rewrite H4 in H5.
      forward_reason.
      split; eauto.
      intros.
      eapply ExprFacts.typeof_expr_exprD' in H1; eauto.
      eapply ExprFacts.typeof_expr_exprD' in H; eauto.
      forward_reason.
      destruct H2.
      do 2 eexists.
      split; eauto. }
  Qed.

  Lemma exprUnify'_sound_mutual
  : forall (unify : unifier typ (expr typ func) subst)
           (unifyOk : unify_sound unify),
    forall tu tv e1 e2 s s' t tv',
      (exprUnify' unify tu (tv' ++ tv) (length tv') e1 e2 t s = Some s' ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall v1 v2 sD,
        exprD' tu (tv' ++ tv) t e1 = Some v1 ->
        exprD' tu (tv' ++ tv) t e2 = Some v2 ->
        substD tu tv s = Some sD ->
        exists sD',
             substR tu tv s s'
          /\ substD (expr := expr typ func) tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)) /\
      (exprUnify_simul' unify tu (tv' ++ tv) (length tv') e1 e2 s = Some (t,s') ->
      WellFormed_subst (expr := expr typ func) s ->
      WellFormed_subst (expr := expr typ func) s' /\
      forall sD,
        typeof_expr tu (tv' ++ tv) e1 <> None ->
        typeof_expr tu (tv' ++ tv) e2 <> None ->
        substD tu tv s = Some sD ->
        exists v1 v2,
          exprD' tu (tv' ++ tv) t e1 = Some v1 /\
          exprD' tu (tv' ++ tv) t e2 = Some v2 /\
          exists sD',
             substR tu tv s s'
          /\ substD (expr := expr typ func) tu tv s' = Some sD'
          /\ forall us vs,
               sD' us vs ->
               sD us vs /\
               forall vs',
                 v1 us (hlist_app vs' vs) = v2 us (hlist_app vs' vs)).
  Proof using RTypeOk RSymOk_func Typ2Ok_arr.
    intros unify unifyOk tu tv.
    induction e1.
    { (** Var **)
      split.
      { destruct e2; try solve [ simpl; congruence | eapply handle_uvar; eauto ].
        simpl.
        forward.
        inv_all; subst.
        split; auto. intros.
        change_rewrite H in H0.
        inv_all; subst. eexists; split; [ reflexivity | ]; eauto. }
      { rewrite exprUnify_simul'_eq.
        destruct e2; try solve [ simpl; congruence | eapply handle_uvar_simul with (e := Var v); eauto ].
        forward.
        eapply ExprFacts.typeof_expr_exprD' in H2; eauto.
        destruct H2.
        eapply ExprFacts.typeof_expr_exprD' in H0; eauto.
        destruct H0.
        inv_all; subst. destruct H3.
        split; auto.
        intros.
        do 2 eexists; split; eauto.
        split; eauto. eexists; split; [ reflexivity | eauto ]. } }
    { (** Inj **)
      simpl. split.
      { destruct e2; intros; try solve [ congruence | eapply handle_uvar; eauto ].
        { generalize (sym_eqbOk f f0).
          forward. inv_all; subst.
          split; auto.
          intros. eexists; split; eauto.
          reflexivity. split; eauto.
          match goal with
            | H : ?X = _ , H' : ?Y = _ |- _ =>
              change Y with X in H' ; rewrite H in H'
          end.
          inv_all; subst. subst. intuition. } }
      { unfold exprUnify_simul'.
        destruct e2; intros; try solve [ congruence | eapply handle_uvar_simul with (e := Inj f); eauto ].
        { generalize (sym_eqbOk f f0).
          forward; inv_all; subst.
          autorewrite with exprD_rw.
          split; auto; intros.
          remember (symAs f0 t) as oF.
          destruct oF.
          { simpl. do 2 eexists; split; eauto.
            split; eauto. eexists; split; [ reflexivity | eauto ]. }
          { exfalso. unfold symAs in HeqoF.
            revert HeqoF.
            match goal with
              | |- context [ @symD ?A ?B ?C ?D ?E ] =>
                generalize (@symD A B C D E)
            end.
            rewrite H2. rewrite type_cast_refl; eauto.
            compute. congruence. } } } }
    { (** App **)
      simpl; split.
      { destruct e2; try solve [ congruence | eapply handle_uvar; eauto ].
        { forward. subst.
          destruct (IHe1_1 e2_1 s s0 t0 tv'); clear IHe1_1; eauto.
          clear H. eapply H3 in H0; clear H3; eauto.
          destruct H0.
          destruct (typ2_match_case t0); eauto.
          { forward_reason.
            rewrite H3 in *; clear H3.
            unfold Relim in H2. red in x1. subst.
            rewrite eq_Const_eq in H2.
            destruct (IHe1_2 e2_2 s0 s' x tv'); clear IHe1_2; eauto.
            clear H4. forward_reason.
            split; auto.
            autorewrite with exprD_rw. simpl.
            intros; forward.
            eapply H0 in H7; eauto using exprD_typeof_not_None.
            forward_reason.
            forward_exprD.
            inv_all. subst.
            rewrite H14 in *. rewrite H7 in *. inv_all; subst.
            specialize (H4 _ _ _ H12 H9 H16).
            forward_reason.
            eexists; split; eauto.
            { etransitivity; eauto. }
            split; eauto.
            intros.
            eapply H10 in H11; clear H10.
            destruct H11. eapply H17 in H10; clear H17.
            forward_reason; split; auto.
            intros. eapply Open_App_equal; eauto. }
          { rewrite H3 in H2. congruence. } } }
      { (* rewrite exprUnify_simul'_eq. *)
        destruct e2; try solve [ congruence ].
        { intros; forward; subst.
          destruct (typ2_match_case t0); eauto.
          { forward_reason.
            rewrite H in *.
            rewrite eq_Const_eq in *.
            red in x1. subst. simpl Relim in *.
            forward. inv_all; subst.
            edestruct IHe1_1 as [ Hz Hx ]; eapply Hx in H1; clear Hx Hz IHe1_1; eauto.
            forward_reason.
            edestruct IHe1_2 as [ Hx Hz ]; eapply Hx in H2; clear Hx Hz IHe1_2; eauto.
            forward_reason. split; auto. simpl.
            intros. forward.
            eapply H10 in H7; try congruence; clear H10.
            forward_reason.
            autorewrite with exprD_rw. simpl.
            repeat match goal with
                     | H : ?X = _ |- context [ ?Y ] =>
                       change Y with X ; rewrite H
                   end.
            forward_exprD.
            intros; subst.
            unfold type_of_apply in *.
            rewrite typ2_match_iota in * by eauto.
            rewrite eq_Const_eq in *. forward.
            red in r. red in r0. subst. subst.
            eapply ExprFacts.typeof_expr_exprD' in H6; eauto.
            eapply ExprFacts.typeof_expr_exprD' in H8; eauto.
            forward_reason.
            repeat match goal with
                     | H : ?X = _ |- context [ ?Y ] =>
                       change Y with X ; rewrite H
                   end.
            do 2 eexists; split; [ | split ]; auto.
            specialize (H4 _ _ _ H6 H8 H13).
            forward_reason.
            eexists; split; eauto.
            { etransitivity; eauto. }
            split; eauto.
            intros.
            eapply H18 in H19; clear H18; destruct H19.
            eapply H14 in H18; clear H14; destruct H18.
            split; auto.
            intros.
            eapply Open_App_equal; eauto. }
          { exfalso. rewrite H in *. congruence. } }
        { intros. eapply handle_uvar_simul with (e := App e1_1 e1_2); eauto. } } }
    { (** Abs **)
      split.
      { simpl; destruct e2; intros; try solve [ congruence | eapply handle_uvar; eauto ].
        match goal with
          | H : typ2_match _ ?t _ _ = _ |- _ =>
            arrow_case t; try congruence
        end.
        { red in x1. subst.
          autorewrite with exprD_rw. simpl.
          do 2 rewrite H1.
          unfold Relim in H.
          clear H1.
          rewrite eq_Const_eq in H.
          destruct (IHe1 e2 s s' x0 (t :: tv')) as [ Hx Hy ] ; clear Hy.
          apply Hx in H; clear Hx; eauto. forward_reason.
          unfold Relim.
          split; auto. intros.
          repeat rewrite eq_option_eq in *.
          forward.
          inv_all; subst. destruct r; destruct r0.
          eapply H1 in H4; eauto.
          forward_reason.
          eexists; split; eauto. split; eauto.
          intros. eapply H7 in H8; clear H7.
          forward_reason. split; auto. intros.
          revert H8. clear.
          autorewrite with eq_rw.
          repeat match goal with
                   | H : ?X = _ , H' : ?Y = _ |- _ =>
                     change Y with X in H' ; rewrite H in H'
                 end.
          inv_all; subst.
          intro.
          match goal with
            | |- match ?X with _ => _ end = match ?Y with _ => _ end =>
              change Y with X ; generalize X
          end.
          intros. eapply match_eq_match_eq with (pf := e) (F := fun x => x).
          eapply functional_extensionality.
          intros. specialize (H8 (Hcons (Rcast_val eq_refl x1) vs')).
          auto. } }
      { rewrite exprUnify_simul'_eq.
        destruct e2; try solve [ congruence | intros; eapply handle_uvar_simul with (e := Abs t e1); eauto ].
        forward. inv_all; subst.
        destruct H.
        destruct (IHe1 e2 s s' t2 (t :: tv')) as [ Hx Hy ] ; clear Hx.
        eapply Hy in H2; clear Hy; eauto.
        forward_reason. split; auto.
        simpl; intros. forward.
        simpl in H0.
        eapply H0 in H4; try congruence.
        forward_reason.
        generalize (exprD_typeof_eq _ _ _ _ _ H4 H2).
        generalize (exprD_typeof_eq _ _ _ _ _ H7 H3).
        intros; subst. subst.
        autorewrite with exprD_rw. simpl.
        repeat rewrite typ2_match_iota by eauto.
        repeat rewrite type_cast_refl by eauto.
        Cases.rewrite_all_goal.
        repeat rewrite eq_option_eq.
        do 2 eexists; split; eauto. split; eauto.
        eexists; split; eauto. split; eauto.
        intros.
        eapply H10 in H11; clear H10.
        forward_reason; split; auto.
        intros.
        autorewrite with eq_rw.
        match goal with
          | |- match ?X with _ => _ end = _ =>
            eapply match_eq_match_eq with (pf := X) (F := fun x => x)
        end.
        eapply functional_extensionality.
        intros. exact (H11 (Hcons (Rcast_val (Rrefl t) x2) vs')). } }
    { (** UVar **)
      split.
      { simpl; destruct e2; intros; try solve [ congruence | eapply handle_uvar'; eauto ].
        consider (EqNat.beq_nat u u0).
        { intros; inv_all; subst.
          split; auto. intros. change_rewrite H in H1.
          inv_all; subst.
          eexists; split. reflexivity. eauto. }
        { intro XXX; clear XXX.
          consider (subst_lookup u s); consider (subst_lookup u0 s); intros.
          { eapply unifyOk in H2.
            forward_reason. split; auto.
            intros.
            eapply lookup_lift in H1; eauto.
            eapply lookup_lift in H; eauto.
            forward_reason.
            eapply H3 in H; clear H3; eauto.
            forward_reason. eexists; split; eauto.
            split; eauto.
            intros. eapply H9 in H10.
            forward_reason. split; auto.
            intros. rewrite H8; eauto. rewrite H7; eauto. }
          { eapply handle_set in H2; eauto.
            forward_reason; split; auto; intros.
            eapply substD_lookup in H1; eauto.
            forward_reason. simpl in *.
            autorewrite with exprD_rw in H4. simpl in H4.
            change_rewrite H1 in H4.
            forwardy.
            destruct y.
            specialize (H3 _ _ _ _ _ _ _ H7 H5 H6).
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros. eapply H11 in H12; clear H11.
            forward_reason; split; eauto.
            intros. inv_all; subst.
            etransitivity; [ eapply H8 ; eauto | eapply H12 ]. }
          { eapply handle_set in H2; eauto.
            forward_reason; split; auto; intros.
            eapply substD_lookup in H; eauto.
            forward_reason. simpl in *.
            autorewrite with exprD_rw in H5. simpl in H5.
            forward.
            (* change_rewrite H9 in H5. *) inv_all; subst.
            destruct r.
            specialize (H3 _ _ _ _ _ _ _ H7 H4 H6).
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros.
            eapply H10 in H11; forward_reason; split; eauto.
            intros. symmetry.
            etransitivity; [ eapply H8; eauto | eapply H12 ]. }
          { consider (subst_set u (UVar u0) s); intros.
            { inv_all; subst.
              eapply handle_set in H2; eauto.
              forward_reason; split; auto.
              intros.
              specialize (exprD'_lower nil tv' tv (UVar u0) t eq_refl H5).
              simpl. intros; forward_reason.
              eapply H3 in H6; eauto.
              forward_reason; eexists; split; eauto.
              split; eauto.
              intros. eapply H10 in H11; eauto.
              forward_reason; split; auto.
              intros. rewrite <- H12.
              symmetry.
              exact (H8 us Hnil vs' vs). }
            { clear H2. rename H3 into H2.
              inv_all; subst.
              eapply handle_set in H2; eauto.
              forward_reason; split; auto.
              intros.
              specialize (exprD'_lower nil tv' tv (UVar u) t eq_refl H4).
              simpl. intros; forward_reason.
              eapply H3 in H6; eauto.
              forward_reason; eexists; split; eauto. split; eauto.
              intros. eapply H10 in H11; eauto.
              forward_reason; split; auto.
              intros. rewrite <- H12.
              exact (H8 us Hnil vs' vs). } } } }
      { rewrite exprUnify_simul'_eq.
        destruct e2; try solve [ congruence | intros; eapply handle_uvar_simul'; eauto ].
        consider (EqNat.beq_nat u u0).
        { intros; subst.
          forward. inv_all; subst.
          split; eauto. simpl. intros.
          autorewrite with exprD_rw. simpl.
          match goal with
            | |- exists x y, match ?X with _ => _ end = _ /\
                             match ?Y with _ => _ end = _ /\ _ =>
              change Y with X ; consider X; intros
          end.
          { eapply nth_error_get_hlist_nth_Some in H4.
            forward_reason. destruct s. simpl in *.
            assert (x0 = t) by congruence.
            subst.
            repeat rewrite type_cast_refl by eauto.
            do 2 eexists; split; eauto. split; eauto.
            eexists; split; eauto. reflexivity. }
          { exfalso.
            eapply nth_error_get_hlist_nth_None in H4.
            congruence. } }
        { intro XXX; clear XXX.
          forward.
          eapply ExprFacts.typeof_expr_exprD' in H; eauto.
          eapply ExprFacts.typeof_expr_exprD' in H0; eauto.
          inv_all; subst.
          destruct H2.
          consider (subst_lookup u s); consider (subst_lookup u0 s); intros.
          { eapply unifyOk in H4.
            forward_reason. split; auto.
            intros. clear H6 H7.
            forward_reason.
            eapply lookup_lift in H2; eauto.
            eapply lookup_lift in H3; eauto.
            forward_reason.
            eapply H5 in H8; [ | eauto | eauto ].
            do 2 eexists; split; eauto. split; eauto.
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros.
            eapply H10 in H11; clear H10.
            forward_reason; split; auto.
            intros.
            rewrite H7; eauto.
            rewrite H6; eauto. }
          { eapply handle_set in H4; eauto.
            forward_reason; split; auto; intros.
            clear H4 H5.
            forward_reason.
            do 2 eexists; split; [ eassumption | split; [ eassumption | ] ].
            eapply substD_lookup in H3; eauto. forward_reason.
            autorewrite with exprD_rw in e0; simpl in e0.
            change_rewrite H3 in e0.
            forwardy. inv_all; subst; destruct y.
            specialize (H0 _ _ _ _ _ _ _ H4 e1 H6).
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros. eapply H9 in H10; forward_reason; split; eauto.
            intros.
            etransitivity; [ eapply H5; eauto | eauto ]. }
          { eapply handle_set in H4; eauto.
            forward_reason; split; auto; intros.
            clear H4 H5.
            forward_reason.
            do 2 eexists; split; [ eassumption | split; [ eassumption | ] ].
            eapply substD_lookup in H2; eauto. forward_reason.
            simpl in H2.
            autorewrite with exprD_rw in e1; simpl in e1.
            change_rewrite H2 in e1.
            forwardy; inv_all; subst. destruct y.
            specialize (H0 _ _ _ _ _ _ _ H4 e0 H6).
            forward_reason.
            eexists; split; eauto. split; eauto.
            intros. eapply H9 in H10.
            forward_reason; split; eauto.
            intros. symmetry.
            etransitivity; [ eapply H5; eauto | eauto ]. }
          { consider (subst_set u (UVar u0) s); intros.
            { inv_all; subst.
              eapply handle_set in H4; eauto.
              forward_reason; split; auto.
              intros. clear H4 H5.
              forward_reason.
              specialize (exprD'_lower nil tv' tv (UVar u0) t eq_refl e0).
              intros; forward_reason.
              simpl in *. eapply H0 in H6; eauto.
              forward_reason.
              do 2 eexists; split; [ eassumption | split; [ eassumption | ] ].
              eexists; split; [ eassumption | ].
              split; eauto.
              intros.
              eapply H8 in H9; forward_reason; split; auto.
              intros.
              specialize (H5 us Hnil vs' vs); simpl in H5.
              rewrite <- H10. auto. }
            { clear H4. rename H5 into H4.
              inv_all; subst.
              eapply handle_set in H4; eauto.
              forward_reason; split; auto.
              intros. clear H4 H5.
              forward_reason.
              specialize (exprD'_lower nil tv' tv (UVar u) t eq_refl e).
              intros; forward_reason.
              simpl in *. eapply H0 in H6; eauto.
              forward_reason.
              do 2 eexists; split; [ eassumption | split; [ eassumption | ] ].
              eexists; split; [ eassumption | ]. split; eauto.
              intros.
              eapply H8 in H9; forward_reason; split; auto.
              intros.
              specialize (H5 us Hnil vs' vs); simpl in H5.
              rewrite <- H10. auto. } } } } }
  Qed.

  Theorem exprUnify'_sound
  : forall unify,
      unify_sound_ind unify ->
      unify_sound_ind (exprUnify' unify).
  Proof using RTypeOk RSymOk_func Typ2Ok_arr.
    intros.
    red. intros.
    eapply exprUnify'_sound_mutual in H.
    destruct H.
    eauto.
  Qed.

  Theorem exprUnify_sound : forall fuel, unify_sound (exprUnify fuel).
  Proof using RTypeOk RSymOk_func Typ2Ok_arr.
    induction fuel; simpl; intros; try congruence.
    eapply exprUnify'_sound. eassumption.
  Qed.

End typed.
