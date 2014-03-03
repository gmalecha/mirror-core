Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Subst2.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Import FMapPositive.PositiveMap.

  Let uvar := nat.
  Variables typ expr : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : @Expr typ typD expr.

  Definition pmap := t.
  Definition pset := pmap unit.
  Definition In_pset (p : positive) (s : pset) : Prop :=
    find p s = Some tt.

  Fixpoint pset_union (a b : pset) : pset :=
    match a , b with
      | Leaf , x => x
      | x , Leaf => x
      | Node la a ra , Node lb b rb =>
        Node (pset_union la lb) (match a , b with
                                   | None , None => None
                                   | _ , _ => Some tt
                                 end) (pset_union ra rb)
    end.

  Variable mentionsU : expr -> uvar -> Prop.
  Variable get_mentions_instantiate : (uvar -> option expr) -> expr -> pset * expr.
  Variable instantiate : (uvar -> option expr) -> expr -> expr.

  Definition ExprData : Type :=
    sum (prod expr pset) pset.

  Definition fast_subst : Type :=
    pmap ExprData.

  Definition to_key : nat -> positive := fun x => Pos.of_nat (S x).
  Definition from_key : positive -> nat := fun x => pred (Pos.to_nat x).

  Definition mentionsOnly (e : expr) (s : pset) : Prop :=
    forall u,
      mentionsU e u ->
      find (to_key u) s = Some tt.

  Definition mentionedBy (k : positive) (ps : pset) (fs : fast_subst) : Prop :=
    forall k' e m,
      find k' fs = Some (inl (e,m)) ->
      mentionsU e (from_key k) ->
      find k' ps = Some tt.

  Definition mentionsNone u (fs : fast_subst) : Prop :=
    forall p' : positive,
      match find p' fs with
        | Some (inl (e,_)) => ~mentionsU e u
        | _ => True
      end.

  Definition WellFormed_fast_subst (fs : fast_subst) : Prop :=
    forall p,
      match find p fs with
        | Some e =>
          match e with
            | inl (e, m) =>
              mentionsOnly e m /\ mentionsNone (from_key p) fs
            | inr mb =>
              mentionedBy p mb fs
          end
        | None => mentionedBy p (empty _) fs
      end.

  Theorem to_key_from_key : forall x, from_key (to_key x) = x.
  Proof.
    unfold to_key, from_key.
    intros. rewrite Pnat.Nat2Pos.id. reflexivity. auto.
  Qed.

  Theorem from_key_to_key : forall x, to_key (from_key x) = x.
  Proof.
    unfold to_key, from_key.
    intros.
    remember (Pos.to_nat x). destruct n.
    { exfalso.
      generalize (Pnat.Pos2Nat.is_pos x). omega. }
    { simpl pred. rewrite Heqn.
      rewrite Pnat.Pos2Nat.id. reflexivity. }
  Qed.

  Definition fs_lookup (s : fast_subst) (u : uvar) : option expr :=
    match find (to_key u) s with
      | Some (inl (e,_)) => Some e
      | _ => None
    end.

  Definition fast_subst_lookup (u : uvar) (s : fast_subst) : option expr :=
    match find (to_key u) s with
      | Some (inl (e,_)) => Some e
      | _ => None
    end.

  Let RelDec_eq_uvar : RelDec (@eq uvar) := RelDec_eq.
  Local Existing Instance RelDec_eq_uvar.

  Definition set_helper_mentionedBy (u : uvar) (up : positive) (e : expr) (mb : pset)
             (fs : fast_subst) : option fast_subst :=
    let (mentions, e_inst) :=
        @get_mentions_instantiate (fs_lookup fs) e
    in
    if find up mentions then None
    else
      Some (fold (fun p _ acc =>
                    match find p acc with
                      | None =>
                        acc (** dead code **)
                      | Some (inr mb) =>
                        acc (** dead code **)
                      | Some (inl (e,m)) =>
                        add p (inl (instantiate (fun x => if x ?[ eq ] u then
                                                            Some e_inst
                                                          else None) e,
                                    remove up (pset_union mentions m))) acc
                    end)
                 mb
                 (fold (fun p _ acc =>
                          match find p acc with
                            | None =>
                              add p (inr (add up tt (empty _))) acc
                            | Some (inr mb) =>
                              add p (inr (add up tt mb)) acc
                            | Some (inl (e,m)) =>
                              (** dead code **) acc
                          end)
                       mentions
                       (add up (inl (e_inst, mentions)) fs))).

  Definition fast_subst_set (u : uvar) (e : expr) (s : fast_subst)
  : option fast_subst :=
    let up := to_key u in
    match find up s with
      | Some (inl _) => None
      | Some (inr mb) => set_helper_mentionedBy u up e mb s
      | None => set_helper_mentionedBy u up e (empty _) s
    end.

  Definition fast_subst_empty : fast_subst :=
    empty _.

  Fixpoint fast_subst_pull' (base : positive) (n : nat) (fs : fast_subst) {struct n}
  : option fast_subst :=
    match n with
      | 0 => Some fs
      | S n =>
        match find base fs with
          | None
          | Some (inr _) => None
          | Some (inl _) =>
            fast_subst_pull' (Pos.succ base) n (remove base fs)
        end
    end.

  Definition fast_subst_pull (base : uvar) := fast_subst_pull' (to_key base).

  Fixpoint filter_map T U (f : T -> option U) (ls : list T) : list U :=
    match ls with
      | nil => nil
      | l :: ls => match f l with
                     | None => filter_map f ls
                     | Some x => x :: filter_map f ls
                   end
    end.


  Instance Subst_fast_subst : Subst fast_subst expr :=
  { lookup := fast_subst_lookup
  ; domain := fun x => filter_map (fun x =>
                                     match snd x with
                                       | inl _ => Some (from_key (fst x))
                                       | _ => None
                                     end) (elements x)
  }.

  Definition WellTyped_fast_subst (tus tvs : EnvI.tenv typ) (s : fast_subst) : Prop :=
    forall u e, lookup u s = Some e ->
                match List.nth_error tus u with
                  | None => False
                  | Some t => Safe_expr tus tvs e t
                end.

  Definition substD_fast_subst (us vs : EnvI.env typD) (s : fast_subst) : list Prop :=
    fold (fun p e acc =>
            match e with
              | inl (e,_) =>
                match List.nth_error us (from_key p) with
                  | None => False :: acc
                  | Some (existT ty val) =>
                    match exprD us vs e ty with
                      | Some val' => (val' = val) :: acc
                      | None => False :: acc
                    end
                end
              | inr _ => acc
            end) s nil.

  Definition substD_fast_subst' (us vs : EnvI.env typD) (s : fast_subst) : list Prop :=
    List.map (fun p_e =>
           let '(p,e) := p_e in
           match e with
             | inl (e,_) =>
               match List.nth_error us (from_key p) with
                 | None => False
                 | Some (existT ty val) =>
                   match exprD us vs e ty with
                     | Some val' => (val' = val)
                     | None => False
                   end
               end
             | inr _ => True
           end) (elements s).

  Lemma Forall_cons_iff : forall T (P : T -> Prop) l ls,
                            Forall P (l :: ls) <-> P l /\ Forall P ls.
  Proof.
    clear.
    intuition;
      inversion H; auto.
  Qed.
  Lemma Forall_app : forall T (P : T -> Prop) ls ls',
                       Forall P (ls ++ ls') <-> Forall P ls /\ Forall P ls'.
  Proof.
    induction ls; simpl in *; intros.
    { intuition. }
    { do 2 rewrite Forall_cons_iff. rewrite IHls. intuition. }
  Qed.

  Theorem substD_fast_subst_substD_fast_subst'
  : forall us vs s,
      Forall (fun x => x) (substD_fast_subst us vs s) <->
      Forall (fun x => x) (substD_fast_subst' us vs s).
  Proof.
    unfold substD_fast_subst, substD_fast_subst'; intros.
    rewrite fold_1.
    assert (forall l,
                      (Forall (fun x : Prop => x)
                              (fold_left
                                 (fun (a : list Prop) (p : key * (expr * pset + pset)) =>
                                    match snd p with
                                      | inl (e, _) =>
                                        match nth_error us (from_key (fst p)) with
                                          | Some (existT ty val) =>
                                            match exprD us vs e ty with
                                              | Some val' => (val' = val) :: a
                                              | None => False :: a
                                            end
                                          | None => False :: a
                                        end
                                      | inr _ => a
                                    end) (elements s) l)
                      <->
                      Forall (fun x : Prop => x)
                             (l ++ List.map
                                (fun p_e : positive * (expr * pset + pset) =>
                                   match p_e with
                                     | (p, inl (e0, _)) =>
                                       match nth_error us (from_key p) with
                                         | Some (existT ty val) =>
                                             match exprD us vs e0 ty with
                                               | Some val' => val' = val
                                               | None => False
                                             end
                                         | None => False
                                       end
                                     | (p, inr _) => True
                                   end) (elements s)))
           ).
    { induction (elements s).
      { simpl. intros. rewrite app_nil_r. intuition. }
      { intros. destruct a. destruct e.
        { simpl in *. destruct p0.
          destruct (nth_error us (from_key p)).
          { destruct s0. destruct (exprD us vs e x).
            { rewrite IHl.
              repeat rewrite Forall_app. repeat rewrite Forall_cons_iff.
              tauto. }
            { rewrite IHl.
              repeat rewrite Forall_app. repeat rewrite Forall_cons_iff.
              tauto. } }
          { rewrite IHl.
            repeat rewrite Forall_app. repeat rewrite Forall_cons_iff.
            tauto. } }
        { simpl. rewrite IHl.
          repeat rewrite Forall_app. repeat rewrite Forall_cons_iff.
          tauto. } } }
    { specialize (H nil).
      simpl in *. apply H. }
  Qed.

  Lemma WellTyped_lookup_fast_subst
  : forall (u v : EnvI.tenv typ) (s : fast_subst) (uv : nat) (e : expr),
      WellFormed_fast_subst s ->
      WellTyped_fast_subst u v s ->
      lookup uv s = Some e ->
      exists t0 : typ, List.nth_error u uv = Some t0 /\ Safe_expr u v e t0.
  Proof.
    unfold WellTyped_fast_subst; simpl; intros.
    apply H0 in H1.
    forward. eauto.
  Qed.

  (** TODO: Move **)
  Lemma Forall_map
  : forall T U (f : T -> U) P ls,
      Forall P (List.map f ls) <-> Forall (fun x => P (f x)) ls.
  Proof.
    induction ls; simpl.
    { split; intros; constructor. }
    { split; inversion 1; intros; subst; constructor; auto.
      apply IHls. auto. apply IHls. auto. }
  Qed.

  Lemma substD_lookup_fast_subst
  : forall (u v : EnvI.env typD) (s : fast_subst) (uv : nat) (e : expr),
      WellFormed_fast_subst s ->
      lookup uv s = Some e ->
      List.Forall (fun x : Prop => x) (substD_fast_subst u v s) ->
      exists val : sigT (typD nil),
        List.nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val).
  Proof.
    simpl. intros. clear H.
    unfold fast_subst_lookup in *; simpl in *.
    forward. inv_all; subst.
    rewrite substD_fast_subst_substD_fast_subst' in H1.
    unfold substD_fast_subst' in H1.
    rewrite Forall_map in H1.
    generalize (elements_correct s (to_key uv) H2).
    intros.
    eapply Forall_forall in H1; eauto.
    simpl in *.
    forward. subst.
    rewrite to_key_from_key in *. eauto.
  Qed.

  Lemma in_filter_map_iff : forall T U (P : T -> option U) ls x,
                              List.In x (filter_map P ls) <->
                              exists y, P y = Some x /\ List.In y ls.
  Proof.
    clear.
    induction ls; simpl.
    { intuition. destruct H; intuition. }
    { intuition.
      { consider (P a); intros.
        { destruct H0. subst. eauto.
          eapply IHls in H0. destruct H0. intuition; eauto. }
        { eapply IHls in H0. destruct H0; intuition; eauto. } }
      { destruct H. destruct H.
        destruct H0; subst.
        { rewrite H. left. auto. }
        { destruct (P a); try right; apply IHls; eauto. } } }
  Qed.

  Lemma WellFormed_domain_fast_subst
  : forall (s : fast_subst) (ls : list nat),
      WellFormed_fast_subst s ->
      domain s = ls -> forall n : nat, List.In n ls <-> lookup n s <> None.
  Proof.
    intros; subst.
    unfold domain, fast_subst_lookup. simpl.
    unfold fast_subst_lookup.
    rewrite in_filter_map_iff.
    split; intros.
    { destruct H0. intuition.
      forward. inv_all; subst.
      rewrite from_key_to_key in H1.
      generalize (elements_complete s (fst x) (snd x)).
      unfold ExprData in *.
      cutrewrite ((fst x, snd x) = x); [ | (destruct x; reflexivity) ].
      intros. apply H2 in H3. rewrite H3 in H1. rewrite H0 in *.
      destruct p; congruence. }
    { generalize (elements_correct s (to_key n)).
      forward. subst.
      specialize (H4 _ eq_refl).
      eexists. split; eauto. simpl.
      rewrite to_key_from_key. auto. }
  Qed.

  Instance SubstOk_fast_subst : SubstOk _ Subst_fast_subst :=
  { WellFormed_subst := WellFormed_fast_subst
  ; WellTyped_subst := WellTyped_fast_subst
  ; substD := substD_fast_subst
  ; WellTyped_lookup := WellTyped_lookup_fast_subst
  ; substD_lookup := substD_lookup_fast_subst
  ; WellFormed_domain := WellFormed_domain_fast_subst
  }.

  Instance SubstUpdate_fast_subst : SubstUpdate fast_subst expr :=
  { empty := fast_subst_empty
  ; pull := fast_subst_pull
  ; set := fast_subst_set
  }.

  Hypothesis get_mentions_instantiateOk
  : forall f e s e',
      get_mentions_instantiate f e = (s, e') ->
      e' = instantiate f e /\
      (forall u, mentionsU e u -> mem (to_key u) s = true).

  Definition self_instantiated (f : uvar -> option expr) : Prop :=
    forall x e, f x = Some e ->
                forall y,
                  f y <> None -> ~mentionsU e y.

  Hypothesis mentionsU_instantiate_complete
  : forall f, self_instantiated f ->
              forall u e,
                mentionsU (instantiate f e) u ->
                f u = None.
  Hypothesis instantiate_exprD
  : forall f us vs e t,
      (forall u t' val,
         f u = Some e ->
         nth_error us u = Some (existT _ t' val) /\
         exprD us vs e t' = Some val) ->
      exprD us vs (instantiate f e) t = exprD us vs e t.
  Hypothesis instantiate_typed
  : forall f tus tvs e t,
      (forall u t',
         f u = Some e ->
         nth_error tus u = Some t' /\
         Safe_expr tus tvs e t') ->
      Safe_expr tus tvs (instantiate f e) t <-> Safe_expr tus tvs e t.

  Lemma All_set_fast_subst
  : forall (uv : nat) (e : expr) (s s' : fast_subst),
      WellFormed_subst s ->
      set uv e s = Some s' ->
      WellFormed_subst s' /\
      forall tus tvs t,
        WellTyped_subst tus tvs s ->
        Safe_expr tus tvs e t ->
        nth_error tus uv = Some t ->
        WellTyped_subst tus tvs s' /\
        forall us vs,
          Forall (fun x => x) (substD us vs s') ->
          Forall (fun x => x) (substD us vs s) /\
          (forall tv : sigT (typD nil),
             nth_error us uv = Some tv -> exprD us vs e (projT1 tv) = Some (projT2 tv)).
  Proof.
    simpl. unfold fast_subst_set; simpl; intros.
    forward. inv_all.
    match goal with
      | |- ?G =>
        assert (forall mb, mentionedBy (to_key uv) mb s ->
                           set_helper_mentionedBy uv (to_key uv) e mb s = Some s' ->
                           G)
    end.
    { admit. }
    { red in H. specialize (H (to_key uv)).
      destruct (find (to_key uv) s); eauto.
      { destruct e0; try congruence; eauto. } }
  Qed.

  Instance SubstUpdateOk_fast_subst : SubstUpdateOk SubstUpdate_fast_subst _.
  Proof.
    constructor.
    { red; simpl. red. unfold fast_subst_empty. simpl.
      intros. rewrite gempty. red. intros.
      rewrite gempty in H. congruence. }
    { compute. constructor. }
    { red. simpl. red. simpl.
      unfold fast_subst_lookup.
      intros. destruct (to_key u0); compute in H; try congruence. }
    { intros.
      specialize (@All_set_fast_subst uv e s s' H H0).
      tauto. }
    { intros.
      destruct (@All_set_fast_subst uv e s s' H H3).
      specialize (@H5 u v t0 H0 H2 H1).
      tauto. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
  Qed.

End parametric.

(** For Expr (TODO: this should move to Ext/ExprSubst **)
Section funced.
  Require Import MirrorCore.Ext.ExprCore.
  Require Import MirrorCore.Ext.ExprSubst.

  Variable func : Type.

  Definition instantiate : (uvar -> option (expr func)) -> expr func -> expr func :=
    fun z => ExprSubst.instantiate z 0.

  Fixpoint get_mentions (e : expr func) (acc : pset) : pset :=
    match e with
      | Var _
      | Inj _ => acc
      | App l r => get_mentions l (get_mentions r acc)
      | Abs _ e => get_mentions e acc
      | UVar u => PositiveMap.add (to_key u) tt acc
    end.

  Definition get_mentions_instantiate (i : uvar -> option (expr func)) (e : expr func)
  : pset * expr func :=
    let e' := instantiate i e in
    (get_mentions e' (PositiveMap.empty _), e').

(*
  Definition l := @fast_subst_lookup (expr func).
  Definition e := @fast_subst_empty (expr func).
  Definition s := @fast_subst_set (expr func) get_mentions_instantiate instantiate.
  Definition d := @fast_subst_pull (expr func).

  Require Import ExtLib.Structures.Monad.
  Require Import ExtLib.Data.Monads.OptionMonad.

  Eval compute in s 0 (UVar 1) e.
  Eval compute in bind (s 1 (Inj 2) e) (fun x => bind (s 0 (UVar 1) x) (d 1 1)).
  Eval compute in bind (s 0 (UVar 1) e) (fun x => bind (s 1 (Inj 2) x) (d 0 2)).
*)

End funced.
