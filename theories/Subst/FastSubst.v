Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.
Require Coq.FSets.FMapFacts.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI2.

Set Implicit Arguments.
Set Strict Implicit.

Import FMapPositive.PositiveMap.

Module Facts := FMapFacts.Facts PositiveMap.

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


Section parametric.

  Let uvar := nat.
  Variables typ expr : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : @Expr typ typD expr.
  Variable ExprOk_expr : ExprOk Expr_expr.

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

  Inductive ExprData : Type :=
  | Mapped (e : expr) (p : pset) (** [e] mentions only things in [p] **)
  | UnMapped (p : pset) (** only elements in [p] mention this index **).

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
      find k' fs = Some (Mapped e m) ->
      mentionsU e (from_key k) ->
      find k' ps = Some tt.

  Definition mentionsNone u (fs : fast_subst) : Prop :=
    forall p' : positive,
      match find p' fs with
        | Some (Mapped e _) => ~mentionsU e u
        | _ => True
      end.

  Definition WellFormed_fast_subst (fs : fast_subst) : Prop :=
    forall p,
      match find p fs with
        | Some e =>
          match e with
            | Mapped e m =>
              mentionsOnly e m /\ mentionsNone (from_key p) fs
            | UnMapped mb =>
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
      | Some (Mapped e _) => Some e
      | _ => None
    end.

  Definition fast_subst_lookup (u : uvar) (s : fast_subst) : option expr :=
    match find (to_key u) s with
      | Some (Mapped e _) => Some e
      | _ => None
    end.

  Let RelDec_eq_uvar : RelDec (@eq uvar) := RelDec_eq.
  Local Existing Instance RelDec_eq_uvar.

  (** This function records that [up] mentions every variable in [s] **)
  Definition add_mentionedBy (up : positive) (s : pset)
  : fast_subst -> fast_subst :=
    fold (fun p _ acc =>
            match find p acc with
              | None =>
                add p (UnMapped (add up tt (empty _))) acc
              | Some (UnMapped mb) =>
                add p (UnMapped (add up tt mb)) acc
              | Some (Mapped e m) =>
                acc (** dead code **)
            end)
         s.

  (** This function instantiates each variable in [s] by applying [mu] to update
   ** the [mentions] field and [i] to update the [expr] field
   **)
  Definition instantiate_current (mu : pset -> pset) (i : expr -> expr) (s : pset)
  : fast_subst -> fast_subst :=
    fold (fun p _ acc =>
            match find p acc with
              | None =>
                acc (** dead code **)
              | Some (UnMapped mb) =>
                acc (** dead code **)
              | Some (Mapped e m) =>
                add p (Mapped (i e) (mu m)) acc
            end) s.

  (** An fmap over the finite map might be more efficient in some cases, but
   ** in general, we expect to only be updating a few elements
   **)
  Definition set_helper_mentionedBy (u : uvar) (up : positive) (e : expr) (mb : pset)
             (fs : fast_subst) : option fast_subst :=
    let (mentions, e_inst) :=
        @get_mentions_instantiate (fs_lookup fs) e
    in
    if find up mentions then None
    else
      Some (add up (Mapped e_inst mentions)
                (instantiate_current
                   (fun m => remove up (pset_union mentions m))
                   (instantiate (fun x => if x ?[ eq ] u then
                                            Some e_inst
                                          else None))
                   mb
                   (add_mentionedBy up mentions fs))).


  Definition pm_left {T} (m : pmap T) :=
    match m with
      | Leaf => Leaf _
      | Node l _ _ => l
    end.
  Definition pm_right {T} (m : pmap T) :=
    match m with
      | Leaf => Leaf _
      | Node _ _ r => r
    end.
  Definition pm_here {T} (m : pmap T) :=
    match m with
      | Leaf => None
      | Node _ d _ => d
    end.

  Section update_1.
    Variable update : option ExprData -> ExprData.

    Fixpoint update_1
             (mb : pset) (fs : fast_subst) : fast_subst :=
      match mb with
        | Leaf => fs
        | Node l d r =>
          match fs with
            | Leaf => Node (update_1 l (Leaf _))
                           match d with
                             | None => None
                             | Some _ => Some (update None)
                           end
                           (update_1 r (@Leaf _))
            | Node sl sd sr => Node (update_1 l sl)
                                    match d with
                                      | None => sd
                                      | Some _ => Some (update sd)
                                    end
                                    (update_1 r sr)
          end
      end.
  End update_1.

  Section update_both.
    Variable update : bool -> bool -> option ExprData -> ExprData.

    Fixpoint update_both
             (mb : pset) (mentions : pset) (fs : fast_subst) : fast_subst :=
      match mb with
        | Leaf => update_1 (update false true) mentions fs
        | Node l d r =>
          match mentions with
            | Leaf => update_1 (update true false) mb fs
            | Node l' d' r' =>
              Node (update_both l l' (pm_left fs))
                   match d , d' with
                     | None , None => pm_here fs
                     | Some _ , None => Some (update true false (pm_here fs))
                     | None , Some _ => Some (update false true (pm_here fs))
                     | Some _ , Some _ => Some (update true true (pm_here fs))
                   end
                   (update_both r r' (pm_right fs))
          end
      end.

    Hypothesis update_false_false : forall x, update false false (Some x) = x.

    Lemma update_1_true_false
    : forall m fs,
        update_1 (update true false) m fs = update_both m (Leaf _) fs.
    Proof.
      clear - update_false_false.
      destruct m; simpl; auto.
    Qed.

    Lemma update_1_false_true
    : forall m fs,
        update_1 (update false true) m fs = update_both (Leaf _) m fs.
    Proof.
      clear - update_false_false.
      destruct m; simpl; auto.
    Qed.

    Lemma mem_empty : forall T k, mem k (empty T) = false.
    Proof.
      destruct k; reflexivity.
    Qed.

    Lemma update_both_spec
    : forall mb men fs k,
        find k (update_both mb men fs) =
        match find k fs with
          | None => if mem k mb || mem k men then
                      Some (update (mem k mb) (mem k men) None)
                    else
                      None
          | Some v => Some (update (mem k mb) (mem k men) (Some v))
        end.
    Proof.
      induction mb; induction men; simpl; intros.
      { simpl. change (Leaf unit) with (empty unit).
        repeat rewrite mem_empty.
        simpl. destruct (find k fs); auto.
        rewrite update_false_false. reflexivity. }
      { destruct fs.
         { destruct k; simpl; repeat rewrite update_1_false_true.
           { rewrite IHmen2.
             change (Leaf ExprData) with (empty ExprData).
             rewrite gempty.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. simpl. reflexivity. }
           { rewrite IHmen1.
             change (Leaf ExprData) with (empty ExprData).
             rewrite gempty.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. simpl. reflexivity. }
           { destruct o; reflexivity. } }
         { destruct k; simpl; repeat rewrite update_1_false_true.
           { rewrite IHmen2.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. reflexivity. }
           { rewrite IHmen1.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. reflexivity. }
           { destruct o; destruct o0; auto.
             rewrite update_false_false. reflexivity. } } }
      { destruct fs.
        { change (Leaf ExprData) with (empty ExprData).
          rewrite gempty.
          change (Leaf unit) with (empty unit).
          rewrite mem_empty.
          rewrite orb_false_r.
          destruct k; simpl; repeat rewrite update_1_true_false;
          Cases.rewrite_all_goal.
          { rewrite gempty.
            change Leaf with empty.
            rewrite mem_empty.
            rewrite orb_false_r. reflexivity. }
          { change Leaf with empty.
            rewrite mem_empty. rewrite gempty.
            rewrite orb_false_r. reflexivity. }
          { destruct o; auto. } }
        { destruct k; simpl; repeat rewrite update_1_true_false;
          Cases.rewrite_all_goal.
          { change Leaf with empty. rewrite mem_empty.
            reflexivity. }
          { change Leaf with empty. rewrite mem_empty.
            reflexivity. }
          { destruct o; destruct o0; auto.
            rewrite update_false_false. auto. } } }
      { destruct k; simpl.
        { rewrite IHmb2.
          destruct fs; simpl.
          { change Leaf with empty. rewrite gempty. reflexivity. }
          { reflexivity. } }
        { rewrite IHmb1; destruct fs; simpl; auto.
          change Leaf with empty; rewrite gempty; auto. }
        { destruct o; destruct o0; destruct fs; simpl; auto; destruct o; auto.
          rewrite update_false_false. reflexivity. } }
    Qed.
  End update_both.

  Section update_both'.
    Section update_1'.
      Variable update' : option ExprData -> option ExprData.

      Fixpoint update_1'
               (mb : pset) (fs : fast_subst) : fast_subst :=
        match mb with
          | Leaf => fs
          | Node l d r =>
            match fs with
              | Leaf => Node (update_1' l (Leaf _))
                             match d with
                               | None => None
                               | Some _ => update' None
                             end
                             (update_1' r (@Leaf _))
              | Node sl sd sr => Node (update_1' l sl)
                                      match d with
                                        | None => sd
                                        | Some _ => update' sd
                                      end
                                      (update_1' r sr)
            end
        end.
    End update_1'.


    Variable update : bool -> bool -> option ExprData -> option ExprData.


    Fixpoint update_both'
             (mb : pset) (mentions : pset) (fs : fast_subst) : fast_subst :=
      match mb with
        | Leaf => update_1' (update false true) mentions fs
        | Node l d r =>
          match mentions with
            | Leaf => update_1' (update true false) mb fs
            | Node l' d' r' =>
              Node (update_both' l l' (pm_left fs))
                   (update (match d with Some _ => true | None => false end)
                           (match d' with Some _ => true | None => false end)
                           (pm_here fs))
                   (update_both' r r' (pm_right fs))
          end
      end.

    Hypothesis update_false_false : forall x, update false false x = x.

    Lemma update_1_true_false'
    : forall m fs,
        update_1' (update true false) m fs = update_both' m (Leaf _) fs.
    Proof.
      clear - update_false_false.
      destruct m; simpl; auto.
    Qed.

    Lemma update_1_false_true'
    : forall m fs,
        update_1' (update false true) m fs = update_both' (Leaf _) m fs.
    Proof.
      clear - update_false_false.
      destruct m; simpl; auto.
    Qed.

    Lemma update_both_spec'
    : forall mb men fs k,
        find k (update_both' mb men fs) = update (mem k mb) (mem k men) (find k fs).
    Proof.
      induction mb; induction men; simpl; intros.
      { simpl. change (Leaf unit) with (empty unit).
        repeat rewrite mem_empty.
        simpl. destruct (find k fs); auto. }
      { destruct fs.
         { destruct k; simpl; repeat rewrite update_1_false_true'.
           { rewrite IHmen2.
             change (Leaf ExprData) with (empty ExprData).
             rewrite gempty.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. simpl. reflexivity. }
           { rewrite IHmen1.
             change (Leaf ExprData) with (empty ExprData).
             rewrite gempty.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. simpl. reflexivity. }
           { destruct o; try reflexivity. rewrite update_false_false. reflexivity. } }
         { destruct k; simpl; repeat rewrite update_1_false_true'.
           { rewrite IHmen2.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. reflexivity. }
           { rewrite IHmen1.
             change (Leaf unit) with (empty unit).
             rewrite mem_empty. reflexivity. }
           { destruct o; destruct o0; auto. } } }
      { destruct fs.
        { change (Leaf ExprData) with (empty ExprData).
          rewrite gempty.
          change (Leaf unit) with (empty unit).
          rewrite mem_empty.
          destruct k; simpl; repeat rewrite update_1_true_false';
          Cases.rewrite_all_goal.
          { rewrite gempty.
            change Leaf with empty.
            rewrite mem_empty. reflexivity. }
          { change Leaf with empty.
            rewrite mem_empty. rewrite gempty.
            reflexivity. }
          { destruct o; auto. } }
        { destruct k; simpl; repeat rewrite update_1_true_false';
          Cases.rewrite_all_goal.
          { change Leaf with empty. rewrite mem_empty.
            reflexivity. }
          { change Leaf with empty. rewrite mem_empty.
            reflexivity. }
          { destruct o; destruct o0; auto. } } }
      { destruct k; simpl.
        { rewrite IHmb2.
          destruct fs; simpl.
          { change Leaf with empty. rewrite gempty. reflexivity. }
          { reflexivity. } }
        { rewrite IHmb1; destruct fs; simpl; auto.
          change Leaf with empty; rewrite gempty; auto. }
        { destruct o; destruct o0; destruct fs; simpl; auto; destruct o; auto. } }
    Qed.
  End update_both'.


  Definition the_update_function' (up : positive) (i : expr -> expr) (mu : pset -> pset)
             (mb mem : bool) : option ExprData -> option ExprData :=
    match mb , mem with
      | false , false => fun x => x
      | true , false => fun x =>
                          match x with
                            | None => None
                            | Some (UnMapped mb) =>
                              None (* Some (UnMapped DEAD4 (** dead code **) *)
                            | Some (Mapped e m) =>
                              Some (Mapped (i e) (mu m))
                          end
      | false , true => fun x =>
                          match x with
                            | None =>
                              Some (UnMapped (add up tt (empty _)))
                            | Some (UnMapped mb) =>
                              Some (UnMapped (add up tt mb))
                            | Some (Mapped e m) =>
                              None (* DEAD2 (** dead code **) *)
                          end
      | true , true => fun _ => None
    end.

  Lemma the_update_function'_Mapped
  : forall up i mu mb mm o e' d',
      the_update_function' up i mu mb mm o = Some (Mapped e' d') ->
      match o with
        | Some (Mapped e d) =>
          mb = true /\ mm = false /\ i e = e' /\ mu d = d'
        | _ => False
      end.
  Proof.
    clear. unfold the_update_function'; intros.
    destruct mb; destruct mm; destruct o; forward; try congruence.
    inv_all; subst.
  Admitted.

(*
  Axiom DEAD : ExprData.
  Axiom DEAD1 : ExprData.
  Axiom DEAD2 : ExprData.
  Axiom DEAD3 : ExprData.
  Axiom DEAD4 : ExprData.

  Definition the_update_function (up : positive) (i : expr -> expr) (mu : pset -> pset)
             (mb mem : bool) : option ExprData -> ExprData :=
    match mb , mem with
      | false , false => fun x => match x with
                                    | None => DEAD1
                                    | Some x => x
                                  end
      | true , false => fun x =>
        match x with
          | None =>
            DEAD3 (** dead code **)
          | Some (UnMapped mb) =>
            DEAD4 (** dead code **)
          | Some (Mapped e m) =>
            Mapped (i e) (mu m)
        end
      | false , true => fun x =>
        match x with
          | None =>
            UnMapped (add up tt (empty _))
          | Some (UnMapped mb) =>
            UnMapped (add up tt mb)
          | Some (Mapped e m) =>
            DEAD2 (** dead code **)
        end
      | true , true => fun _ => DEAD
    end.
*)
  Definition set_helper_mentionedBy' (u : uvar) (up : positive) (e : expr) (mb : pset)
             (fs : fast_subst) : option fast_subst :=
    let (mentions, e_inst) :=
        @get_mentions_instantiate (fs_lookup fs) e
    in
    if find up mentions then None
    else
      let new :=
          update_both'
            (the_update_function' up
                                 (instantiate (fun x => if x ?[ eq ] u then
                                                          Some e_inst
                                                        else None))
                                 (fun m => remove up (pset_union mentions m)))
            mb mentions fs
      in
      Some (add up (Mapped e_inst mentions) new).

  Definition fast_subst_set (u : uvar) (e : expr) (s : fast_subst)
  : option fast_subst :=
    let up := to_key u in
    match find up s with
      | Some (Mapped _ _) => None
      | Some (UnMapped mb) => set_helper_mentionedBy' u up e mb s
      | None => set_helper_mentionedBy' u up e (empty _) s
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
          | Some (UnMapped _) => None
          | Some (Mapped _ _) =>
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
                                       | Mapped _ _ => Some (from_key (fst x))
                                       | _ => None
                                     end) (elements x)
  }.

  Definition WellTyped_fast_subst (tus tvs : EnvI.tenv typ) (s : fast_subst) : Prop :=
    forall u e, lookup u s = Some e ->
                match List.nth_error tus u with
                  | None => False
                  | Some t => Safe_expr tus tvs e t
                end.

  Definition substD_fast_subst (us vs : EnvI.env typD) (s : fast_subst)
  : Prop :=
    Forall (fun P => P)
           (fold (fun p e acc =>
                    match e with
                      | Mapped e _ =>
                        match List.nth_error us (from_key p) with
                          | None => False :: acc
                          | Some (existT ty val) =>
                            match exprD us vs e ty with
                              | Some val' => (val' = val) :: acc
                              | None => False :: acc
                            end
                        end
                      | UnMapped _ => acc
                    end) s nil).

  Definition substD_fast_subst' (us vs : EnvI.env typD) (s : fast_subst) : Prop :=
    Forall (fun p_e =>
           let '(p,e) := p_e in
           match e with
             | Mapped e _ =>
               match List.nth_error us (from_key p) with
                 | None => False
                 | Some (existT ty val) =>
                   match exprD us vs e ty with
                     | Some val' => (val' = val)
                     | None => False
                   end
               end
             | UnMapped _ => True
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
      substD_fast_subst us vs s <->
      substD_fast_subst' us vs s.
  Proof.
    unfold substD_fast_subst, substD_fast_subst'; intros.
    rewrite fold_1.
    assert (forall l,
                      (Forall (fun x : Prop => x)
                              (fold_left
                                 (fun (a : list Prop) (p : key * ExprData) =>
                                    match snd p with
                                      | Mapped e _ =>
                                        match nth_error us (from_key (fst p)) with
                                          | Some (existT ty val) =>
                                            match exprD us vs e ty with
                                              | Some val' => (val' = val) :: a
                                              | None => False :: a
                                            end
                                          | None => False :: a
                                        end
                                      | UnMapped _ => a
                                    end) (elements s) l)
                      <->
                      Forall (fun x : Prop => x)
                             (l ++ List.map
                                (fun p_e : positive * ExprData =>
                                   match p_e with
                                     | (p, Mapped e0 _) =>
                                       match nth_error us (from_key p) with
                                         | Some (existT ty val) =>
                                             match exprD us vs e0 ty with
                                               | Some val' => val' = val
                                               | None => False
                                             end
                                         | None => False
                                       end
                                     | (p, UnMapped _) => True
                                   end) (elements s)))
           ).
    { induction (elements s).
      { simpl. intros. rewrite app_nil_r. intuition. }
      { intros. destruct a. destruct e.
        { simpl in *.
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
      simpl in *.
      rewrite H. rewrite Forall_map. reflexivity. }
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


  Lemma substD_lookup_fast_subst
  : forall (u v : EnvI.env typD) (s : fast_subst) (uv : nat) (e : expr),
      WellFormed_fast_subst s ->
      lookup uv s = Some e ->
      substD_fast_subst u v s ->
      exists val : sigT (typD nil),
        List.nth_error u uv = Some val /\
        exprD u v e (projT1 val) = Some (projT2 val).
  Proof.
    simpl. intros. clear H.
    unfold fast_subst_lookup in *; simpl in *.
    forward. inv_all; subst.
    rewrite substD_fast_subst_substD_fast_subst' in H1.
    unfold substD_fast_subst' in H1.
    generalize (elements_correct s (to_key uv) H0).
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
      cutrewrite ((fst x, snd x) = x); [ | (destruct x; reflexivity) ].
      intros. apply H2 in H3. rewrite H3 in H1. rewrite H0 in *.
      destruct p; congruence. }
    { generalize (elements_correct s (to_key n)).
      forward. subst.
      specialize (H3 _ eq_refl).
      eexists. split; eauto. simpl.
      rewrite to_key_from_key. auto. }
  Qed.

  Lemma substD_welltyped
  : forall (u v : EnvI.env typD) (s : fast_subst),
      WellFormed_fast_subst s ->
      substD_fast_subst u v s ->
      WellTyped_fast_subst (EnvI.typeof_env u) (EnvI.typeof_env v) s.
  Proof.
    intros.
    red. intros.
    eapply substD_lookup_fast_subst in H0; eauto.
    destruct H0 as [ ? [ ? ? ] ].
    unfold EnvI.typeof_env.
    rewrite ListNth.nth_error_map. rewrite H0.
    eapply Safe_expr_exprD; eauto.
    unfold exprD in H2. forward.
    do 2 rewrite <- EnvI.split_env_projT1.
    Cases.rewrite_all_goal. simpl. eauto.
  Qed.

  Instance SubstOk_fast_subst : SubstOk _ Subst_fast_subst :=
  { WellFormed_subst := WellFormed_fast_subst
  ; WellTyped_subst := WellTyped_fast_subst
  ; substD := substD_fast_subst
  ; substD_WellTyped := substD_welltyped
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
      (forall u, mentionsU e' u -> mem (to_key u) s = true).

  Definition self_instantiated (f : uvar -> option expr) : Prop :=
    forall x e, f x = Some e ->
                forall y,
                  f y <> None -> ~mentionsU e y.

  Hypothesis mentionsU_instantiate_complete
  : forall f, self_instantiated f ->
              forall u e,
                mentionsU (instantiate f e) u ->
                (f u = None /\ mentionsU e u) \/
                (exists e', f u = Some e' /\ mentionsU e' u).

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

  Lemma to_key_injective : forall a b, to_key a = to_key b -> a = b.
  Proof.
    clear. unfold to_key.
    intros.
    apply Pnat.Nat2Pos.inj in H; auto.
  Qed.

  Instance Injective_to_key a b : Injective (to_key a = to_key b) :=
  { result := a = b
  }.
  Proof.
    apply to_key_injective.
  Defined.

(*
  Lemma set_helper_mentionedBy'_ok
  : forall (s s' : fast_subst) (e : expr) (uv : nat),
      WellFormed_fast_subst s ->
      lookup uv s = None ->
      forall mb : pset,
        mentionedBy (to_key uv) mb s ->
        set_helper_mentionedBy' uv (to_key uv) e mb s = Some s' ->
        WellFormed_fast_subst s' /\
        (forall (tus tvs : EnvI.tenv typ) (t0 : typ),
           WellTyped_fast_subst tus tvs s ->
           Safe_expr tus tvs e t0 ->
           nth_error tus uv = Some t0 ->
           WellTyped_fast_subst tus tvs s' /\
           (forall us vs : EnvI.env typD,
              substD_fast_subst us vs s' ->
              substD_fast_subst us vs s /\
              (forall tv : sigT (typD nil),
                 nth_error us uv = Some tv ->
                 exprD us vs e (projT1 tv) = Some (projT2 tv)))).
  Proof.
    unfold set_helper_mentionedBy'. intros.
    forward. inv_all; subst. split.
    { admit. (** this is the hard one? **) }
    { intros. split.
      { (** WellTyped **)
        unfold WellTyped_fast_subst in *. intros.
        unfold lookup in *. simpl in *.
        unfold fast_subst_lookup in *.
        rewrite Facts.add_o in H7.
        consider (E.eq_dec (to_key uv) (to_key u)).
        { intros. inv_all. subst.
          rewrite H6. admit. }
        { rewrite update_both_spec; eauto.
          forward. inv_all; subst.
          specialize (H4 u). admit. (*
          consider (find (to_key u) s).
          { intros.
            inv_all; subst. destruct e2.
            { destruct p0. specialize (H6 _ eq_refl).
              forward.
              unfold the_update_function in *. *) } }
      { (** substD **)
        intros. split.
        { eapply substD_fast_subst_substD_fast_subst'.
          eapply substD_fast_subst_substD_fast_subst' in H7.
          unfold substD_fast_subst' in *.
          repeat rewrite Forall_map in *.
          Lemma Forall_elements
          : forall T (P : positive * T -> Prop) m,
              Forall P (elements m) <->
              (forall k,
                 match find k m with
                   | None => True
                   | Some v => P (k,v)
                 end).
          Proof.
            clear. intros. rewrite Forall_forall.
            split; intros.
            { forward. eapply H.
              eapply elements_correct. auto. }
            { destruct x. specialize (H p).
              apply elements_complete in H0.
              rewrite H0 in *. assumption. }
          Qed.
          rewrite Forall_elements in H7.
          apply Forall_elements.
          intro k. specialize (H7 k).
          rewrite Facts.add_o in H7.
          forward. subst.
          consider (E.eq_dec (to_key uv) k); intros.
          { forward. subst.
            rewrite to_key_from_key in H8.
            clear - H10 H0.
            unfold lookup in *. simpl in *. unfold fast_subst_lookup in H0.
            rewrite H10 in H0. congruence. }
          { rewrite update_both_spec in H7; eauto.
            { rewrite H10 in *. simpl in *.
              admit. } } }
        { admit. } } }
  Qed.

  Lemma All_set_fast_subst
  : forall (uv : nat) (e : expr) (s s' : fast_subst),
      @WellFormed_subst _ _ _ _ _ _ SubstOk_fast_subst s ->
      lookup uv s = None ->
      set uv e s = Some s' ->
      WellFormed_subst s' /\
      forall tus tvs t,
        WellTyped_subst tus tvs s ->
        Safe_expr tus tvs e t ->
        nth_error tus uv = Some t ->
        WellTyped_subst tus tvs s' /\
        forall us vs,
          substD us vs s' ->
          substD us vs s /\
          (forall tv : sigT (typD nil),
             nth_error us uv = Some tv -> exprD us vs e (projT1 tv) = Some (projT2 tv)).
  Proof.
    simpl. unfold fast_subst_set; simpl; intros.
    forward. inv_all.
    match goal with
      | |- ?G =>
        assert (forall mb, mentionedBy (to_key uv) mb s ->
                           set_helper_mentionedBy' uv (to_key uv) e mb s = Some s' ->
                           G)
    end.
    { eapply set_helper_mentionedBy'_ok; eauto. }
    { red in H. specialize (H (to_key uv)).
      destruct (find (to_key uv) s); eauto.
      { destruct e0; try congruence; eauto. } }
  Qed.
*)

(*
  Lemma All_set_fast_subst
  : forall (uv : nat) (e : expr) (s s' : fast_subst),
      set uv e s = Some s' ->
      @WellFormed_subst _ _ _ _ _ _ SubstOk_fast_subst s ->
      lookup uv s = None ->
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
                           set_helper_mentionedBy' uv (to_key uv) e mb s = Some s' ->
                           G)
    end.
    { eapply set_helper_mentionedBy'_ok; eauto. }
    { red in H. specialize (H (to_key uv)).
      destruct (find (to_key uv) s); eauto.
      { destruct e0; try congruence; eauto. } }
  Qed.
*)

  Lemma set'_combined
  : forall uv e s s',
      WellFormed_fast_subst s ->
      forall mb : pset,
        mentionedBy (to_key uv) mb s ->
        set_helper_mentionedBy' uv (to_key uv) e mb s = Some s' ->
        WellFormed_fast_subst s' /\
        (forall (u v : EnvI.tenv typ) (t0 : typ),
           WellTyped_fast_subst u v s ->
           nth_error u uv = Some t0 ->
           Safe_expr u v e t0 -> WellTyped_fast_subst u v s') /\
        (forall (u v : EnvI.env typD) (tv : sigT (typD nil)),
           WellTyped_fast_subst (EnvI.typeof_env u) (EnvI.typeof_env v) s ->
           substD_fast_subst u v s' ->
           nth_error u uv = Some tv ->
           fast_subst_lookup uv s = None ->
           substD_fast_subst u v s /\
           exprD u v e (projT1 tv) = Some (projT2 tv)).
  Proof.
(*
    intros.
    unfold set_helper_mentionedBy' in *.
    split.
    { forward. inv_all; subst.
      unfold WellFormed_fast_subst; simpl; intros.
      rewrite Facts.add_o.
      consider (E.eq_dec (to_key uv) p0).
      { eapply get_mentions_instantiateOk in H1.
        destruct H1. subst.
        split.
        { red; intros.
          eapply H3 in H1.
          rewrite mem_find in *.
          forward. destruct u0; auto. }
        { red. intros.
          rewrite Facts.add_o.
          consider (E.eq_dec (to_key uv) p'); intros; forward.
          { rewrite to_key_from_key.
            intro. eapply H3 in H1.
            clear - H2 H1. rewrite mem_find in H1. forward. }
          { rewrite to_key_from_key. subst. intro.
            admit. } } }
      {
        Print the_update_function'.
        Lemma update_both_the_update_function_find
        : forall s mb p f g kuv z,
            find z (update_both' (the_update_function' kuv f g) mb p s) =
            match find z s with
              | None    => if mem z mb then Some (UnMapped (add kuv tt (empty unit))) else None
              | Some (Mapped e m) =>
                Some (Mapped (f e) (g m))
              | Some (UnMapped m) =>
                if mem z mb then
                  Some (UnMapped (add kuv tt mb))
                else
                  Some (UnMapped m)
            end.
        Proof.
        Admitted.
        rewrite update_both_the_update_function_find.
        specialize (H p0).
        consider (find p0 s); intros; forward.
        { destruct e1.
          { split.
            { unfold mentionsOnly.
              intros.
              eapply mentionsU_instantiate_complete in H4.
              2: admit.
              destruct H4.
              { forward.
                eapply get_mentions_instantiateOk in H1. destruct H1.
                subst. admit. }
              { exfalso. admit. }

          }

            rewrite update_both_spec' in H4 by reflexivity.
            
            consider (find p' s); intros.
            { inv_all; subst.
              generalize dependent p'.
              unfold the_update_function in H5.
              consider (mem p' mb); intros.
              { consider (mem p' p); intros.
                { clear H7.
                  generalize dependent mb. generalize dependent p.
                  Print mentionedBy.
                
              
            
  Qed.
*)
  Admitted.

  Lemma set_combined
  : forall (uv : nat) (e : expr) (s s' : fast_subst),
      set uv e s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      (forall u v t0,
         WellTyped_subst u v s ->
         nth_error u uv = Some t0 ->
         Safe_expr u v e t0 -> WellTyped_subst u v s') /\
      (forall (u v : EnvI.env typD) (tv : sigT (typD nil)),
         WellTyped_subst (EnvI.typeof_env u) (EnvI.typeof_env v) s ->
         substD u v s' ->
         nth_error u uv = Some tv ->
         lookup uv s = None ->
         substD u v s /\
         exprD u v e (projT1 tv) = Some (projT2 tv)).
  Proof.
(*
    simpl. unfold fast_subst_set; simpl; intros.
    match goal with
      | |- ?G =>
        assert (forall mb, mentionedBy (to_key uv) mb s ->
                           set_helper_mentionedBy' uv (to_key uv) e mb s = Some s' ->
                           G)
    end.
    { revert H0. 
      

    { consider (find (to_key uv) s); intros; forward.
      { subst.
        specialize (H1 p).
        red in H0. specialize (H0 (to_key uv)). rewrite H2 in *.
        forward_reason. intuition. }
      { specialize (H1 (empty unit)).
        specialize (H0 (to_key uv)).
        rewrite H in *.
        forward_reason. intuition. } }
  Qed.
*)
  Admitted.

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
      specialize (@set_combined _ _ _ _ H0); intuition. }
    { intros.
      specialize (@set_combined _ _ _ _ H3); intuition.
      eapply H5; eauto. }
    { intros. admit. (*
      destruct (@set_combined _ _ _ _ H4 H) as [ ? [ ? ? ] ].
      specialize (H7 u v tv).
      forward_reason. intuition. *) }
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
