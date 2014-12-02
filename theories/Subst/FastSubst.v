Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.
Require Coq.FSets.FMapFacts.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.VariablesI.
Require Import MirrorCore.Util.Iteration.

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


Section parametric.

  Let uvar := nat.
  Variables typ expr : Type.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : @Expr _ _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

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

(*
  Variable mentionsU : expr -> uvar -> Prop.
  Variable instantiate : (uvar -> option expr) -> expr -> expr.
*)
  Variable get_mentions_instantiate : (uvar -> option expr) -> expr -> pset * expr.

  Inductive ExprData : Type :=
  | Mapped (e : expr) (p : pset) (** [e] mentions only things in [p] **)
  | UnMapped (p : pset) (** only elements in [p] mention this index **).

  Definition fast_subst : Type :=
    pmap ExprData.

  Definition to_key : nat -> positive := fun x => Pos.of_nat (S x).
  Definition from_key : positive -> nat := fun x => pred (Pos.to_nat x).

  Definition mentionsOnly (e : expr) (s : pset) : Prop :=
    forall u,
      mentionsU u e = true ->
      find (to_key u) s = Some tt.

  Definition mentionedBy (k : positive) (ps : pset) (fs : fast_subst) : Prop :=
    forall k' e m,
      find k' fs = Some (Mapped e m) ->
      mentionsU (from_key k) e = true ->
      find k' ps = Some tt.

  Definition mentionsNone u (fs : fast_subst) : Prop :=
    forall p' : positive,
      match find p' fs with
        | Some (Mapped e _) => mentionsU u e = false
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
                                          else None) 0)
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
          (mm = false /\ mb = false) \/
          (mb = true /\ mm = false /\ i e = e' /\ mu d = d')
        | _ => False
      end.
  Proof.
    clear. unfold the_update_function'; intros.
    destruct mb; destruct mm; destruct o; forward; try congruence.
  Qed.

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
                                                        else None) 0)
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

  Instance Subst_fast_subst : Subst fast_subst expr :=
  { subst_lookup := fast_subst_lookup
  ; subst_domain :=
      fun x => filter_map (fun x =>
                             match snd x with
                               | Mapped _ _ => Some (from_key (fst x))
                               | _ => None
                             end) (elements x)
  }.

  Definition substD_fast_subst_list (tus tvs : EnvI.tenv typ) (s : fast_subst)
  : option (list (exprT tus tvs Prop)) :=
    fold (fun p e acc =>
            match e with
              | UnMapped _ => acc
              | Mapped e _ =>
                match acc with
                  | None => None
                  | Some acc =>
                    match nth_error_get_hlist_nth _ tus (from_key p) with
                      | None => None
                      | Some (existT ty get) =>
                        match exprD' tus tvs e ty with
                          | Some val' =>
                            Some ((fun us vs => get us = val' us vs) :: acc)
                          | None => None
                        end
                    end
                end
            end) s (Some nil).

  Definition substD_fast_subst (tus tvs : EnvI.tenv typ) (s : fast_subst)
  : option (exprT tus tvs Prop) :=
    match substD_fast_subst_list tus tvs s with
      | None => None
      | Some ls => Some (fun us vs => Forall (fun P => P us vs) ls)
    end.

  Require Import ExtLib.Structures.Traversable.
  Require Import ExtLib.Data.Option.
  Require Import ExtLib.Data.List.


  Definition substD_fast_subst' (tus tvs : EnvI.tenv typ) (s : fast_subst)
  : option (exprT tus tvs Prop) :=
    match
      mapT (F := option) (T := list) (fun t => match snd t with
                                                 | None => None
                                                 | Some t => Some t
                                               end)
           (elements (mapi (fun p e =>
                              match e with
                                | UnMapped _ => Some (fun _ _ => True)
                                | Mapped e _ =>
                                  match nth_error_get_hlist_nth _ tus (from_key p) with
                                    | None => None
                                    | Some (existT ty get) =>
                                      match exprD' tus tvs e ty with
                                        | Some val' =>
                                          Some (fun us vs => get us = val' us vs)
                                        | None => None
                                      end
                                  end
                              end) s))
    with
      | None => None
      | Some ls => Some (fun us vs => Forall (fun P => P us vs) ls)
    end.

  Lemma xelements_xmapi
  : forall T U (f : positive -> T -> U) x p,
      xelements (xmapi f x p) p =
      map (fun kv => (fst kv,
                      f (fst kv) (snd kv))) (xelements x p).
  Proof.
    induction x; simpl; intros.
    { reflexivity. }
    { destruct o; simpl; rewrite IHx1; rewrite IHx2.
      { rewrite map_app. reflexivity. }
      { rewrite map_app. reflexivity. } }
  Qed.

  Lemma elements_mapi
  : forall T U (f : positive -> T -> U) x,
      elements (mapi f x) =
      map (fun kv => (fst kv,
                      f (fst kv) (snd kv))) (elements x).
  Proof.
    unfold elements, mapi. intros. apply xelements_xmapi.
  Qed.

  Theorem substD_fast_subst_substD_fast_subst'
  : forall tus tvs s,
      match substD_fast_subst tus tvs s , substD_fast_subst' tus tvs s with
        | Some P , Some Q => forall us vs, P us vs <-> Q us vs
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    intros.
    unfold substD_fast_subst, substD_fast_subst_list, substD_fast_subst'.
    rewrite elements_mapi.
(*
    rewrite mapT_map.
    rewrite fold_1.
    simpl.
    induction (elements s).
    { simpl. intuition. }
    { admit. (** TODO: this is not true, due to a weak inductive hyp **) }
*)
  Admitted.

(*
  Lemma substD_fast_subst_sem
  : forall tus tvs s sD,
      substD_fast_subst tus tvs s = Some sD <->
      (forall u e,
         lookup_fast_subst u s = Some e ->
         exists t val,
           nth_error tus u = Some t /\
           exprD' tus tvs e t = Some val /\
           forall us vs,
*)

  Theorem substD_weaken
  : forall (tus tvs : tenv typ) (tus' tvs' : list typ)
           (s : fast_subst)
           (sD : exprT tus tvs Prop),
      substD_fast_subst tus tvs s = Some sD ->
      exists
        sD' : exprT (tus ++ tus') (tvs ++ tvs') Prop,
        substD_fast_subst (tus ++ tus') (tvs ++ tvs') s = Some sD' /\
        (forall (us : HList.hlist typD tus)
                (us' : HList.hlist typD tus') (vs : HList.hlist typD tvs)
                (vs' : HList.hlist typD tvs'),
           sD us vs <-> sD' (HList.hlist_app us us') (HList.hlist_app vs vs')).
  Proof.
    admit.
  Qed.

  Lemma WellFormed_domain_fast_subst
  : forall (s : fast_subst) (ls : list nat),
      WellFormed_fast_subst s ->
      subst_domain s = ls ->
      forall n : nat, List.In n ls <-> subst_lookup n s <> None.
  Proof.
    intros; subst.
    unfold subst_domain, fast_subst_lookup. simpl.
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

  Lemma mapT_In_bwd
  : forall T U (f : T -> option U) (l : list T) (l' : list U) x',
      mapT f l = Some l' ->
      In x' l' ->
      exists x,
        f x = Some x' /\ In x l.
  Proof.
    clear. induction l; simpl; intros.
    { inv_all. subst. inversion H0. }
    { forward. inv_all; subst.
      destruct H0; subst.
      { eexists; split; eauto. }
      { eapply IHl in H1; eauto.
        forward_reason. eauto. } }
  Qed.
  Lemma mapT_In_fwd
  : forall T U (f : T -> option U) (l : list T) (l' : list U) x,
      mapT f l = Some l' ->
      In x l ->
      match f x with
        | None => False
        | Some x' => In x' l'
      end.
  Proof.
    clear. induction l; simpl; intros.
    { inversion H0. }
    { forward. inv_all; subst.
      destruct H0; subst.
      { rewrite H. left. reflexivity. }
      { eapply IHl in H1; eauto.
        forward. right; assumption. } }
  Qed.

  Theorem substD_lookup_fast_subst
  : forall (s : fast_subst) (uv : nat) (e : expr),
   WellFormed_fast_subst s ->
   subst_lookup uv s = Some e ->
   forall (tus tvs : tenv typ)
     (sD : HList.hlist typD tus -> HList.hlist typD tvs -> Prop),
   substD_fast_subst tus tvs s = Some sD ->
   exists
     (t0 : typ) (val : exprT tus tvs (typD t0))
   (pf : Some t0 = nth_error tus uv),
     exprD' tus tvs e t0 = Some val /\
     (forall (us : HList.hlist typD tus)
        (vs : HList.hlist typD tvs),
      sD us vs ->
      HList.hlist_nth us uv =
      match
        pf in (_ = t1)
        return match t1 with
               | Some x => typD x
               | None => unit
               end
      with
      | eq_refl => val us vs
      end).
  Proof.
    intros.
    generalize (substD_fast_subst_substD_fast_subst' tus tvs s).
    rewrite H1. forward. clear H1.
    simpl in *. unfold fast_subst_lookup in H0.
    forward. inv_all; subst.
    unfold substD_fast_subst' in H2.
    forward. inv_all; subst.
    rewrite elements_mapi in *.
    rewrite ListMapT.mapT_map in *. Opaque mapT. simpl in *. Transparent mapT.
    eapply elements_correct in H1.
    eapply mapT_In_fwd in H0; eauto.
    simpl in *.
    forward. inv_all; subst. subst.
    eapply nth_error_get_hlist_nth_Some in H5.
    destruct H5. simpl in *.
    exists x. eexists.
    exists (eq_sym match to_key_from_key uv in _ = t
                         return nth_error tus t = Some x
                   with
                     | eq_refl => x0
                   end).
    split; eauto. intros.
    eapply H3 in H4.
    eapply Forall_forall in H4; eauto.
    simpl in *. rewrite <- H4. rewrite H0.
    clear.
    destruct x0; simpl.
    destruct (to_key_from_key uv). reflexivity.
  Qed.

  Instance SubstOk_fast_subst : SubstOk Subst_fast_subst :=
  { WellFormed_subst := WellFormed_fast_subst
  ; substD := substD_fast_subst
  ; substD_weaken := substD_weaken
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

  Fixpoint fast_subst_pull'' (cur : positive) (rest : nat) (fs : fast_subst) {struct rest}
  : option fast_subst :=
    match rest with
      | 0 => Some fs
      | S n =>
        match PositiveMap.find cur fs with
          | None
          | Some (UnMapped _) => None
          | Some (Mapped _ _) =>
            fast_subst_pull' (Pos.pred cur) rest (PositiveMap.remove cur fs)
        end
    end.

  Theorem fast_subst_pull'_app
  : forall len len' base fs,
      match fast_subst_pull' base len fs with
        | None => None
        | Some fs =>
          fast_subst_pull' (match len with
                              | 0 => base
                              | S n => base + Pos.of_nat len
                            end) len' fs
      end =
      fast_subst_pull' base (len + len') fs.
  Proof.
    clear. induction len.
    { simpl. auto. }
    { simpl.
      intros. forward. subst.
      rewrite <- IHlen. forward.
      f_equal. destruct len.
      { simpl. apply Pos.add_1_r. }
      { rewrite Pos.add_succ_r.
        rewrite Pos.add_succ_l. reflexivity. } }
  Qed.

  Definition plus_nat (p : positive) (n : nat) : positive :=
    match n with
      | 0 => p
      | S _ => (p + (Pos.of_nat n))%positive
    end.

  Lemma plus_nat_S
  : forall p n, plus_nat p (S n) = Pos.succ (plus_nat p n).
  Proof.
    clear. destruct n; simpl; intros.
    { apply Pos.add_1_r. }
    { rewrite Pos.add_succ_r. reflexivity. }
  Qed.

  Lemma plus_nat_succ
  : forall p n, plus_nat (Pos.succ p) n = Pos.succ (plus_nat p n).
  Proof.
    clear. intros.
    unfold plus_nat.
    rewrite Pos.add_succ_l.
    destruct n; reflexivity.
  Qed.

  Lemma fast_subst_pull'_sem
  : forall len base fs fs',
      fast_subst_pull' base len fs = Some fs' ->
      (forall n,
         n < len ->
         (exists e, lookup (from_key (plus_nat base n)) fs = Some e)) /\
      (forall n,
         (n < base)%positive ->
         lookup (from_key n) fs' = lookup (from_key n) fs).
  Proof.
    clear.
    induction len; intros; simpl.
    { split.
      { inversion 1. }
      { intros. simpl in *. inv_all; subst. reflexivity. } }
    { simpl in *. forward. subst. unfold fast_subst_lookup in *.
      split; intros.
      { rewrite from_key_to_key.
        destruct n.
        { simpl in *. rewrite H0. eauto. }
        { eapply IHlen in H1. destruct H1.
          assert (n < len) by omega.
          eapply H1 in H3.
          rewrite from_key_to_key in H3.
          rewrite plus_nat_S. rewrite plus_nat_succ in *.
          rewrite Facts.remove_neq_o in H3. auto.
          clear.
          Lemma plus_nat_geq : forall p n, (plus_nat p n >= p)%positive.
          Proof.
            clear.
            destruct n; simpl.
            Global Instance Refl_Pos_geq : Reflexive Pos.ge.
            Proof.
              clear. red. induction x; simpl; auto.
              compute. inversion 1.
            Qed.
            reflexivity.
            eapply Pnat.Pos2Nat.inj_ge.
            rewrite Pnat.Pos2Nat.inj_add. omega.
          Qed.
          generalize (plus_nat_geq base n).
          Lemma pos_succ_gt : forall p, (p < Pos.succ p)%positive.
          Proof.
            clear. intros.
            eapply Pnat.Pos2Nat.inj_lt.
            rewrite Pnat.Pos2Nat.inj_succ.
            omega.
          Qed.
          intros.
          intro. rewrite H0 in H at 2.
          clear H0.
          eapply Pnat.Pos2Nat.inj_ge in H.
          rewrite Pnat.Pos2Nat.inj_succ in *. omega. } }
      { eapply IHlen in H1. destruct H1.
        assert ((n < Pos.succ base)%positive).
        { etransitivity. eassumption. eapply pos_succ_gt. }
        specialize (H2 n H3).
        rewrite from_key_to_key in *.
        rewrite Facts.remove_neq_o in H2. auto.
        clear - H.
        intro. subst. eapply Pnat.Pos2Nat.inj_lt in H. omega. } }
  Qed.

  Lemma fast_subst_pull'_sem'
  : forall len base fs fs',
      fast_subst_pull' base len fs = Some fs' ->
      (forall n,
         n < len ->
         (exists e,
            PositiveMap.find (plus_nat base n) fs = Some e /\
            PositiveMap.find (plus_nat base n) fs' = None)) /\
      (forall n,
         (n < base)%positive ->
         PositiveMap.find n fs' = PositiveMap.find n fs).
  Proof.
    clear.
    induction len; intros; simpl.
    { split.
      { inversion 1. }
      { intros. simpl in *. inv_all; subst. reflexivity. } }
    { simpl in *. forward. subst. unfold fast_subst_lookup in *.
      eapply IHlen in H1; clear IHlen. destruct H1.
      split; intros.
      { destruct n.
        { simpl in *. rewrite H0.
          eexists; split; eauto.
          specialize (H1 base).
          rewrite H1. rewrite Facts.remove_eq_o; auto.
          eapply pos_succ_gt. }
        { assert (n < len) by omega.
          apply H in H3.
          rewrite plus_nat_S. rewrite plus_nat_succ in *.
          rewrite Facts.remove_neq_o in H3. auto.
          clear.
          intro.
          generalize (plus_nat_geq base n).
          intro. eapply Pnat.Pos2Nat.inj_ge in H0.
          rewrite H in H0 at 2.
          repeat rewrite Pnat.Pos2Nat.inj_succ in *. omega. } }
      { assert ((n < Pos.succ base)%positive).
        { eapply Pnat.Pos2Nat.inj_lt in H2.
          eapply Pnat.Pos2Nat.inj_lt.
          rewrite Pnat.Pos2Nat.inj_succ. omega. }
        specialize (H1 n H3).
        rewrite Facts.remove_neq_o in H1. auto.
        clear - H2.
        eapply Pnat.Pos2Nat.inj_lt in H2.
        intro. subst. omega. } }
  Qed.

  Lemma substD_pull_fast_subst
  : forall (s s' : fast_subst) (u n : nat),
      pull u n s = Some s' ->
      WellFormed_subst s ->
      WellFormed_subst s' /\
      (forall (tus tus' : list typ) (tvs : tenv typ)
              (sD : HList.hlist typD (tus ++ tus') ->
                    HList.hlist typD tvs -> Prop),
         u = length tus ->
         n = length tus' ->
         substD (tus ++ tus') tvs s = Some sD ->
         exists
           sD' : HList.hlist typD tus -> HList.hlist typD tvs -> Prop,
           substD tus tvs s' = Some sD' /\
           (exists (eus' : list expr)
                   (us' : HList.hlist
                            (fun t : typ =>
                               HList.hlist typD tus ->
                               HList.hlist typD tvs -> typD nil t)
                            tus'),
               hlist_build
                 (fun t0 : typ =>
                    HList.hlist typD tus ->
                    HList.hlist typD tvs -> typD nil t0)
                 (fun (t0 : typ) (e : expr) => exprD' tus tvs e t0) tus' eus' =
               Some us' /\
               (forall (us : HList.hlist typD tus)
                       (vs : HList.hlist typD tvs),
                  let us'0 :=
                      HList.hlist_map
                        (fun (t : typ)
                             (x : HList.hlist typD tus ->
                                  HList.hlist typD tvs -> typD nil t) =>
                           x us vs) us' in
                  sD' us vs -> sD (HList.hlist_app us us'0) vs))).
  Proof.
    clear.
    unfold pull. simpl.
    unfold fast_subst_pull.
    intros.
    eapply fast_subst_pull'_sem' in H; destruct H.
    split.
    { unfold WellFormed_fast_subst in *.
      intros. specialize (H0 p).
      admit. }
    { intros. subst.
      admit. }
  Qed.

  Instance SubstUpdateOk_fast_subst : SubstUpdateOk SubstUpdate_fast_subst _.
  Proof.
    constructor.
    { simpl. unfold WellFormed_fast_subst, fast_subst_empty.
      intros; rewrite gempty.
      red. intros.
      rewrite gempty in H. congruence. }
    { compute. eexists; split; eauto.
      simpl. constructor. }
    { admit. }
    { eapply substD_pull_fast_subst. }
  Qed.

End parametric.
