Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section hlist_Forall.
  Context {T : Type} {F G : T -> Type}.
  Variable P : forall t, F t -> Prop.
  Inductive hlist_Forall : forall ts, hlist F ts -> Prop :=
  | hlist_Forall_nil : @hlist_Forall nil Hnil
  | hlist_Forall_cons : forall t ts x xs,
      @P t x ->
      @hlist_Forall ts xs ->
      @hlist_Forall (t :: ts) (Hcons x xs).

  Variable R : forall t, F t -> G t -> Prop.
  Inductive hlist_Forall2 : forall ts, hlist F ts -> hlist G ts -> Prop :=
  | hlist_Forall2_nil : @hlist_Forall2 nil Hnil Hnil
  | hlist_Forall2_cons : forall t ts x xs y ys,
      @R t x y ->
      @hlist_Forall2 ts xs ys ->
      @hlist_Forall2 (t :: ts) (Hcons x xs) (Hcons y ys).
End hlist_Forall.
Arguments hlist_Forall_nil {_ _ _}.
Arguments hlist_Forall_cons {_ _ _ _ _ _ _} _ _.

Section Forall2.
  Context {T U : Type}.
  Variable P : T -> U -> Prop.
  Inductive Forall2 : list T -> list U -> Prop :=
  | Forall2nil : Forall2 nil nil
  | Forall2cons : forall x xs y ys, P x y -> Forall2 xs ys ->
                                    Forall2 (x :: xs) (y :: ys).
End Forall2.

Section hlist_Forall2.
  Context {T : Type} {F : T -> Type} {G : forall x, F x -> F x -> Prop}
          (P : forall x (a b : F x), G x a b -> Prop).

  Variable R : forall t (a b : F t), G a b -> Prop.
  Inductive hlist_Forall2_dep
    : forall ts (a b : hlist F ts), hlist_Forall2 G a b -> Prop :=
  | hlist_Forall2_dep_nil :
      @hlist_Forall2_dep nil Hnil Hnil (@hlist_Forall2_nil _ _ _ _)
  | hlist_Forall2_dep_cons : forall t ts x xs y ys pf pfs,
      P pf ->
      @hlist_Forall2_dep ts xs ys pfs ->
      @hlist_Forall2_dep (t :: ts) (Hcons x xs) (Hcons y ys)
                         (@hlist_Forall2_cons T F F G t ts _ _ _ _ pf pfs).

End hlist_Forall2.

(** * Auxiliary Functions **)

Section member_eq_dec.
  Context {T : Type}.
  Context {T_dec : forall a b : T, {a = b} + {a <> b}}.
  Fixpoint member_eq_dec ts (t : T) (a : member t ts)
    : forall b,  {a = b} + {a <> b}.
    refine
      match a in member _ ts
            return forall b : member t ts, {a = b} + {a <> b}
      with
      | MZ _ _ => fun b =>
                    match b as b in member _ (t' :: l)
                          return forall pf : t' = t,
                        {MZ t l = match pf with
                                  | eq_refl => b
                                  end} +
                        {MZ t l <> match pf with
                                   | eq_refl => b
                                   end}
                    with
                    | MZ _ ls => fun pf => left _
                    | MN _ _ => fun pf => right _
                    end eq_refl
      | MN _ m => fun b =>
                    match b as b in member _ (t' :: l)
                          return forall m, (forall x, {m = x} + {m <> x}) ->
                                           {MN _ m = b} + {MN _ m <> b}
                    with
                    | MZ _ _ => fun _ _ => right _
                    | MN _ m => fun _ rec => match rec m with
                                             | left pf => left _
                                             | right pf => right _
                                             end
                    end m (fun x => member_eq_dec _ _ m x)
      end.
    destruct (eq_sym (UIP_refl pf)). reflexivity.
    clear - pf. subst. intro. inversion H.
    clear. intro. inversion H.
    f_equal. assumption.
    clear - pf T_dec. intro. apply pf. inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1. assumption.
    eapply List.list_eq_dec. eassumption.
    Unshelve. eapply T_dec.
  Defined.

  Require Import Coq.Lists.List.

  Section with_t.
    Context {t : T}.
    Fixpoint member_weaken ls' {ls}
    : member t ls -> member t (ls' ++ ls) :=
      match ls' as ls'
            return member t ls -> member t (ls' ++ ls)
      with
      | nil => fun x => x
      | l :: ls' => fun x => MN _ (member_weaken ls' x)
      end.

    Fixpoint member_lift ls ls' ls''
      : member t (ls'' ++ ls) -> member t (ls'' ++ ls' ++ ls) :=
      match ls'' as ls''
            return member t (ls'' ++ ls) -> member t (ls'' ++ ls' ++ ls)
      with
      | nil => member_weaken ls'
      | l :: ls'' => fun m =>
                       match m in member _ (x :: xs)
                             return forall xs', (member t xs -> member t xs') ->
                                                member t (x :: xs')
                       with
                       | MZ _ _ => fun _ _ => MZ _ _
                       | MN _ m => fun _ rec => MN _ (rec m)
                       end _ (member_lift  ls ls' ls'')
      end.
  End with_t.
End member_eq_dec.

Section hlist_eq_dec.
  Context {T : Type} {F : T -> Type}.
  Variable F_dec : forall t (a b : F t), {a = b} + {a <> b}.
  Fixpoint hlist_eq_dec {ls} (a : hlist F ls)
    : forall b : hlist F ls, {a = b} + {a <> b}.
    refine
      match a as a in hlist _ ls
            return forall b : hlist F ls, {a = b} + {a <> b}
      with
      | Hnil => fun x => left _
      | Hcons x xs => fun b =>
                        match F_dec x (hlist_hd b)
                              , hlist_eq_dec _ xs (hlist_tl b)
                        with
                        | left pf , left pf' => left _
                        | _ , _ => right _
                        end
      end.
    { symmetry. apply (hlist_eta x). }
    { rewrite hlist_eta. congruence. }
    { clear - n. intro; subst. simpl in *. auto. }
    { clear - n. intro; subst. simpl in *. auto. }
  Defined.
End hlist_eq_dec.

(** TODO(gmalecha): Move to ExtLib **)
Definition pair_eq_dec {T U} (T_dec : forall a b : T, {a = b} + {a <> b})
           (U_dec : forall a b : U, {a = b} + {a <> b})
  : forall a b : T * U, {a = b} + {a <> b}.
  refine
    (fun a b =>
       match a as a , b as b with
       | (l,r) , (l',r') => match T_dec l l' , U_dec r r' with
                            | left pf , left pf' => left _
                            | _ , _ => right _
                            end
       end); subst; auto. congruence. congruence.
Defined.

Section hlist_map_rules.
  Variable A : Type.
  Variables F G G' : A -> Type.
  Variable ff : forall x, F x -> G x.
  Variable gg : forall x, G x -> G' x.

  Theorem hlist_map_hlist_map : forall ls (hl : hlist F ls),
      hlist_map gg (hlist_map ff hl) = hlist_map (fun _ x => gg (ff x)) hl.
  Proof.
    induction hl; simpl; f_equal. assumption.
  Defined.

  Theorem hlist_get_hlist_map : forall ls t (hl : hlist F ls) (m : member t ls),
      hlist_get m (hlist_map ff hl) = ff (hlist_get m hl).
  Proof.
    induction m; simpl.
    { rewrite (hlist_eta hl). reflexivity. }
    { rewrite (hlist_eta hl). simpl. auto. }
  Defined.

  Lemma hlist_map_ext : forall (ff gg : forall x, F x -> G x),
      (forall x t, ff x t = gg x t) ->
      forall ls (hl : hlist F ls),
        hlist_map ff hl = hlist_map gg hl.
  Proof.
    induction hl; simpl; auto.
    intros. f_equal; auto.
  Defined.

End hlist_map_rules.

Lemma hlist_get_member_weaken:
  forall {T : Type} (F : T -> Type) (tvs tvs' : list T) (t0 : T) (m : member t0 tvs) (vs : hlist F tvs) (vs' : hlist F tvs'),
    hlist_get (member_weaken tvs' m) (hlist_app vs' vs) = hlist_get m vs.
Proof.
  clear.
  induction tvs'; simpl; intros.
  { rewrite (hlist_eta vs'). reflexivity. }
  { rewrite (hlist_eta vs'). simpl. eauto. }
Qed.

Lemma hlist_get_member_lift
: forall T (F : T -> Type) (tvs tvs' tvs0 : list T) (t0 : T) (m : member t0 (tvs0 ++ tvs)) (vs : hlist F tvs)
         (vs' : hlist F tvs') (vs'' : hlist F tvs0),
    hlist_get (member_lift tvs tvs' tvs0 m) (hlist_app vs'' (hlist_app vs' vs))
    = hlist_get m (hlist_app vs'' vs).
Proof.
  clear.
  induction vs''.
  { simpl in *.
    eapply hlist_get_member_weaken. }
  { destruct (member_case m).
    { destruct H. subst. reflexivity. }
    { destruct H. subst. eapply IHvs''. } }
Qed.

(*
Lemma hlist_get_member_lift'
  : forall tus tvsX tvs tvs' tvs''
           (xs : hlist (wtexpr tus tvsX) tvs)
           (xs' : hlist (wtexpr tus tvsX) tvs')
           (xs'' : hlist (wtexpr tus tvsX) tvs'')
           t Z
           (pf : Z = (List.app tvs'' tvs))
           (m : member t Z),
    hlist_get (member_lift tvs tvs' tvs'' match pf with
                                          | eq_refl => m
                                          end) (hlist_app xs'' (hlist_app xs' xs)) =
    hlist_get match pf with
              | eq_refl => m
              end (hlist_app xs'' xs).
Proof using.
  clear.
  induction tvs''; simpl.
  { intros; subst. rewrite (hlist_eta xs''). simpl.
    clear.
    induction xs'.
    { reflexivity. }
    { simpl. eauto. } }
  { clear - IHtvs''.
    intros; subst.
    destruct (member_case m).
    { destruct H. subst. simpl. rewrite (hlist_eta xs'').
      reflexivity. }
    { destruct H. subst. simpl. rewrite (hlist_eta xs''). simpl.
      specialize (IHtvs'' xs xs' (hlist_tl xs'') t _ eq_refl).
      simpl in *. eauto. } }
Qed.

Lemma hlist_get_member_lift
  : forall tus tvsX tvs tvs' tvs''
           (xs : hlist (wtexpr tus tvsX) tvs)
           (xs' : hlist (wtexpr tus tvsX) tvs')
           (xs'' : hlist (wtexpr tus tvsX) tvs'')
           t
           (m : member t (List.app tvs'' tvs)),
    hlist_get (member_lift tvs tvs' tvs'' m) (hlist_app xs'' (hlist_app xs' xs)) =
    hlist_get m (hlist_app xs'' xs).
Proof using.
  intros. eapply hlist_get_member_lift' with (pf:=eq_refl).
Qed.
*)