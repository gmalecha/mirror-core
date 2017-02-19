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
Defined.

Definition member_caseT
: forall {T : Type} (x y : T) xs (m : member y (x :: xs)),
    { pf : x = y & m = match pf in _ = Z return member Z _ with
                       | eq_refl => MZ _ _
                       end } +
    { m' : member y xs & m = MN x m' }.
Proof.
  clear.
  intros T x y xs m.
  refine
    match m as m in member _ (x :: xs)
          return {pf : x = y &
                       m =
                       match pf in (_ = Z) return (member Z (x :: xs)) with
                       | eq_refl => MZ x xs
                       end} + {m' : member y xs & m = MN x m'}
    with
    | MZ _ _ => inl (@existT _ _ eq_refl eq_refl)
    | MN _ _ => inr (@existT _ _ _ eq_refl)
    end.
Defined.

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
  { destruct (member_caseT m).
    { destruct s. subst. reflexivity. }
    { destruct s. subst. eapply IHvs''. } }
Defined.

(** **)
Section find_in_hlist.
  Context {T : Type} {F : T -> Type}.
  Context {t : T}.
  Variable check_dec : forall {u}, F u -> option (t = u).

  Fixpoint find_in_hlist {Z ts} (xs : hlist F ts)
  : (member t ts -> Z) -> option Z :=
    match xs in hlist _ ts
          return (member t ts -> Z) -> option Z
    with
    | Hnil => fun _ => None
    | @Hcons _ _ t' _ x' xs =>
      match check_dec x' with
      | Some pf => fun k =>
        Some (k match pf with
                | eq_refl => MZ _ _
                end)
      | _ => fun k => find_in_hlist xs (fun z => k (MN _ z))
      end
    end.

(*
  Variable P : forall ts, member t ts -> Prop.
  Hypothesis eq_dec_ok : forall u b pf,
      @check_dec u b = Some pf ->
      P match eq_sym pf in _ = X return F X with
        | eq_refl => b
        end.
*)

  Lemma find_in_hlist_ok : forall ts xs Z k e' Q,
      (forall (x : member t ts), check_dec (hlist_get x xs) = Some eq_refl -> Q (k x)) ->
      @find_in_hlist Z ts xs k = Some e' ->
      Q e'.
  Proof.
    induction xs; simpl; intros; try congruence.
    { destruct (check_dec f) eqn:?.
      { inv_all. clear IHxs.
        subst. eapply X. assumption. }
      { eapply IHxs; [ | eassumption ].
        simpl. eauto. } }
  Defined.

End find_in_hlist.

(** Backported **)

Require Import ExtLib.Structures.Applicative.

(** TODO(gmalecha): Move to ExtLib *)
Instance Applicative_id : Applicative id :=
{ pure := fun _ x => x
; ap := fun _ _ f x => f x
}.

(** TODO(gmalecha): Move to ExtLib *)
Definition Compose {T U V} (g : U -> V) (f : T -> U) : T -> V :=
  fun x => g (f x).

(** TODO(gmalecha): Move to ExtLib *)
Instance Applicative_Compose (f g : Type -> Type) (Af : Applicative f) (Ag : Applicative g)
: Applicative (Compose f g) :=
{ pure := fun (A : Type) (X : A) => pure (T:=f) (pure (T:=g) X)
; ap := fun (A B : Type) (X : f (g (A -> B))) (X0 : f (g A)) =>
          ap (T:=f) (ap (pure ap) X) X0
}.


(** TODO(gmalecha): This is generic *)
Section del_val.
  Context {T : Type}.
  Variable ku : T.

  Fixpoint del_member (ls : list T) (m : member ku ls) : list T :=
    match m with
    | MZ _ l => l
    | MN ku' m => ku' :: del_member m
    end.

  Lemma lenth_del_member : forall ls (m : member ku ls),
      length (del_member m) < length ls.
  Proof using.
    clear.
    induction m; simpl.
    { constructor. }
    { apply Lt.lt_n_S. (** BAD: opaque *)
      assumption. }
  Defined.

End del_val.


Section member_heq.
  Context {T : Type}.
  Fixpoint member_heq {l r : T} {ls} (m : member l ls)
  : member r ls -> member r (del_member m) + (l = r).
    refine
      match m as m in member _ ls
            return member r ls -> member r (del_member m) + (l = r)
      with
      | @MZ _ _ ls => fun b : member r (l :: ls) =>
                       match b in member _ (z :: ls)
                             return l = z -> member r (del_member (@MZ _ _ ls)) + (l = r)
                       with
                       | MZ _ _ => @inr _ _
                       | MN _ m' => fun pf => inl m'
                       end eq_refl
      | @MN _ _ l' ls' mx => fun b : member r (l' :: ls') =>
                              match b in member _ (z :: ls)
                                    return (member _ ls -> member _ (del_member mx) + (_ = r)) ->
                                           member r (del_member (@MN _ _ _ _ mx)) + (_ = r)
                              with
                              | MZ _ _ => fun _ => inl (MZ _ _)
                              | MN _ m' => fun f => match f m' with
                                                | inl m => inl (MN _ m)
                                                | inr pf => inr pf
                                                end
                              end (fun x => @member_heq _ _ _ mx x)
      end.
  Defined.

  Fixpoint member_heq_pf {l r : T} {ls} (m : member l ls)
  : forall m' : member r ls, member r (del_member m) + { pf : l = r | match pf with
                                                                 | eq_refl => m
                                                                 end = m' }.
  Admitted. (*
    refine
      match m as m in member _ ls
            return forall m' : member r ls,
          member r (del_member m) + { pf : l = r | match pf with
                                                   | eq_refl => m
                                                   end = m'}
      with
      | @MZ _ _ ls => fun b : member r (l :: ls) =>
        match b as b in member _ (z :: ls)
              return l = z -> member r (del_member m) + { pf : l = r | match pf with
                                                                      | eq_refl => @MZ _ _ _
                                                                      end = b }
        with
        | MZ _ _ => @inr _ _
        | MN _ m' => fun pf => inl m'
        end eq_refl
      | @MN _ _ l' ls' mx => fun b : member r (l' :: ls') =>
                              match b in member _ (z :: ls)
                                    return (member _ ls -> member _ (del_member mx) + (_ = r)) ->
                                           member r (del_member (@MN _ _ _ _ mx)) + (_ = r)
                              with
                              | MZ _ _ => fun _ => inl (MZ _ _)
                              | MN _ m' => fun f => match f m' with
                                                | inl m => inl (MN _ m)
                                                | inr pf => inr pf
                                                end
                              end (fun x => @member_heq _ _ _ mx x)
      end.
  Defined.
*)

  Lemma member_heq_refl : forall (l : T) (ls : list T) (m : member l ls),
      member_heq m m = inr eq_refl.
  Proof.
    clear.
    induction m; simpl; auto.
    rewrite IHm. reflexivity.
  Defined.

  Variable UIP_T : forall (a : T) (pf : a = a), pf = eq_refl.

  Lemma member_heq_eq : forall {l ls} (m1 m2 : member l ls),
      member_heq m1 m2 = inr eq_refl ->
      m1 = m2.
  Proof.
    induction m1; simpl.
    { intro. destruct (member_case m2) as [ [ ? ? ] | [ ? ? ] ]; subst.
      { intro XXX; clear XXX. rewrite (UIP_T x). reflexivity. }
      { inversion 1. } }
    { intro. destruct (member_case m2) as [ [ ? ? ] | [ ? ? ] ]; subst.
      { inversion 1. }
      { specialize (IHm1 x).
        destruct (member_heq m1 x).
        { inversion 1. }
        { inversion 1. f_equal. eapply IHm1.
          rewrite (UIP_T e). reflexivity. } } }
  Defined.

End member_heq.

(** TODO(gmalecha): This could have more liberal universes *)
Section hlist_traverse.
  Polymorphic Universe u.
  Polymorphic Variable m : Type@{u} -> Type@{u}.
  Polymorphic Context {Applicative_m : ExtLib.Structures.Applicative.Applicative m}.

  Polymorphic Variable T : Type.
  Polymorphic Variable F : T -> Type.
  Polymorphic Variable G : T -> Type.
  Polymorphic Variable ff : forall t : T, F t -> m (G t).

  Polymorphic Fixpoint hlist_traverse {ls} (h : hlist@{u u} F ls) : m (hlist G ls) :=
    match h in hlist _ ls return m (hlist G ls) with
    | Hnil => pure (@Hnil _ _)
    | Hcons h hs => ap (T:=m) (ap (T:=m) (pure (T:=m) (@Hcons _ _ _ _)) (ff h)) (hlist_traverse hs)
    end.
End hlist_traverse.

(** GENERIC **)
Section hlist_zipWith.
  Context {T : Type}.
  Context {F G R : T -> Type}.

  Variable f : forall t, F t -> G t -> R t.
  Fixpoint hlist_zipWith {ls : list T} (h : hlist F ls) {struct h}
    : hlist G ls -> hlist R ls :=
    match h in hlist _ ls return hlist G ls -> hlist R ls with
    | Hnil => fun _ => Hnil
    | Hcons x xs => fun ys =>
                     match ys in hlist _ (i :: is)
                           return _ -> (hlist G is -> hlist R is) -> hlist R (i :: is)
                     with
                     | Hcons y ys => fun x xs => Hcons (x y) (xs ys)
                     end (f x) (hlist_zipWith xs)
    end.
End hlist_zipWith.

Require Import ExtLib.Structures.Monad.

(** GENERIC **)
Section hlist_foldM.
  Context {m : Type -> Type}.
  Context {App_m : Monad m}.
  Context {T : Type}.
  Context {A : list T -> Type}.
  Context {F : T -> Type}.

  Variable f : forall l, F l -> forall ls, A ls -> m (A (l :: ls)).

  Fixpoint hlist_foldM {ls} (xs : hlist F ls) (a : A nil) {struct xs} : m (A ls).
    refine
      match xs in hlist _ ls return m (A ls) with
      | Hnil => ret (m:=m) a
      | Hcons x xs => bind (m:=m) (hlist_foldM _ xs a) (@f _ x _)
      end.
  Defined.
End hlist_foldM.

Require Import ExtLib.Data.Monads.OptionMonad.


(** Generic definitions **)
Section ForallT_hlist.
  Polymorphic Context {T} {F : T -> Type} {G : forall x, F x -> Type}.
  Polymorphic Inductive ForallT_hlist : forall ts : list T, hlist F ts -> Type :=
  | ForallT_Hnil : ForallT_hlist Hnil
  | ForallT_Hcons : forall t ts h hs,
      G h ->
      ForallT_hlist hs ->
      @ForallT_hlist (t :: ts) (Hcons h hs).
End ForallT_hlist.

Section ForallT2_hlist.
  Polymorphic Context {T} {F G : T -> Type}.
  Polymorphic Variable P : forall x, F x -> G x -> Type.
  Polymorphic Inductive ForallT2_hlist : forall ts : list T, hlist F ts -> hlist G ts -> Type :=
  | ForallT2_Hnil : ForallT2_hlist Hnil Hnil
  | ForallT2_Hcons : forall t ts x xs y ys,
      P x y ->
      ForallT2_hlist xs ys ->
      @ForallT2_hlist (t :: ts) (Hcons x xs) (Hcons y ys).
End ForallT2_hlist.
Arguments ForallT2_hlist [_ _ _] _ [_] _ _.
Arguments ForallT_hlist [_ _] _ [_] _.

Section ForallT_hlist_lems.
  Polymorphic Context {T} {F G : T -> Type} (f : forall x, F x -> G x)
              (P : forall t, G t -> Type).

  Polymorphic Lemma ForallT_hlist_map
    : forall ls hs,
      ForallT_hlist (ts:=ls) (fun t x => P (f x)) hs ->
      ForallT_hlist (ts:=ls) P (hlist_map f hs).
  Proof using. clear.
               induction 1; constructor; eauto.
  Defined.

  Polymorphic Lemma ForallT_hlist_pure
    : (forall t f, @P t f) -> forall ls hs,
        ForallT_hlist (ts:=ls) P hs.
  Proof using. clear.
               induction hs; constructor; eauto.
  Defined.

  Polymorphic Definition ForallT_hlist_hd
              {l ls} {hs : hlist G (l :: ls)} (Fhs : ForallT_hlist P hs)
    : P (hlist_hd hs) :=
    match Fhs in @ForallT_hlist _ _ _ (_ :: _)  hs
          return P (hlist_hd hs)
    with
    | ForallT_Hcons _ _ pf _ => pf
    end.

  Polymorphic Definition ForallT_hlist_tl
              {l ls} {hs : hlist G (l :: ls)} (Fhs : ForallT_hlist P hs)
    : ForallT_hlist P (hlist_tl hs) :=
    match Fhs in @ForallT_hlist _ _ _ (_ :: _)  hs
          return ForallT_hlist P (hlist_tl hs)
    with
    | ForallT_Hcons _ _ _ pf => pf
    end.

  Polymorphic Lemma ForallT_hlist_ap (Q : forall t, G t -> Type)
    : forall ls hs,
      ForallT_hlist (ts:=ls) (fun t x => P x -> Q t x) hs ->
      ForallT_hlist (ts:=ls) P hs ->
      ForallT_hlist (ts:=ls) Q hs.
  Proof using. clear.
               induction 1; constructor.
               { apply g.
                 eapply (ForallT_hlist_hd X0). }
               { eapply IHX. eapply (ForallT_hlist_tl X0). }
  Defined.

  Polymorphic Lemma ForallT_hlist_get
    : forall ls (hs : hlist G ls),
      ForallT_hlist P hs ->
      forall t m, @P t (hlist_get m hs).
  Proof.
    induction m.
    { eapply ForallT_hlist_hd. assumption. }
    { eapply IHm. eapply ForallT_hlist_tl. eassumption. }
  Defined.

  Polymorphic Lemma ForallT2_hlist_map_l
    : forall E Q ls (hs : hlist _ ls) (hs' : hlist E ls),
      ForallT2_hlist (fun t x y => @Q t (@f t x) y) hs hs' ->
      ForallT2_hlist Q (hlist_map f hs) hs'.
  Proof.
    induction 1; constructor; auto.
  Defined.

  Polymorphic Lemma ForallT2_hlist_map_r
    : forall E Q ls (hs : hlist E ls) (hs' : hlist _ ls),
      ForallT2_hlist (fun t x y => @Q t x (@f t y)) hs hs' ->
      ForallT2_hlist Q hs (hlist_map f hs').
  Proof.
    induction 1; constructor; auto.
  Defined.

  Polymorphic Lemma ForallT2_hlist_same
    : forall Q ls (hs : hlist F ls),
      ForallT_hlist (fun t x => Q t x x) hs ->
      ForallT2_hlist Q hs hs.
  Proof. induction 1; constructor; auto. Defined.
End ForallT_hlist_lems.

(** TODO: This is generic *)
Fixpoint members {T} (ls : list T) : hlist (fun x => member x ls) ls :=
  match ls as ls
        return hlist (fun x => member x ls) ls
  with
  | nil => Hnil
  | l :: ls => Hcons (MZ _ _) (hlist_map (fun t m => @MN _ _ _ _ m) (@members _ ls))
  end.


Polymorphic Lemma hlist_get_members {T} {ls : list T} t (m : member t ls)
: hlist_get m (members ls) = m.
Proof.
  induction m; simpl.
  { reflexivity. }
  { rewrite hlist_get_hlist_map. f_equal. assumption. }
Defined.



Lemma hlist_traverse_hlist_map
  : forall {T} {F G H : T -> Type} (m : Type -> Type) (Am : Applicative m)
      (g : forall t, F t -> G t)
      (f : forall t, G t -> m (H t))
      {ls} (hs : hlist F ls),
    @hlist_traverse m _ T G H f ls (hlist_map g hs) =
    @hlist_traverse m _ T _ _ (fun u (t : F u) => f u (g u t)) ls hs.
Proof.
  induction hs.
  { reflexivity. }
  { simpl. f_equal. apply IHhs. }
Defined.

Lemma hlist_traverse_id_hlist_map
  : forall {T} {F G : T -> Type}
      (f : forall t, F t -> id (G t))
      {ls} (hs : hlist F ls),
    hlist_traverse _ f hs =
    hlist_map f hs.
Proof.
  reflexivity.
Defined.



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
Defined.

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
Defined.
*)