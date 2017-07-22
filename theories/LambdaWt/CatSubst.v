Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.
Require Import MirrorCore.LambdaWt.WtType.
Require Import MirrorCore.LambdaWt.WtExpr.

Set Implicit Arguments.
Set Strict Implicit.

Section hlist.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_inj_impl
    : forall  t ts
         (Ts : hlist F (t :: ts)) (Us : hlist G (t :: ts)),
      hlist_Forall2 P Ts Us ->
      P (hlist_hd Ts) (hlist_hd Us) /\
      hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us).
  Proof.
    clear.
    intros.
    Print hlist_Forall2.
    refine
      match H in @hlist_Forall2 _ _ _ _ ts xs ys
            return match ts as ts return hlist F ts -> hlist G ts -> Prop with
                   | nil => fun _ _ => True
                   | t :: ts => fun Ts Us => P (hlist_hd Ts) (hlist_hd Us) /\ hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us)
                   end xs ys
      with
      | hlist_Forall2_nil _ => I
      | hlist_Forall2_cons _ _ _ _ _ => conj _ _
      end.
    assumption. assumption.
  Defined.

  Lemma hlist_Forall2_inj
    : forall  t ts
         (Ts : hlist F (t :: ts)) (Us : hlist G (t :: ts)),
      hlist_Forall2 P Ts Us <->
      P (hlist_hd Ts) (hlist_hd Us) /\
      hlist_Forall2 P (hlist_tl Ts) (hlist_tl Us).
  Proof.
    split. eapply hlist_Forall2_inj_impl.
    intro.
    rewrite (hlist_eta Ts). rewrite (hlist_eta Us).
    destruct H; constructor; auto.
  Defined.

End hlist.

Section hlist'.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_hlist_map_l
  : forall F' (f : forall t, F' t -> F t) ts (xs : hlist _ ts) ys,
      hlist_Forall2 P (hlist_map f xs) ys <->
      hlist_Forall2 (fun t x y => P (f _ x) y) xs ys.
  Proof.
    induction xs; intros.
    { rewrite (hlist_eta ys). simpl. split; constructor. }
    { rewrite hlist_Forall2_inj. rewrite IHxs.
      rewrite hlist_Forall2_inj. reflexivity. }
  Defined.

  Lemma hlist_Forall2_hlist_map_swap
  : forall ts (xs : hlist _ ts) ys,
      hlist_Forall2 P xs ys <->
      hlist_Forall2 (fun t x y => P y x) ys xs.
  Proof.
    induction xs; intros.
    { rewrite (hlist_eta ys). simpl. split; constructor. }
    { rewrite hlist_Forall2_inj. rewrite IHxs.
      rewrite hlist_Forall2_inj. reflexivity. }
  Defined.

End hlist'.

Section hlist'''.
  Variables (T : Type) (F G : T -> Type) (P : forall (t : T), F t -> G t -> Prop).

  Lemma hlist_Forall2_hlist_map_r
  : forall G' (f : forall t, G' t -> G t) ts (xs : hlist _ ts) ys,
      hlist_Forall2 P xs (hlist_map f ys) <->
      hlist_Forall2 (fun t x y => P x (f _ y)) xs ys.
  Proof.
    intros. rewrite hlist_Forall2_hlist_map_swap.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_swap.
    reflexivity.
  Defined.

End hlist'''.

Section hlist''.

  Variables (T : Type) (F : T -> Type) (P : forall (t : T), F t -> F t -> Prop).

  Lemma hlist_Forall2_hlist_Forall
  : forall ts (xs : hlist _ ts),
      hlist_Forall (fun t x => P x x) xs <->
      hlist_Forall2 P xs xs.
  Proof.
    split.
    { induction 1; constructor; auto. }
    { induction xs; intros.
      - constructor.
      - apply hlist_Forall2_inj_impl in H. destruct H; constructor; auto. }
  Defined.

End hlist''.

Lemma hlist_Forall_Hcons_inj
  : forall T (F : T -> Type) (P : forall t, F t -> Prop) l ls (h : F l) (hs : hlist F ls),
    hlist_Forall P (Hcons h hs) <-> (P _ h /\ hlist_Forall P hs).
Proof.
  split.
  { refine (fun H =>
              match H in hlist_Forall _ xs
                    return match xs return Prop with
                           | Hnil => True
                           | Hcons h hs => P _ h /\ hlist_Forall P hs
                           end
              with
              | hlist_Forall_nil => I
              | hlist_Forall_cons p q => conj p q
              end). }
  { destruct 1; constructor; assumption. }
Defined.

Lemma hlist_Forall_hlist_map
  : forall T (F G : T -> Type) (P : forall t, G t -> Prop) (f : forall t, F t -> G t) ls (hs : hlist F ls),
    hlist_Forall P (hlist_map f hs) <-> hlist_Forall (fun t x => P t (f t x)) hs.
Proof.
  split.
  { induction hs; simpl; intros.
    { constructor. }
    { eapply hlist_Forall_Hcons_inj in H.
      destruct H; constructor; auto. } }
  { induction 1; constructor; auto. }
Defined.

Lemma hlist_Forall2_members_l:
  forall (T : Type) (i : list T) (T0 : T -> Type) (m : hlist T0 i)
    (P : forall t : T, member t i -> T0 t -> Prop),
    hlist_Forall (fun (t : T) (mem : member t i) => P t mem (hlist_get mem m)) (members i) ->
    hlist_Forall2 P (members i) m.
Proof.
  clear. induction m; intros.
  - constructor.
  - simpl in *.
    apply hlist_Forall_Hcons_inj in H.
    destruct H. constructor; auto.
    apply hlist_Forall_hlist_map in H0.
    apply hlist_Forall2_hlist_map_l.
    eapply IHm.
    assumption.
Defined.

Lemma hlist_Forall_pure : forall T (F : T -> Type) (P : forall t, F t -> Prop) ls (hs : hlist F ls),
    (forall t x, P t x) ->
    hlist_Forall P hs.
Proof.
  clear.
  induction hs; constructor; eauto.
Defined.

Lemma member_app_case : forall T (ls ls' : list T) t (m : member t (ls ++ ls')),
    (exists m' : member t ls, m = match app_nil_r_trans _ in _ = X
                                   return member t (ls ++ X)
                             with
                             | eq_refl =>
                               @member_lift _ t nil _ ls match eq_sym (app_nil_r_trans ls) with
                                                         | eq_refl => m'
                                                         end
                             end)
    \/ (exists m' : member t ls', m = member_weaken _ m').
Proof.
  clear.
  induction ls; simpl.
  { right. eauto. }
  { intros.
    destruct (member_caseT m).
    { destruct s. subst. left.
      clear. generalize (app_nil_r_trans ls').
      generalize (app_nil_r_trans ls).
      destruct e. simpl.
      destruct e.
      exists (MZ _ _). reflexivity. }
    { destruct s. subst.
      specialize (IHls _ _ x).
      destruct IHls.
      { destruct H. left.
        subst. exists (MN _ x0).
        destruct (app_nil_r_trans ls'); simpl.
        generalize (app_nil_r_trans ls).
        match goal with
        | |- forall e, _ = _ _ ?X => generalize X
        end.
        generalize (ls ++ ls' ++ nil).
        generalize dependent (ls ++ nil).
        destruct e; reflexivity. }
      { right. destruct H. subst. eauto. } } }
Defined.

Lemma forall_eq_rw : forall T U (a b : T) (F : U -> T -> Type) (pf : a = b) z,
    match pf in _ = X return forall u, F u X with
    | eq_refl => z
    end = fun u => match pf in _ = X return F u X with
                | eq_refl => z u
                end.
Proof. clear. destruct pf. reflexivity. Defined.

Lemma impl_eq_rw : forall T (a b : T) (pf : a = b) (F G : T -> Type) z,
    match pf in _ = X return F X -> G X with
    | eq_refl => z
    end = fun u => match pf in _ = X return G X with
                | eq_refl => z
                              match eq_sym pf in _ = X return F X with
                              | eq_refl => u
                              end
                end.
Proof. clear. destruct pf. reflexivity. Defined.

Lemma const_eq_rw : forall T (a b : T) (pf : a = b) (F : Type) z,
    match pf in _ = X return F with
    | eq_refl => z
    end = z.
Proof. clear. destruct pf. reflexivity. Defined.

Require Import ExtLib.Data.Eq.

Ltac autorewrite_with_eq_rw :=
  repeat progress (autorewrite with eq_rw ;
                   repeat match goal with
                          | |- context [ match ?Y in @eq _ _ X return forall t, @?F t X with
                                        | eq_refl => _
                                        end ] =>
                            rewrite (@forall_eq_rw _ _ _ _ F Y)
                          | |- context [ match ?X in @eq _ _ _ return _ -> _ with
                                        | eq_refl => _
                                        end ] =>
                            rewrite (eq_Arr_eq X)
                          end).

Lemma hlist_get_cast_app_nil_r : forall T (F : T -> Type) ls ls' t (m : member t _) (hs : hlist F ls) (hs' : hlist F ls'),
    hlist_get match app_nil_r_trans ls' in _ = X return member t (ls ++ X) with
              | eq_refl => m
              end
              (hlist_app hs hs')
    = hlist_get m (hlist_app hs (hlist_app hs' Hnil)).
Proof.
  clear.
  intros. rewrite hlist_app_nil_r.
  generalize dependent (app_nil_r_trans ls').
  generalize dependent (ls' ++ nil).
  destruct e. reflexivity.
Defined.

Lemma member_lift_member_lift:
  forall {T} (tvs' tvs0 z' : list T)
    (tvs : list T) (t : T) (m : member t (tvs ++ tvs')),
    member_lift (tvs0 ++ tvs') z' tvs (member_lift tvs' tvs0 tvs m) =
    match app_ass_trans z' tvs0 tvs' in (_ = x0) return (member t (tvs ++ x0)) with
    | eq_refl => member_lift tvs' (z' ++ tvs0) tvs m
    end.
Proof.
  clear.
  induction tvs; simpl.
  { induction z'; simpl in *.
    { reflexivity. }
    { intros. rewrite IHz'; clear.
      destruct (app_ass_trans z' tvs0 tvs'). reflexivity. } }
  { intros. destruct (member_caseT m).
    { destruct s; subst.
      clear. destruct (app_ass_trans z' tvs0 tvs'). reflexivity. }
    { destruct s; subst.
      rewrite IHtvs. clear. destruct (app_ass_trans z' tvs0 tvs'). reflexivity. } }
Defined.

(** Not needed here *)
Lemma MN_cast : forall T (t t' : T) ts ts' (pf : ts = ts') (m : member t ts),
    match pf in _ = X return member t (t' :: X) with
    | eq_refl => MN t' m
    end = MN t' match pf with
                | eq_refl => m
                end.
Proof.
  clear. intros; subst; reflexivity.
Defined.

Lemma MZ_cast : forall T (t : T) ts ts' (pf : ts = ts'),
    match pf in _ = X return member t (t :: X) with
    | eq_refl => MZ t _
    end = MZ t _.
Proof.
  clear. intros; subst; reflexivity.
Defined.


Lemma app_nil_r_trans_app : forall T (ls ls' : list T),
    app_nil_r_trans (ls ++ ls') = match eq_sym (app_ass_trans ls ls' nil) with
                                  | eq_refl => f_equal (fun x => ls ++ x) (app_nil_r_trans ls')
                                  end.
Proof.
  Transparent app_nil_r_trans.
  clear.
  induction ls; simpl.
  { intros. destruct (app_nil_r_trans ls'). reflexivity. }
  { intros. rewrite IHls; clear.
    generalize (app_nil_r_trans ls').
    generalize (app_ass_trans ls ls' nil).
    generalize ((ls ++ ls') ++ nil).
    intros; subst. simpl. destruct e0; reflexivity. }
Defined.

Lemma to_f_equal : forall (T U : Type) (a b : T) (pf : a = b) (F : T -> U),
    match pf in _ = X return F a = F X with
    | eq_refl => eq_refl
    end = f_equal F pf.
Proof. reflexivity. Defined.
Lemma eq_sym_f_equal : forall (T U : Type) (a b : T) (pf : a = b) (F : T -> U),
    eq_sym (f_equal F pf) = f_equal F (eq_sym pf).
Proof. clear; intros; subst; reflexivity. Defined.
Lemma match_f_equal : forall (T U : Type) (F : T -> U) (R : U -> Type) (a b : T) (pf : a = b) z,
    match f_equal F pf in _ = X return R X with
    | eq_refl => z
    end = match pf in _ = X return R (F X) with
          | eq_refl => z
          end.
Proof.
  clear. intros; subst; reflexivity. Defined.

Lemma member_weaken_member_weaken:
  forall (T : Type) (tvs' tvs0 z' : list T) (t : T) (m : member t tvs'),
    member_lift tvs' tvs0 z' (member_weaken z' m) = member_weaken z' (member_weaken tvs0 m).
Proof.
  clear. induction z'; simpl; intros; f_equal; auto.
Defined.

Lemma member_lift_by_nil:
  forall T (tvs ts' : list T) (t : T) (m : member t (tvs ++ ts')),
    member_lift ts' nil tvs m = m.
Proof.
  clear.
  induction tvs; simpl; auto.
  { intros.
    destruct (member_caseT m) as [ [ ? ? ] | [ ? ? ] ]; subst; auto.
    f_equal; auto. }
Defined.
Lemma hlist_map_id : forall T (F : T -> Type) ls (hs : hlist F ls),
    hlist_map (fun _ x => x) hs = hs.
Proof. clear.
       induction hs; simpl; f_equal; eauto.
Defined.


Lemma member_lift_swap :
  forall {T} (tvs' tvs0 z' tvs : list T) (t : T) (m : member t (tvs ++ tvs')),
    member_lift tvs' tvs0 (tvs ++ z')
                match eq_sym (app_ass_trans tvs z' tvs') in (_ = x0) return (member t x0) with
                | eq_refl => member_lift tvs' z' tvs m
                end =
    match eq_sym (app_ass_trans tvs z' (tvs0 ++ tvs')) in (_ = x0) return (member t x0) with
    | eq_refl => member_lift (tvs0 ++ tvs') z' tvs (member_lift tvs' tvs0 tvs m)
    end.
Proof.
  clear.
  induction tvs; simpl.
  { eapply member_weaken_member_weaken. }
  { intros.
    destruct (member_caseT m) as [ [ ? ? ] | [ ? ? ] ]; subst; autorewrite_with_eq_rw.
    { clear.
      repeat rewrite to_f_equal.
      repeat rewrite eq_sym_f_equal.
      repeat rewrite match_f_equal.
      repeat rewrite MZ_cast. reflexivity. }
    { specialize (IHtvs _ x); clear - IHtvs.
      revert IHtvs.
      simpl. generalize (app_ass_trans tvs z' tvs').
      generalize (app_ass_trans tvs z' (tvs0 ++ tvs')).
      generalize (member_lift (tvs0 ++ tvs') z' tvs (member_lift tvs' tvs0 tvs x)).
      generalize (member_lift tvs' z' tvs x).
      generalize (@member_lift T t tvs' tvs0 (tvs ++ z')).
      destruct e. destruct e. simpl; intros.
      f_equal; auto. } }
Defined.

Lemma hlist_map_cast_contents
  : forall U (a b : U) T (F : T -> Type) (G : U -> T -> Type) (f : forall t, F t -> G a t) ls (hs : hlist F ls)
      (pf : a = b),
    match pf in _ = X return hlist (G X) ls with
    | eq_refl => @hlist_map T F (G a) f _ hs
    end = hlist_map (fun t x => match pf in _ = X return G X _ with
                             | eq_refl => f t x
                             end) hs.
Proof.
  clear. intros; subst. reflexivity.
Defined.


Definition Rforall {T : Type} {F : T -> Type} (R : forall t, F t -> F t -> Prop)
: (forall t, F t) -> (forall t, F t) -> Prop :=
  fun l r => forall t, R t (l t) (r t).

Check @member_lift.

Theorem members_app : forall T (ls ls' : list T),
    members (ls ++ ls') =
    hlist_app
      (hlist_map (fun t m =>
                    match app_nil_r_trans ls' in _ = X return member t (ls ++ X) with
                    | eq_refl => member_lift nil ls' ls
                                            match eq_sym (app_nil_r_trans ls) in _ = X return member t X with
                                            | eq_refl => m
                                            end
                    end) (members ls))
      (hlist_map (fun t m => member_weaken ls m) (members ls')).
Proof.
  induction ls; simpl; intros.
  { symmetry. apply hlist_map_id. }
  { f_equal.
    { repeat rewrite to_f_equal.
      repeat rewrite eq_sym_f_equal.
      rewrite match_f_equal.
      rewrite MZ_cast.
      clear.
      destruct (app_nil_r_trans ls'). reflexivity. }
    { rewrite IHls; clear IHls.
      rewrite hlist_app_hlist_map.
      repeat rewrite hlist_map_hlist_map.
      f_equal.
      eapply hlist_map_ext. intros.
      repeat rewrite to_f_equal.
      repeat rewrite eq_sym_f_equal.
      rewrite match_f_equal.
      rewrite MN_cast.
      destruct (app_nil_r_trans ls').
      reflexivity. } }
Defined.

Lemma hlist_Forall2_hlist_app : forall T (F G : T -> Type) (P : forall t, F t -> G t -> Prop) ls ls'
                                  (hs : hlist F ls) (hs' : hlist F ls')
                                  (gs : hlist G ls) (gs' : hlist G ls'),
    (hlist_Forall2 P hs gs /\ hlist_Forall2 P hs' gs') <->
    hlist_Forall2 P (hlist_app hs hs') (hlist_app gs gs').
Proof.
  clear. split.
  { destruct 1.
    induction H; simpl; intros; try constructor; auto. }
  { induction hs; simpl.
    { rewrite (hlist_eta gs). simpl. split; eauto. constructor. }
    { rewrite (hlist_eta gs). simpl. intros.
      eapply hlist_Forall2_inj in H. destruct H.
      eapply IHhs in H0. destruct H0. simpl in *.
      split; [ constructor | ]; eauto. } }
Defined.


(** ABOVE THIS CAN BE MOVED OUT **)

(* This is the universe of the reified language *)
Universe Urefl.

Section SimpleCat.
  Variable I : Type.

  (** Category *)
  Class SCat (arr : I -> I -> Type) : Type :=
  { rel : forall {i i'}, arr i i' -> arr i i' -> Prop
  ; id : forall i, arr i i
  ; compose : forall {i i' i''}, arr i' i'' -> arr i i' -> arr i i''
  ; Reflexive_rel :> forall {i i'}, Reflexive (@rel i i')
  ; Transitive_rel :> forall {i i'}, Transitive (@rel i i')
  ; id_compose : forall i i' (m : arr i i'), rel (compose (@id _) m) m
  ; compose_id : forall i i' (m : arr i i'), rel (compose m (@id _)) m
  ; compose_compose : forall i i' i'' i''' (a : arr i i') (b : arr i' i'') (c : arr i'' i'''),
      rel (compose c (compose b a)) (compose (compose c b) a)
  ; Proper_compose : forall {i i' i''}, Proper (rel ==> rel ==> rel) (@compose i i' i'')
  }.

  Arguments rel [_] {_ _} _.
  Arguments id {_ _} {_}.
  Arguments compose {_ _} {_ _ _} _ _.

  (** Functor *)
  Class SFunctor (arr1 arr2 : I -> I -> Type) (SC1 : SCat arr1) (SC2 : SCat arr2)
  : Type :=
  { apply : forall {i i'}, arr1 i i' -> arr2 i i'
  ; apply_id : forall {i}, rel i (apply (@id _ SC1 i)) (@id _ _ _)
  ; apply_compose : forall i i' i'' (a : arr1 i' i'') (b : arr1 i i'),
      rel _ (apply (compose a b)) (compose (apply a) (apply b))
  }.

End SimpleCat.

Section subst_is_cat.
  Variable Tsymbol : Type.
  Variable Esymbol : type Tsymbol -> Type.

  Variable tus : list (Tuvar Tsymbol).

  Definition Vmigrator (tvs tvs' : list (type Tsymbol)) : Type :=
    hlist (wtexpr Esymbol tus tvs') tvs.

  Definition Vmigrator_id {tvs} : Vmigrator tvs tvs :=
    hlist_map (fun t m => wtVar m) (members tvs).

  Definition Vmigrator_compose {tvs tvs' tvs''} (g : Vmigrator tvs' tvs'')
  : Vmigrator tvs tvs' -> Vmigrator tvs tvs'' :=
    hlist_map (fun t e => subst g e).

  Variable Rexpr : forall tvs t, wtexpr Esymbol tus tvs t -> wtexpr Esymbol tus tvs t -> Prop.

  Definition RVmigrator (tvs tvs' : list (type Tsymbol))
  : Vmigrator tvs tvs' -> Vmigrator tvs tvs' -> Prop :=
    @hlist_Forall2 _ _ _ (fun _ e1 e2 => Rexpr e1 e2) _.

  Variable Refl_Rexpr : forall tvs t, Reflexive (@Rexpr tvs t).
  Variable Trans_Rexpr : forall tvs t, Transitive (@Rexpr tvs t).

  Theorem Refl_RVmigrator : forall tvs tvs', Reflexive (@RVmigrator tvs tvs').
  Proof.
    red. red.
    induction x; constructor.
    - reflexivity.
    - assumption.
  Defined.

  Theorem Trans_RVmigrator : forall tvs tvs', Transitive (@RVmigrator tvs tvs').
  Proof.
    red. red.
    induction 1.
    - rewrite (hlist_eta z). constructor.
    - intro. eapply hlist_Forall2_inj in H1.
      rewrite (hlist_eta z). destruct H1. constructor; auto. etransitivity; eassumption.
  Defined.

  Lemma subst_id : forall tvs ts t (e : wtexpr Esymbol tus (ts ++ tvs) t),
      subst Vmigrator_id e = e.
  Proof.
    intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    - unfold Vmigrator_id. rewrite hlist_get_hlist_map.
      rewrite hlist_get_members. reflexivity.
    - f_equal; eauto.
    - f_equal.
      etransitivity; [ | eapply H ].
      f_equal. unfold Vmigrator_id. simpl.
      repeat rewrite hlist_map_hlist_map.
      reflexivity.
    - f_equal. clear - H.
      induction H; simpl; auto.
      f_equal; eauto.
  Defined.

  Theorem Vmigrator_id_compose : forall i i' (m : Vmigrator i i'),
      RVmigrator (Vmigrator_compose (@Vmigrator_id _) m) m.
  Proof.
    red.
    unfold Vmigrator_compose; intros.
    eapply hlist_Forall2_hlist_map_l.
    eapply hlist_Forall2_hlist_Forall.
    induction m; constructor; eauto.
    generalize (@subst_id _ nil _ f). simpl.
    intro H; rewrite H. reflexivity.
  Defined.

  Theorem Vmigrator_compose_id : forall i i' (m : Vmigrator i i'),
      RVmigrator (Vmigrator_compose m (@Vmigrator_id _)) m.
  Proof.
    red.
    unfold Vmigrator_compose; intros.
    eapply hlist_Forall2_hlist_map_l.
    unfold Vmigrator_id.
    eapply hlist_Forall2_hlist_map_l.
    simpl.
    eapply hlist_Forall2_members_l.
    eapply hlist_Forall_pure. intros. reflexivity.
  Defined.

  Definition Vmigrator_inr i i' ts
  : Vmigrator i i' -> Vmigrator i (ts ++ i') :=
    hlist_map (fun t e => wtexpr_lift ts nil e).

  Definition wtexpr_post_weaken i' ts
  : forall t, wtexpr _ tus _ t -> wtexpr _ _ _ t :=
    match app_nil_r_trans i' in _ = X , app_nil_r_trans ts in _ = Y
          return forall t, wtexpr _ _ X t -> wtexpr Esymbol _ (_ ++ Y) t
    with
    | eq_refl , eq_refl => @wtexpr_lift _ _ _ _ ts i'
    end.

  Definition Vmigrator_inl i i' ts
  : Vmigrator i i' -> Vmigrator i (i' ++ ts) :=
    hlist_map (@wtexpr_post_weaken _ _).

  Definition Vmigrator_cofork a b d
  : Vmigrator a d -> Vmigrator b d -> Vmigrator (a ++ b) d :=
    @hlist_app _ _ _ _.

  Theorem Vmigrator_cofork_compose : forall i i' i'' i''' a b d,
      RVmigrator (Vmigrator_compose d (@Vmigrator_cofork i i' i'' a b))
                 ((@Vmigrator_cofork i i' i''' (Vmigrator_compose d a) (Vmigrator_compose d b))).
  Proof.
    clear - Refl_Rexpr.
    unfold Vmigrator_compose, Vmigrator_cofork, RVmigrator. simpl.
    intros. rewrite <- hlist_app_hlist_map.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    apply hlist_Forall2_hlist_Forall.
    apply hlist_Forall_pure.
    intros; reflexivity.
  Defined.

  Lemma wtVar_cast:
    forall (tvs tvs' : list (type Tsymbol)) (t : type Tsymbol)
      (x : member t tvs) (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus x0 t with
      | eq_refl => wtVar x
      end
      = wtVar match pf in (_ = x0) return member t x0 with
              | eq_refl => x
              end.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.

  Lemma wtVar_cast_compose :
    forall (tvs tvs' : list (type Tsymbol)) F (t : type Tsymbol)
      (x : member t (F tvs)) (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus (F x0) t with
      | eq_refl => wtVar x
      end
      = wtVar match pf in (_ = x0) return member t (F x0) with
              | eq_refl => x
              end.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.
  Lemma wtAbs_cast_compose :
    forall (tvs tvs' : list (type Tsymbol)) F (t u : type Tsymbol)
      (x : wtexpr Esymbol tus (u::_) t) (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus (F x0) _ with
      | eq_refl => wtAbs x
      end
      = wtAbs match pf in (_ = x0) return wtexpr _ _ (u::F x0) t with
              | eq_refl => x
              end.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.
  Lemma wtApp_cast_compose :
    forall (tvs tvs' : list (type Tsymbol)) F (t u : type Tsymbol)
      f x (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus (F x0) t with
      | eq_refl => wtApp f x
      end
      = wtApp match pf in (_ = x0) return wtexpr Esymbol tus (F x0) _ with
              | eq_refl => f
              end
              match pf in (_ = x0) return wtexpr Esymbol tus (F x0) u with
              | eq_refl => x
              end.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.
  Lemma wtInj_cast_compose :
    forall (tvs tvs' : list (type Tsymbol)) F (t : type Tsymbol)
      x (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus (F x0) t with
      | eq_refl => wtInj x
      end
      = wtInj x.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.
  Lemma wtUVar_cast_compose :
    forall (tvs tvs' : list (type Tsymbol)) F ts t
      (x : member (ts,t) tus) xs (pf : tvs = tvs'),
      match pf in (_ = x0) return wtexpr Esymbol tus (F x0) _ with
      | eq_refl => wtUVar x xs
      end
      = wtUVar x match pf in _ = X return hlist _ _ with
                 | eq_refl => xs
                 end.
  Proof.
    clear. intros; subst. reflexivity.
  Defined.
  Arguments wtexpr_lift {_ _} _ _ _ _ _.


  Lemma wtexpr_lift_wtexpr_lift :
    forall (tvs' tvs0 : list (type Tsymbol)) (z' : list (type Tsymbol)) ts
      (x : type Tsymbol) (w : wtexpr Esymbol tus (ts ++ tvs') x),
      wtexpr_lift tus (tvs0 ++ tvs') z' ts x (wtexpr_lift tus tvs' tvs0 ts x w) =
      match app_ass_trans z' tvs0 tvs' in _ = X
            return wtexpr Esymbol tus (ts ++ X) x
      with
      | eq_refl => wtexpr_lift tus tvs' (z' ++ tvs0) ts x w
      end.
  Proof.
    clear.
    do 3 intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    { rewrite wtVar_cast_compose. f_equal.
      eapply member_lift_member_lift. }
    { destruct (app_ass_trans z' tvs0 tvs'). reflexivity. }
    { rewrite H. rewrite H0. clear. destruct (app_ass_trans z' tvs0 tvs'). reflexivity. }
    { rewrite H. clear. destruct (app_ass_trans z' tvs0 tvs'). reflexivity. }
    { rewrite wtUVar_cast_compose. f_equal.
      rewrite hlist_map_hlist_map.
      clear - H. induction H.
      { simpl. destruct (app_ass_trans z' tvs0 tvs'). reflexivity. }
      { simpl. rewrite H; clear H.
        rewrite IHhlist_Forall. clear.
        destruct (app_ass_trans z' tvs0 tvs'). reflexivity. } }
  Defined.

Lemma wtexpr_lift_by_nil : forall ts' ts t (e : wtexpr Esymbol tus (ts ++ ts') t),
    wtexpr_lift tus ts' nil ts t e = e.
Proof.
  clear. intro.
  refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; try f_equal; eauto.
  { apply member_lift_by_nil. }
  { clear - H.
    induction H; simpl; f_equal; auto. }
Defined.




  Lemma wtexpr_lift_wtexpr_lift' :
    forall (tvs' tvs0 : list (type Tsymbol)) (z' : list (type Tsymbol)) ts
      (x : type Tsymbol) (w : wtexpr Esymbol tus (ts ++ tvs') x),
      wtexpr_lift tus tvs' tvs0 (ts ++ z') x (match eq_sym (app_ass_trans ts z' tvs') with
                                              | eq_refl => wtexpr_lift tus tvs' z' ts x w
                                              end) =
      match eq_sym (app_ass_trans ts z' (tvs0 ++ tvs')) in _ = X return wtexpr _ _ X _
      with
      | eq_refl =>
        match app_ass_trans z' tvs0 tvs' in _ = X return wtexpr _ _ (ts ++ X) _
        with
        | eq_refl => wtexpr_lift tus tvs' (z' ++ tvs0) ts x w
        end
      end.
  Proof.
    clear.
    do 3 intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    { rewrite wtVar_cast.
      rewrite wtVar_cast_compose.
      rewrite wtVar_cast.
      simpl.
      f_equal. clear.
      rewrite <- member_lift_member_lift.

      rewrite member_lift_swap. reflexivity. }

    { repeat rewrite wtInj_cast_compose.
      repeat rewrite wtInj_cast_compose with (F:=fun x => x).
      reflexivity. }
    { repeat rewrite wtApp_cast_compose.
      repeat rewrite wtApp_cast_compose with (F:=fun x => x).
      simpl. f_equal; eauto. }
    { repeat rewrite wtAbs_cast_compose.
      repeat rewrite wtAbs_cast_compose with (F:=fun x => x).
      simpl. f_equal.
      generalize dependent (app_ass_trans tvs z' tvs').
      generalize dependent (app_ass_trans tvs z' (tvs0 ++ tvs')).
      generalize dependent (app_ass_trans z' tvs0 tvs').
      destruct e.
      generalize (wtexpr_lift tus tvs' z' (d :: tvs) c f).
      generalize (wtexpr_lift tus tvs' (z' ++ tvs0) (d :: tvs) c f).
      generalize (@wtexpr_lift _ Esymbol tus tvs' tvs0 (d :: tvs ++ z') c).
      clear. simpl.
      generalize ((tvs ++ z') ++ tvs').
      generalize ((tvs ++ z') ++ tvs0 ++ tvs').
      intros; subst. apply H. }
    { rewrite wtUVar_cast_compose with (F:=fun x => tvs ++ x).
      repeat rewrite wtUVar_cast_compose with (F:=fun x => x).
      simpl. f_equal.
      repeat match goal with
      | |- context [ match ?PF in @eq _ _ X return hlist (@?G X) _ with
                    | eq_refl => @hlist_map ?T ?F ?G' ?f ?ls ?xs
                    end ] =>
        match type of PF with
        | ?X = _ =>
            let H := fresh in
            generalize (@hlist_map_cast_contents _ _ _ T F G f ls xs PF); intro H;
              change_rewrite H; clear H
        end
      end.
      rewrite hlist_map_hlist_map.
      clear - H. induction H.
      { reflexivity. }
      { simpl; f_equal; auto. } }
  Defined.


  Lemma wtexpr_lift_subst:
    forall (tvs : list (type Tsymbol)) tvs'
      (c : Vmigrator tvs tvs')
      ts (x : type Tsymbol) (t : wtexpr Esymbol tus (ts ++ tvs) x)
      z,
      let cl : Vmigrator (ts ++ tvs) (ts ++ z ++ tvs') :=
          Vmigrator_cofork (Vmigrator_inl _ Vmigrator_id)
                           (Vmigrator_cofork Hnil (Vmigrator_inr _ (Vmigrator_inr _ c)))
      in
      let cr : Vmigrator (ts ++ tvs) (ts ++ tvs') :=
          Vmigrator_cofork (Vmigrator_inl _ (Vmigrator_id)) (Vmigrator_inr _ c)
      in
      subst cl t =
      wtexpr_lift tus tvs' z ts _ (subst cr t).
  Proof.
    do 3 intro.
    Opaque app_nil_r_trans.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    { unfold Vmigrator_cofork, Vmigrator_id, Vmigrator_compose, Vmigrator_inl, Vmigrator_inr.
      repeat rewrite hlist_map_hlist_map.
      destruct (member_app_case _ _ m).
      { destruct H. subst.
        do 2 rewrite hlist_get_cast_app_nil_r.
        do 2 rewrite hlist_get_member_lift.
        do 2 rewrite hlist_app_nil_r.
        clear.
        generalize dependent (app_nil_r_trans tvs0).
        generalize dependent (tvs0 ++ nil).
        intros; subst. simpl.
        repeat rewrite hlist_get_hlist_map.
        repeat rewrite hlist_get_members.
        unfold wtexpr_post_weaken.
        autorewrite_with_eq_rw.
        repeat rewrite wtVar_cast. simpl.
        repeat rewrite wtVar_cast_compose. simpl.
        f_equal. clear.
        generalize (match eq_sym (app_nil_r_trans tvs0) in (_ = x0) return (member t x0) with
                    | eq_refl => x
                    end).
        clear. intros.
        rewrite app_nil_r_trans_app.
        destruct (app_nil_r_trans tvs'). simpl in *.
        rewrite member_lift_member_lift.
        destruct (app_ass_trans z tvs' nil). reflexivity. }
      { destruct H; subst.
        do 2 rewrite hlist_get_member_weaken.
        repeat rewrite hlist_get_hlist_map.
        simpl. rewrite wtexpr_lift_wtexpr_lift.
        generalize (wtexpr_lift_wtexpr_lift' tvs' z tvs0 nil).
        simpl. intro H; rewrite H; clear H.
        reflexivity. } }
    { f_equal; eauto. }
    { f_equal.
      specialize (H z).
      etransitivity; [ clear H | etransitivity; [ eapply H | clear H ] ].
      { f_equal. f_equal.
        { clear.
          unfold wtexpr_post_weaken.
          rewrite (@forall_eq_rw (list (type Tsymbol)) (type Tsymbol) _ _ (fun t X => wtexpr Esymbol tus X t -> wtexpr Esymbol tus (d :: tvs0 ++ z ++ tvs') t)).
          rewrite (@impl_eq_rw _ _ _ (app_nil_r_trans (d :: tvs0))).
          rewrite const_eq_rw.
          rewrite (@forall_eq_rw _ _ _ _ _ (app_nil_r_trans (z ++ tvs'))).
          rewrite (@impl_eq_rw _ _ _ (app_nil_r_trans (z ++ tvs'))).
          rewrite const_eq_rw.
          Transparent app_nil_r_trans. simpl.
          destruct (app_nil_r_trans tvs0). simpl.
          destruct (app_nil_r_trans (z ++ tvs')). reflexivity. }
        { unfold Vmigrator_cofork, Vmigrator_id, Vmigrator_inr, Vmigrator_inl.
          rewrite hlist_app_hlist_map.
          repeat rewrite hlist_map_hlist_map.
          clear.
          match goal with
          | |- hlist_app ?L ?R = hlist_app ?L' ?R' =>
            cutrewrite (L = L'); [ cutrewrite (R = R') ; [ reflexivity | eapply hlist_map_ext ] | eapply hlist_map_ext ]
          end.
          { simpl. intros.
            generalize (wtexpr_lift tus tvs' z nil x t); clear; intros.
            rewrite wtexpr_lift_wtexpr_lift. reflexivity. }
          { simpl. intros.
            unfold wtexpr_post_weaken.
            autorewrite_with_eq_rw.
            repeat rewrite wtVar_cast. simpl.
            repeat rewrite wtVar_cast_compose. simpl.
            rewrite wtVar_cast_compose with (F:=fun X => d :: tvs0 ++ X).
            f_equal.
            destruct (app_nil_r_trans (z ++ tvs')).
            generalize dependent (app_nil_r_trans tvs0).
            clear.
            generalize (@member_lift (type Tsymbol) x (@nil (type Tsymbol)) (z ++ tvs') tvs0).
            generalize dependent (tvs0 ++ nil).
            intros; subst. reflexivity. } } }
      { f_equal. f_equal.
        f_equal.
        { unfold wtexpr_post_weaken. autorewrite_with_eq_rw.
          simpl. rewrite wtVar_cast. simpl.
          rewrite wtVar_cast_compose with (F:=fun X => d :: tvs0 ++ X).
          f_equal; clear.
          destruct (app_nil_r_trans tvs0); simpl.
          destruct (app_nil_r_trans tvs'). reflexivity. }
        { unfold Vmigrator_cofork, Vmigrator_inr, Vmigrator_inl, Vmigrator_id.
          rewrite hlist_app_hlist_map.
          repeat rewrite hlist_map_hlist_map.
          match goal with
          | |- hlist_app ?L ?R = hlist_app ?L' ?R' =>
            cutrewrite (L = L'); [ cutrewrite (R = R') ; [ reflexivity | eapply hlist_map_ext ] | eapply hlist_map_ext ]
          end.
          { intros. rewrite wtexpr_lift_wtexpr_lift. reflexivity. }
          { intros. unfold wtexpr_post_weaken.
            autorewrite_with_eq_rw.
            repeat rewrite wtVar_cast. simpl.
            repeat rewrite wtVar_cast_compose. simpl.
            rewrite wtVar_cast_compose with (F:=fun X => d :: tvs0 ++ X).
            f_equal.
            destruct (app_nil_r_trans tvs').
            clear.
            generalize (@member_lift (type Tsymbol) x (@nil (type Tsymbol)) tvs' tvs0).
            generalize (app_nil_r_trans tvs0).
            generalize dependent (tvs0 ++ nil).
            intros; subst. reflexivity. } } } }
    { f_equal.
      rewrite hlist_map_hlist_map.
      clear - H.
      induction H; simpl; f_equal; eauto. }
  Defined.


  Lemma subst_subst:
    forall (i' : list (type Tsymbol))
      ts (t : type Tsymbol) (x : wtexpr Esymbol tus (ts ++ i') t)
      i'' i'''  (c : Vmigrator i'' i''') (b : Vmigrator (ts ++ i') i'') ,
      subst c (subst b x) =
      subst (hlist_map (fun (t0 : type Tsymbol) (e : wtexpr Esymbol tus i'' t0) => subst c e) b) x.
  Proof.
    clear. intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _); simpl; intros; eauto.
    { rewrite hlist_get_hlist_map. reflexivity. }
    { f_equal; eauto. }
    { f_equal. rewrite hlist_map_hlist_map.
      rewrite H; clear H. simpl.
      rewrite hlist_map_hlist_map.
      f_equal. f_equal.
      eapply hlist_map_ext.
      intros.
      generalize (@subst_wtexpr_lift _ Esymbol tus nil _ _ t (d :: nil)
                                     _ Hnil (Hcons (wtVar (MZ d i''')) Hnil)
                                     (hlist_map (ls:=i'') (wtexpr_lift _ i''' (d::nil) nil) c0)).
      simpl. intro H.
      change_rewrite H; clear H.
      etransitivity; [ | etransitivity; [
      eapply (@wtexpr_lift_subst _ i''' c0 nil x t (d::nil)) | ] ].
      { f_equal.
        unfold Vmigrator_cofork, Vmigrator_inl, Vmigrator_id, Vmigrator_inr.
        repeat rewrite hlist_map_hlist_map. simpl.
        eapply hlist_map_ext. intros.
        symmetry; apply (@wtexpr_lift_wtexpr_lift i''' (d :: nil) nil nil x0 t0). }
      { f_equal.
        unfold Vmigrator_cofork, Vmigrator_inl, Vmigrator_inr, Vmigrator_id.
        repeat rewrite hlist_map_hlist_map. simpl.
        f_equal.
        etransitivity; [ | eapply hlist_map_id ].
        eapply hlist_map_ext.
        intros. rewrite wtexpr_lift_by_nil. reflexivity. } }
    { rewrite hlist_map_hlist_map. f_equal.
      clear - H.
      induction H; simpl; f_equal; eauto. }
  Defined.

  Theorem Vmigrator_compose_compose
  : forall i i' i'' i''' (a : Vmigrator i i') (b : Vmigrator i' i'') (c : Vmigrator i'' i'''),
      RVmigrator (Vmigrator_compose c (Vmigrator_compose b a))
                 (Vmigrator_compose (Vmigrator_compose c b) a).
  Proof.
    unfold Vmigrator_compose. intros.
    rewrite hlist_map_hlist_map.
    red.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    eapply hlist_Forall2_hlist_Forall.
    eapply hlist_Forall_pure.
    intros.
    generalize (@subst_subst _ nil _ x _ _ c b). simpl.
    intro H; rewrite H; clear H. reflexivity.
  Defined.

  Theorem Vmigrator_cofork_inl : forall i i' i'' ts v a b,
      RVmigrator (Vmigrator_compose (@Vmigrator_cofork i i' i'' a b) (@Vmigrator_inl ts _ _ v))
                 (Vmigrator_compose a v).
  Proof.
    unfold RVmigrator, Vmigrator_compose, Vmigrator_inl.
    intros.
    repeat rewrite hlist_Forall2_hlist_map_l.
    repeat rewrite hlist_Forall2_hlist_map_r.
    eapply hlist_Forall2_hlist_Forall.
    eapply hlist_Forall_pure. intros.
    unfold Vmigrator_cofork, wtexpr_post_weaken.
    autorewrite_with_eq_rw.
    clear - Refl_Rexpr.
    generalize (@subst_wtexpr_lift _ Esymbol tus _ _ t
                                   match eq_sym (app_nil_r_trans i) in (_ = x0) return (wtexpr Esymbol tus x0 t) with
                                   | eq_refl => x
                                   end _ _ a b Hnil).
    repeat rewrite hlist_app_nil_r.
    generalize (@wtexpr_lift _ Esymbol tus nil i' i t). clear - Refl_Rexpr.
    (** This should be a 'generalize dependent', but Ltac doesn't find all of the
     ** instances. **)
    assert(forall (e : i ++ nil = i)
    (w : wtexpr Esymbol tus (i ++ nil) t -> wtexpr Esymbol tus (i ++ i' ++ nil) t),
  subst
    (hlist_app a
       match eq_sym (app_nil_r_trans i') in (_ = t0) return (hlist (wtexpr Esymbol tus i'') t0) with
       | eq_refl => b
       end) (w match eq_sym e in (_ = x0) return (wtexpr Esymbol tus x0 t) with
               | eq_refl => x
               end) =
  subst
    match eq_sym e in (_ = t0) return (hlist (wtexpr Esymbol tus i'') t0) with
    | eq_refl => a
    end match eq_sym e in (_ = x0) return (wtexpr Esymbol tus x0 t) with
        | eq_refl => x
        end ->
  Rexpr
    (subst (hlist_app a b)
       match app_nil_r_trans i' in (_ = X) return (wtexpr Esymbol tus (i ++ X) t) with
       | eq_refl =>
           w
             match eq_sym e in (_ = x0) return (wtexpr Esymbol tus x0 t) with
             | eq_refl => x
             end
       end) (subst a x)).
    { generalize (i ++ nil). intros; subst; simpl in *.
      rewrite <- H; clear H.
      generalize (app_nil_r_trans i').
      generalize dependent (i' ++ nil).
      intros; subst. reflexivity. }
    { eapply H. }
  Defined.

  Theorem Vmigrator_cofork_inr : forall i i' i'' ts v a b,
      RVmigrator (Vmigrator_compose (@Vmigrator_cofork i i' i'' a b) (@Vmigrator_inr ts _ _ v))
                 (Vmigrator_compose b v).
  Proof.
    unfold RVmigrator, Vmigrator_compose, Vmigrator_inr.
    intros.
    repeat rewrite hlist_Forall2_hlist_map_l.
    repeat rewrite hlist_Forall2_hlist_map_r.
    eapply hlist_Forall2_hlist_Forall.
    eapply hlist_Forall_pure. intros.
    unfold Vmigrator_cofork, wtexpr_post_weaken.
    clear - Refl_Rexpr.
    generalize (@subst_wtexpr_lift _ Esymbol tus nil _ _ x _ _ Hnil a b).
    simpl. intro H; rewrite H. reflexivity.
  Defined.

  Variable Proper_wtApp
  : forall tvs t u, Proper (@Rexpr tvs _ ==> @Rexpr _ t ==> @Rexpr _ u) (@wtApp _ _ tus tvs _ _).
  Variable Proper_wtAbs
  : forall tvs t u, Proper (@Rexpr (t :: tvs) u ==> @Rexpr _ _) (@wtAbs _ _ tus tvs _ _).
  Variable Proper_wtUVar
  : forall ts tvs t, Proper (@eq (member (ts,t) tus) ==> hlist_Forall2 (@Rexpr tvs) (ts:=ts) ==> @Rexpr _ _)
                       (@wtUVar _ _ tus tvs _ _).


  Lemma Vmigrator_id_app : forall tvs tvs',
      RVmigrator (@Vmigrator_id (tvs ++ tvs'))
                 (Vmigrator_cofork (Vmigrator_inl tvs' Vmigrator_id)
                                   (Vmigrator_inr tvs Vmigrator_id)).
  Proof.
    unfold RVmigrator, Vmigrator_cofork, Vmigrator_inl, Vmigrator_inr, Vmigrator_id; intros.
    repeat rewrite hlist_Forall2_hlist_map_l.
    repeat rewrite hlist_Forall2_hlist_map_r.
    repeat rewrite hlist_map_hlist_map.
    rewrite members_app.
    apply hlist_Forall2_hlist_app.
    split.
    { rewrite hlist_Forall2_hlist_map_l.
      rewrite hlist_Forall2_hlist_map_r.
      apply hlist_Forall2_hlist_Forall.
      apply hlist_Forall_pure.
      intros.
      unfold wtexpr_post_weaken.
      destruct (app_nil_r_trans tvs').
      autorewrite_with_eq_rw.
      rewrite wtVar_cast.
      reflexivity. }
    { rewrite hlist_Forall2_hlist_map_l.
      rewrite hlist_Forall2_hlist_map_r.
      apply hlist_Forall2_hlist_Forall.
      apply hlist_Forall_pure.
      intros.
      reflexivity. }
  Defined.

  (** TODO: This should move *)
  Arguments subst {_ _ _ _ _} _ [_] _.


  Definition Vsubst {tvs tvs'}
             (xs : Vmigrator tvs' tvs)
             {t} (e : wtexpr Esymbol tus tvs' t)
  : wtexpr Esymbol tus tvs t :=
    match e in wtexpr _ _ _ t return wtexpr _ tus tvs t
    with
    | wtVar v => hlist_get v xs
    | wtInj s => wtInj s
    | wtApp f x => wtApp (subst xs f) (subst xs x)
    | wtAbs e =>
      let xs' :=
          Vmigrator_cofork (Vmigrator_inl _ Vmigrator_id)
                           (Vmigrator_inr (_::nil) xs)
      in wtAbs (subst xs' e)
    | wtUVar u ys => wtUVar u (hlist_map (subst xs) ys)
    end.

  Theorem subst_Vsubst : forall tvs tvs' xs t e,
      subst xs e = @Vsubst tvs tvs' xs t e.
  Proof.
    induction e; simpl; auto.
    f_equal. f_equal. f_equal.
    unfold wtexpr_post_weaken.
    autorewrite_with_eq_rw.
    rewrite wtVar_cast. simpl.
    destruct (app_nil_r_trans tvs). reflexivity.
  Defined.

  (** TODO: Does this follow from simpler laws? *)
  Lemma Vmigrator_cofork_lemma:
    forall (tvs tvs' tvs0 : list (type Tsymbol)) (d : type Tsymbol) (y : Vmigrator tvs (tvs0 ++ tvs')),
      @Vmigrator_cofork (d :: @nil (type Tsymbol)) (tvs0 ++ tvs)
                        ((d :: @nil (type Tsymbol)) ++ tvs0 ++ tvs')
                        (@Vmigrator_inl (d :: @nil (type Tsymbol)) (d :: @nil (type Tsymbol))
                                        (tvs0 ++ tvs') (@Vmigrator_id (d :: @nil (type Tsymbol))))
                        (@Vmigrator_inr (tvs0 ++ tvs) (tvs0 ++ tvs') (d :: @nil (type Tsymbol))
                                        (@Vmigrator_cofork tvs0 tvs (tvs0 ++ tvs')
                                                           (@Vmigrator_inl tvs0 tvs0 tvs' (@Vmigrator_id tvs0)) y)) =
      @Vmigrator_cofork (d :: tvs0) tvs ((d :: tvs0) ++ tvs')
                        (@Vmigrator_inl (d :: tvs0) (d :: tvs0) tvs' (@Vmigrator_id (d :: tvs0)))
                        (@Vmigrator_inr tvs (tvs0 ++ tvs') (d :: @nil (type Tsymbol)) y).
  Proof.
    clear. intros tvs tvs' tvs0 d y.
    unfold Vmigrator_cofork, Vmigrator_inl, Vmigrator_id, Vmigrator_inr.
    rewrite hlist_app_hlist_map.
    repeat rewrite hlist_map_hlist_map.
    simpl. f_equal.
    { unfold wtexpr_post_weaken.
      autorewrite_with_eq_rw.
      simpl.
      rewrite wtVar_cast_compose.
      rewrite wtVar_cast. simpl.
      rewrite to_f_equal.
      rewrite eq_sym_f_equal.
      rewrite match_f_equal.
      repeat rewrite MZ_cast.
      destruct (app_nil_r_trans tvs'). reflexivity. }
    { f_equal.
      rewrite hlist_map_hlist_map.
      eapply hlist_map_ext. intros.
      unfold wtexpr_post_weaken.
      autorewrite_with_eq_rw.
      destruct (app_nil_r_trans tvs'). simpl.
      repeat rewrite wtVar_cast.
      simpl.
      f_equal.
      repeat rewrite to_f_equal.
      repeat rewrite eq_sym_f_equal.
      rewrite match_f_equal.
      rewrite MN_cast. reflexivity. }
  Defined.

  Lemma hlist_Forall_ap : forall T (F : T -> Type) (P Q : forall t, F t -> Prop) ls (hs : hlist F ls),
      hlist_Forall (fun t x => P t x -> Q t x) hs ->
      hlist_Forall P hs -> hlist_Forall Q hs.
  Proof.
    clear.
    induction 1; intros.
    - constructor.
    - apply hlist_Forall_Hcons_inj in H1.
      destruct H1.
      constructor; auto.
  Defined.

  Lemma Proper_Vmigrator_inr : forall tvs tvs' tvs'',
      Proper (@RVmigrator _ _ ==> @RVmigrator _ _) (@Vmigrator_inr tvs tvs' tvs'').
  Proof.
    clear. unfold Proper, respectful, RVmigrator, Vmigrator_inr.
    intros.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    admit.
  Admitted.
  Lemma Proper_Vmigrator_inl : forall tvs tvs' tvs'',
      Proper (@RVmigrator _ _ ==> @RVmigrator _ _) (@Vmigrator_inl tvs tvs' tvs'').
  Proof.
    clear. unfold Proper, respectful, RVmigrator, Vmigrator_inl.
    intros.
    rewrite hlist_Forall2_hlist_map_l.
    rewrite hlist_Forall2_hlist_map_r.
    admit.
  Admitted.
  Lemma Proper_Vmigrator_cofork : forall tvs tvs' tvs'',
      Proper (@RVmigrator _ _ ==> @RVmigrator _ _ ==> @RVmigrator _ _)
             (@Vmigrator_cofork tvs tvs' tvs'').
  Proof.
    clear. unfold Proper, respectful, RVmigrator, Vmigrator_cofork.
    intros.
    rewrite <- hlist_Forall2_hlist_app. split; auto.
  Defined.

  Lemma Proper_Vmigrator_id : forall tvs,
      Proper (@RVmigrator _ _) (@Vmigrator_id tvs).
  Proof.
    clear - Refl_Rexpr. unfold Proper, respectful, RVmigrator, Vmigrator_id.
    intros.
    eapply hlist_Forall2_hlist_Forall.
    eapply hlist_Forall_pure. reflexivity.
  Defined.

  Lemma Proper_hlist_get : forall t tvs tvs',
      Proper (@eq (member t tvs) ==> @RVmigrator _ _ ==> @Rexpr _ _)
             (@hlist_get (type Tsymbol) (wtexpr Esymbol tus tvs') tvs t).
  Proof.
    unfold Proper, respectful; intros; subst.
    clear - H0. induction H0.
    { destruct (member_case y). }
    { destruct (member_case y) as [ [ ? ? ] | [ ? ? ] ]; subst; eauto. }
  Defined.

  Lemma Rexpr_subst:
    forall (tvs tvs' : list (type Tsymbol)) ts (t : type Tsymbol)
      (y0 : wtexpr Esymbol tus (ts ++ tvs) t)
      (x y : Vmigrator tvs (ts ++ tvs')),
      RVmigrator x y ->
      Rexpr (subst (Vmigrator_cofork (Vmigrator_inl _ Vmigrator_id) x) y0)
            (subst (Vmigrator_cofork (Vmigrator_inl _ Vmigrator_id) y) y0).
  Proof.
    do 2 intro.
    refine (@wtexpr_ind_app _ _ _ _ _ _ _ _ _ _).
    { simpl. clear - Refl_Rexpr.
      intros. eapply Proper_hlist_get; eauto.
      eapply Proper_Vmigrator_cofork; eauto.
      eapply Proper_Vmigrator_inl.
      eapply Proper_Vmigrator_id. }
    { reflexivity. }
    { simpl; intros; eapply Proper_wtApp; eauto. }
    { intros.
      do 2 rewrite subst_Vsubst.
      unfold Vsubst. eapply Proper_wtAbs.
      specialize (H (Vmigrator_inr (d::nil) x) (Vmigrator_inr (d::nil) y)).
      do 2 rewrite subst_Vsubst in H.
      do 2 rewrite subst_Vsubst.
      clear - H H0.
      do 2 rewrite Vmigrator_cofork_lemma.
      eapply H.
      eapply (@Proper_Vmigrator_inr tvs (tvs0 ++ tvs') (d :: nil)).
      assumption. }
    { intros. simpl.
      eapply Proper_wtUVar; auto.
      rewrite hlist_Forall2_hlist_map_l.
      rewrite hlist_Forall2_hlist_map_r.
      eapply hlist_Forall2_hlist_Forall.
      revert H.
      eapply hlist_Forall_ap.
      eapply hlist_Forall_pure.
      eauto. }
  Defined.

  (** NOTE: If I want to prove `Rexpr ==> Rexpr`, then I need some proof
   ** rule for `Rexpr`
   **)
  Theorem Proper_subst : forall tvs tvs',
    Proper (@RVmigrator tvs tvs' ==> Rforall (fun t => @eq _ ==> @Rexpr _ t))%signature
           (@subst _ Esymbol tus tvs' tvs).
  Proof.
    red. unfold respectful, Rforall. intros.
    subst.
    About subst.
  Admitted.
End subst_is_cat.