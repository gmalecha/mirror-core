Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.

Set Primitive Projections.
Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

Polymorphic Record path@{t} (x y : Type@{t}) : Type :=
{ into : x -> y
; outof : y -> x }.

Polymorphic Definition path_refl@{t u} (x : Type@{t}) : path@{t} x x :=
  {| into := fun x => x
   ; outof := fun x => x |}.

Polymorphic Definition path_sym@{t u} (x y : Type@{t}) (p : path@{t} x y)
: path@{t} y x :=
  {| into := p.(outof)
   ; outof := p.(into) |}.

Polymorphic Definition path_trans@{t u} (x y z : Type@{t})
            (p1 : path@{t} x y) (p2 : path@{t} y z)
: path@{t} x z :=
  {| into  := fun x => p2.(into) (p1.(into) x)
   ; outof := fun x => p1.(outof) (p2.(outof) x) |}.

Polymorphic Definition path_arrow@{u v} {a b : Type@{u}} {c d : Type@{v}}
            (p1 : path@{u} a b) (p2 : path@{v} c d) : path@{v} (a -> c) (b -> d) :=
{| into := fun f x => p2.(into) (f (p1.(outof) x))
 ; outof := fun f x => p2.(outof) (f (p1.(into) x))
 |}.

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

(** NOTE: When these definitions are not in a section, they get the wrong
 ** universe constraints.
 **)
Section pii.
  Polymorphic Universes u0 u1.
  Polymorphic Constraint u0 <= u1.

  Polymorphic Definition pii (t : Type@{u1}) (x : t -> Type@{u0}) : Type@{u1} :=
    forall y : t, x y.

  Polymorphic Definition path_all (T : Type@{u1}) (a b : T -> Type@{u0})
              (p : forall x : T, path (a x) (b x))
    : path (@pii T a) (@pii T b).
  Proof.
    unfold pii.
    constructor.
    { intros. eapply (p y).(into). apply X. }
    { intros. eapply (p y).(outof). apply X. }
  Defined.
End pii.


Section ForallT_hlist_lems.
  Polymorphic Context {T} {F G : T -> Type} (f : forall x, F x -> G x) (P : forall t, G t -> Type).

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

  Polymorphic Definition ForallT_hlist_hd {l ls} {hs : hlist G (l :: ls)} (Fhs : ForallT_hlist P hs)
    : P (hlist_hd hs) :=
    match Fhs in @ForallT_hlist _ _ _ (_ :: _)  hs
          return P (hlist_hd hs)
    with
    | ForallT_Hcons _ _ pf _ => pf
    end.
  Polymorphic Definition ForallT_hlist_tl {l ls} {hs : hlist G (l :: ls)} (Fhs : ForallT_hlist P hs)
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

(* This is the universe of the reified language *)
Universe Urefl.
(* These are the universes of the denotation *)
Universe Uhuge Ularge Usmall Utiny.

(** Universes **)
Inductive univ : Type@{Urefl} :=
| U1 | U0.

Definition univD (u : univ) : Type@{Uhuge} :=
  match u with
  | U1 => Type@{Ularge}
  | U0 => Type@{Usmall}
  end.

Definition uarr (a b : univ) : Type@{Uhuge} :=
  univD a -> univD b.

Definition univD_to_Type {u : univ} (v : univD u) : Type@{Ularge}.
  destruct u; apply v.
Defined.

Coercion univD_to_Type : univD >-> Sortclass.

(** Kinds **)
Inductive kind : univ -> Type@{Urefl} :=
| Karr : kind U0 -> kind U0 -> kind U0
| Kstar : forall n, kind n.

Fixpoint kindD {u} (k : kind u) : univD u :=
  match k in kind u return univD u with
  | Karr a b => kindD a -> kindD b
  | Kstar U0 => Type@{Utiny}
  | Kstar U1 => Type@{Usmall}
  end.

Section simple_dep_types.
  Variable Tsymbol : forall u, kind u -> Type@{Urefl}.

  Record Kuvar : Type :=
  { Tuctx : list (kind U0)
  ; Tukind : kind U0 }.

  Unset Elimination Schemes.
  Inductive type (kus : list Kuvar) (ks : list (kind U0)) : forall u, kind u -> Type@{Urefl} :=
  | TArr : forall u, type kus ks (Kstar U0) -> type kus ks (Kstar u) -> type kus ks (Kstar u)
  | TApp : forall k1 k2, type kus ks (Karr k1 k2) -> type kus ks k1 -> type kus ks k2
  | TPi  : forall (k : kind U0) u, type kus (k :: ks) (Kstar u) -> type kus ks (Kstar U1)
  | TVar : forall k, member k ks -> type kus ks k
  | TInj : forall (k : kind U0), Tsymbol k -> type kus ks k
  | TUVar : forall ku, member ku kus -> hlist (@type kus ks U0) ku.(Tuctx) -> type kus ks ku.(Tukind).
  Arguments TInj [_ _ _] _.
  Arguments TVar [_ _ _] _.
  Arguments TUVar [_ _ _] _ _.
  Set Elimination Schemes.

  Section type_rect_under.
    Variable kus : list Kuvar.
    Variable ks : list (kind U0).
    Variable P : forall ks' u (k : kind u), type kus (ks' ++ ks) k -> Type.

    Hypothesis Harr : forall ks' u t1 t2,
        @P ks' U0 (Kstar U0) t1 -> @P ks' u (Kstar u) t2 -> @P ks' u (Kstar u) (TArr t1 t2).
    Hypothesis Happ : forall ks' k1 k2 t1 t2,
        @P ks' U0 (Karr k1 k2) t1 -> @P ks' _ k1 t2 -> @P ks' _ k2 (TApp t1 t2).
    Hypothesis Hpi : forall ks' (k : kind U0) u t,
        @P (k :: ks') u _ t -> @P ks' U1 _ (@TPi kus _ k _ t).
    Hypothesis Hvar : forall ks' k m, @P ks' U0 k (TVar m).
    Hypothesis Hinj : forall ks' k m, @P ks' U0 k (TInj m).
    Hypothesis Huvar : forall ks' ku (m : member ku kus)
                                     (xs : hlist (@type kus (ks' ++ ks) U0) ku.(Tuctx)),
        ForallT_hlist (@P ks' U0) xs ->
        @P ks' U0 _ (TUVar m xs).

    Fixpoint type_rect_under {ks'} {u} {k : kind u} (t : type kus (ks' ++ ks) k)
    : @P ks' u k t :=
      match t as t in @type _ _ u k
            return @P ks' u k t
      with
      | TArr l r => Harr (type_rect_under l) (type_rect_under r)
      | TApp l r => Happ (type_rect_under l) (type_rect_under r)
      | TPi t    => Hpi (@type_rect_under (_ :: ks') _ _ t)
      | TVar m   => Hvar _ m
      | TInj i   => Hinj _ i
      | TUVar u xs =>
        Huvar _ ((fix gen tus (xs : hlist (@type kus (ks' ++ ks) U0) tus)
                  : ForallT_hlist (@P ks' U0) xs :=
                    match xs as xs return ForallT_hlist (@P ks' U0) xs with
                    | Hnil => ForallT_Hnil
                    | Hcons x xs => @ForallT_Hcons _ _ _ _ _ _ _ (type_rect_under x) (gen _ xs)
                    end) _ xs)
      end.
  End type_rect_under.


  Section type_rect.
    Variable kus : list Kuvar.
    Variable P : forall ks' u (k : kind u), type kus ks' k -> Type.

    Hypothesis Harr : forall ks' u t1 t2,
        @P ks' U0 (Kstar U0) t1 -> @P ks' u (Kstar u) t2 -> @P ks' u (Kstar u) (TArr t1 t2).
    Hypothesis Happ : forall ks' k1 k2 t1 t2,
        @P ks' U0 (Karr k1 k2) t1 -> @P ks' _ k1 t2 -> @P ks' _ k2 (TApp t1 t2).
    Hypothesis Hpi : forall ks' (k : kind U0) u t,
        @P (k :: ks') u _ t -> @P ks' U1 _ (@TPi kus _ k _ t).
    Hypothesis Hvar : forall ks' k m, @P ks' U0 k (TVar m).
    Hypothesis Hinj : forall ks' k m, @P ks' U0 k (TInj m).
    Hypothesis Huvar : forall ks' ku (m : member ku kus)
                                     (xs : hlist (@type kus ks' U0) ku.(Tuctx)),
        ForallT_hlist (@P ks' U0) xs ->
        @P ks' U0 _ (TUVar m xs).

    Fixpoint type_rect {ks'} {u} {k : kind u} (t : type kus ks' k)
    : @P ks' u k t :=
      match t as t in @type _ _ u k
            return @P ks' u k t
      with
      | TArr l r => Harr (type_rect l) (type_rect r)
      | TApp l r => Happ (type_rect l) (type_rect r)
      | TPi t    => Hpi (@type_rect (_ :: ks') _ _ t)
      | TVar m   => Hvar m
      | TInj i   => Hinj _ i
      | TUVar u xs =>
        Huvar _ ((fix gen tus (xs : hlist (@type kus ks' U0) tus)
                  : ForallT_hlist (@P ks' U0) xs :=
                    match xs as xs return ForallT_hlist (@P ks' U0) xs with
                    | Hnil => ForallT_Hnil
                    | Hcons x xs => @ForallT_Hcons _ _ _ _ _ _ _ (type_rect x) (gen _ xs)
                    end) _ xs)
      end.
  End type_rect.

  Definition mx (a b : univ) : univ :=
    match a with
    | U1 => U1
    | U0 => b
    end.

  Fixpoint tmorphism (u : univ) (k : kind u) {struct k}
  : kindD k -> kindD k -> univD u :=
    match k  as k in kind u
          return kindD k -> kindD k -> univD u
    with
    | Karr k1 k2 => fun f g =>
      forall x y : kindD k1,
        tmorphism k1 x x ->
        tmorphism k1 y y ->
        tmorphism k1 x y ->
        tmorphism k2 (f x) (g y)
    | Kstar U0 => path
    | Kstar U1 => path
    end.
  Arguments tmorphism [_] _ _ _.

  Record TSigT0 (k : kind U0) : Type@{Usmall} := mkTSigT0
  { tsigT0      : kindD k
  ; tsigProper0 : tmorphism k tsigT0 tsigT0
  }.

  Record TSigT1 (k : kind U1) : Type@{Ularge} := mkTSigT1
  { tsigT1      : kindD k
  ; tsigProper1 : tmorphism k tsigT1 tsigT1
  }.

  Definition TSigT {u} : kind u -> Type@{Ularge} :=
    match u as u return kind u -> Type@{Ularge} with
    | U0 => TSigT0
    | U1 => TSigT1
    end.

  Definition tarr {a b}
  : TSigT (Kstar a) ->
    TSigT (Kstar b) ->
    TSigT (Kstar (mx a b)).
  refine
    match a as a
        , b as b
          return TSigT (Kstar a) ->
                 TSigT (Kstar b) ->
                 TSigT (Kstar (mx a b))
    with
    | U0 , U0 => fun a b => _
    | U0 , U1 => fun a b => _
    | U1 , U0 => fun a b => _
    | U1 , U1 => fun a b => _
    end.
  all: try (exists (a.(tsigT0) -> b.(tsigT0)); simpl; apply path_refl).
  all: try (exists (a.(tsigT1) -> b.(tsigT0)); simpl; apply path_refl).
  all: try (exists (a.(tsigT0) -> b.(tsigT1)); simpl; apply path_refl).
  all: try (exists (a.(tsigT1) -> b.(tsigT1)); simpl; apply path_refl).
  Defined.

  Definition tapp {a b}
  : TSigT (Karr a b) -> TSigT a -> TSigT b :=
    fun (X : TSigT0 (Karr a b)) (X0 : TSigT0 a) =>
      {| tsigT0 := X.(tsigT0) X0.(tsigT0)
       ; tsigProper0 := X.(tsigProper0) X0.(tsigT0) X0.(tsigT0)
                         X0.(tsigProper0) X0.(tsigProper0) X0.(tsigProper0) |}.

  Definition tpi {a} {k : kind U0}
  : (TSigT k -> TSigT (Kstar a)) -> TSigT (Kstar U1) :=
    match a as a
          return (TSigT k -> TSigT (Kstar a)) -> TSigT (Kstar U1)
    with
    | U0 => fun X =>
      @mkTSigT1 (Kstar U1)
                (forall x : TSigT0 k, (X x).(tsigT0))
                (path_refl@{Usmall Usmall} (forall x : TSigT0 k, (X x).(tsigT0)))
    | U1 => fun X =>
      @mkTSigT1 (Kstar U1)
                (forall x : TSigT0 k, (X x).(tsigT1))
                (path_refl@{Usmall Usmall} (forall x : TSigT0 k, (X x).(tsigT1)))
    end.

  Variable TsymbolD : forall u (k : kind u),
      Tsymbol k -> TSigT k.

  Definition Kenv (ks : list (kind U0)) : Type@{Usmall} :=
    hlist@{Urefl Usmall} TSigT0 ks.

  Fixpoint Karrs (ks : list (kind U0)) (r : kind U0) : kind U0 :=
    match ks with
    | nil => r
    | k :: ks => Karr k (Karrs ks r)
    end.

  Fixpoint apply_Karrs {ks} {r} (f : TSigT0 (Karrs ks r)) (Ks : Kenv ks) : TSigT0 r :=
    match Ks in hlist _ ks
          return TSigT0 (Karrs ks r) -> TSigT0 r
    with
    | Hnil => fun f => f
    | Hcons x xs => fun f => @apply_Karrs _ r (tapp f x) xs
    end f.

  Definition Kuenv (ks : list Kuvar) : Type@{Usmall} :=
    hlist@{Urefl Usmall} (fun ku => TSigT0 (Karrs ku.(Tuctx) ku.(Tukind))) ks.

  Fixpoint typeD {kus ks u} {k : kind u} (t : type kus ks k)
  : Kuenv kus -> Kenv ks -> TSigT k.
  refine
    match t in @type _ _ u k
          return Kuenv kus -> Kenv ks -> TSigT k
    with
    | TArr a b => fun us vs => tarr (@typeD _ _ _ _ a us vs) (@typeD _ _ _ _ b us vs)
    | TApp f x => fun us vs => tapp (@typeD _ _ _ _ f us vs) (@typeD _ _ _ _ x us vs)
    | @TPi _ _ k0 _ t => fun us vs =>
      tpi (fun x : @TSigT U0 k0 => @typeD _ _ _ _ t us (Hcons _ vs))
    | TVar m   => fun _ vs => hlist_get m vs
    | TInj s   => fun _  _ => TsymbolD s
    | TUVar u xs => fun us vs =>
      apply_Karrs (hlist_get u us)
        (hlist_map (fun (k : kind U0) (t : type kus ks k) => @typeD _ _ U0 _ t us vs : TSigT0 k) xs)
    end.
  { exact x. }
  Defined.

  Record Tuvar kus (ks : list (kind U0)) : Type@{Urefl} :=
  { Uctx  : list (type kus ks (Kstar U0))
  ; Utype : type kus ks (Kstar U0)
  }.

  Definition Venv kus (ks : list (kind U0)) (tvs : list (type kus ks (Kstar U0)))
             (Kus : Kuenv kus) (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t : type kus ks (Kstar U0) =>
                           tsigT0 (@typeD _ _ U0 _ t Kus Ks)) tvs.


  Definition Uenv kus (ks : list (kind U0)) (tus : list (Tuvar kus ks))
             (Kus : Kuenv kus) (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t =>
                           @Venv kus ks t.(Uctx) Kus Ks ->
                           tsigT0 (@typeD _ _ U0 _ t.(Utype) Kus Ks)) tus.

  Unset Elimination Schemes.

  Fixpoint type_lift kus ks ks' ks'' u (k : kind u) (t : type kus (ks ++ ks'') k)
  : type kus (ks ++ ks' ++ ks'') k :=
    match t in @type _ _ u k
          return @type kus (ks ++ ks' ++ ks'') u k
    with
    | TArr a b => TArr (type_lift _ _ _ a) (type_lift _ _ _ b)
    | TApp f x => TApp (type_lift _ _ _ f) (type_lift _ _ _ x)
    | TVar v => TVar (member_lift _ _ _ v)
    | TPi t => TPi (type_lift (_::_) _ _ t)
    | TInj x => TInj x
    | TUVar u xs => TUVar u (hlist_map (@type_lift kus ks ks' ks'' U0) xs)
    end.

  Definition Umigrator_rec kus kus' : Type@{Urefl} :=
    hlist (fun tu => forall ks' (sub : hlist (@type kus' ks' U0) tu.(Tuctx)), type kus' ks' tu.(Tukind)) kus.

  Definition Umigrator kus kus' : Type@{Urefl} :=
    hlist (fun tu => @type kus' tu.(Tuctx) U0 tu.(Tukind)) kus.

  Definition tvars_id kus ks
  : hlist (@type kus ks U0) ks := hlist_map (fun k m => TVar m) (members ks).

  Fixpoint type_subst_rec kus kus' {ks ks'}
           (subu : Umigrator_rec kus kus')
           (sub : hlist (@type kus' ks' U0) ks)
           {u} {ku : kind u}
           (t : type kus ks ku) {struct t}
  : type kus' ks' ku :=
    match t in type _ _ Z
          return type kus' ks' Z
    with
    | TArr a b => TArr (type_subst_rec subu sub a) (type_subst_rec subu sub b)
    | TApp a b => TApp (type_subst_rec subu sub a) (type_subst_rec subu sub b)
    | TPi t =>
      let sub' := hlist_map (fun k t => @type_lift kus' nil (_::nil) ks' _ k t) sub in
      TPi (@type_subst_rec kus kus' (_::ks) _ subu (Hcons (TVar (@MZ _ _ _)) sub') _ _ t)
    | TVar v => hlist_get v sub
    | TInj x => TInj x
    | TUVar u xs =>
      (hlist_get u subu) _
                  (hlist_map (@type_subst_rec kus kus' ks ks' subu sub U0) xs)
    end.

  Definition Umigrator_rec_id kus : Umigrator_rec kus kus :=
    hlist_map (fun _ m _ xs => TUVar m xs) (members kus).

  Definition type_subst kus kus' {ks ks'}
           (subu : Umigrator kus kus')
           (sub : hlist (@type kus' ks' U0) ks)
           {u} {ku : kind u}
           (t : type kus ks ku)
  : type kus' ks' ku :=
    @type_subst_rec kus kus' ks ks'
                    (hlist_map (fun _ ty => fun ks' sub => @type_subst_rec kus' kus' _ ks' (Umigrator_rec_id _) sub _ _ ty) subu)
                    sub
                    u ku t.

  Definition Umigrator_id kus : Umigrator kus kus :=
    hlist_map (fun ku m => TUVar m (hlist_map (@TVar _ _) (members ku.(Tuctx)))) (members kus).

  (** TODO: This is generic *)
  Fixpoint member_post_weaken {T} (ls ls' : list T) {t} (m : member t ls)
  : member t (ls ++ ls') :=
    match m in member _ ls return member t (ls ++ ls') with
    | MZ _ _ => MZ _ _
    | MN _ m => MN _ (@member_post_weaken _ _ ls' _ m)
    end.

  Definition type_weaken kus kus' (ks' ks : list (kind U0)) (u : univ) (k : kind u) (t : type kus ks k)
  : type (kus ++ kus') (ks ++ ks') k :=
    type_subst
      (hlist_map@{Urefl Urefl Urefl}
                (fun k0 (x : member k0 kus) => TUVar (member_post_weaken kus' x) (tvars_id _ _))
                (members kus))
      (hlist_map@{Urefl Urefl Urefl}
                (fun (k0 : kind U0) (x : member k0 ks) => TVar (member_post_weaken ks' x))
                (members ks)) t.


  Variable Esymbol : forall u (t : type nil nil (Kstar u)), Type@{Urefl}.

  Inductive wtexpr kus (ks : list (kind U0))
            (tus : list (Tuvar kus ks))
            (tvs : list (type kus ks (Kstar U0)))
  : forall u, type kus ks (Kstar u) -> Type@{Urefl} :=
  | wtVar : forall t, member t tvs -> wtexpr tus tvs t
  | wtInj : forall u (t : type nil nil (Kstar u)),
      Esymbol t -> wtexpr tus tvs (type_weaken _ _ t)
  | wtApp : forall u d r,
      wtexpr tus tvs (TArr d r) ->
      wtexpr tus tvs d -> wtexpr tus tvs (u:=u) r
  | wtTApp : forall k u t,
      wtexpr tus tvs (@TPi kus ks k u t) ->
      forall w : type kus ks k,
        @wtexpr kus ks tus tvs u
                (@type_subst kus kus _ _ (Umigrator_id _)
                             (Hcons w (tvars_id kus _)) _ _ t)
  | wtAbs : forall u d (r : type kus ks (Kstar u)),
      wtexpr tus (d :: tvs) r -> wtexpr tus tvs (TArr d r)
  | wtUVar : forall tst, member tst tus ->
                    hlist (@wtexpr kus ks tus tvs U0) tst.(Uctx) ->
                    wtexpr tus tvs tst.(Utype).
  Set Elimination Schemes.
  Arguments wtVar {_ _ _ _} [_] _.
  Arguments wtInj {_ _ _ _} [_ _] _.
  Arguments wtApp {_ _ _ _} [_ _ _] _ _.
  Arguments wtAbs {_ _ _ _} [_ _ _] _.
  Arguments wtTApp {_ _ _ _} [_ _ _] _ _.
  Arguments wtUVar {_ _ _ _} [_] _ _.

  Definition tsigT_star (u : univ) : TSigT (Kstar u) -> Type@{Ularge} :=
    match u as u return TSigT (Kstar u) -> Type@{Ularge} with
    | U0 => fun x => x.(tsigT0)
    | U1 => fun x => x.(tsigT1)
    end.

  Definition tsigT (u : univ) (k : kind u) : TSigT k -> kindD k.
  destruct u.
  { refine (fun x => x.(tsigT1)). }
  { refine (fun x => x.(tsigT0)). }
  Defined.

  Arguments tsigT_star [_] _.
  Arguments tsigT [_ _] _.


  Definition exprApp kus {ks : list (kind U0)} {u0 : univ} {t0 : type kus ks (Kstar U0)}
             {t1 : type kus ks (Kstar u0)} {Tus : Kuenv kus} {Ts : Kenv ks}
  : tsigT_star (typeD (TArr t0 t1) Tus Ts) ->
    tsigT_star (typeD t0 Tus Ts) ->
    tsigT_star (typeD t1 Tus Ts).
  Proof using.
  { simpl in *. destruct u0; refine (fun x => x). }
  Defined.

  Definition exprAbs {kus} {ks : list (kind U0)}
             {u0 : univ} {t0 : type kus ks (Kstar U0)} {t1 : type kus ks (Kstar u0)}
             {Tus : Kuenv kus} {Ts : Kenv ks}
  : (tsigT (typeD t0 Tus Ts) -> tsigT_star (typeD t1 Tus Ts)) ->
    tsigT_star (typeD (TArr t0 t1) Tus Ts).
  Proof using.
    destruct u0; simpl; refine (fun f x => f x).
  Defined.

  Lemma exprInst {kus} {ks : list (kind U0)} {k : kind U0} {u0 : univ}
        {t0 : type kus (k :: ks) (Kstar u0)} {t : type kus ks k}
        {Tus : Kuenv kus} {Ts : Kenv ks}
  : tsigT_star (typeD (TPi t0) Tus Ts) ->
    forall x : TSigT0 k,
      tsigT_star (typeD t0 Tus (Hcons@{Urefl Usmall} x Ts)).
  Proof using.
    simpl in *. unfold tpi.
    destruct u0; exact (fun x => x).
  Defined.

  Variable EsymbolD : forall u t, @Esymbol u t -> tsigT_star (@typeD _ _ _ _ t Hnil Hnil).

  Lemma tmorphism_TSigT_refl:
    forall u (k : kind u) (t : TSigT k), tmorphism k (tsigT t) (tsigT t).
  Proof using.
    destruct k; simpl.
    { intros. eapply t.(tsigProper0); assumption. }
    { destruct n; intros; apply path_refl. }
  Defined.

  Lemma tmorphism_TSigT_trans:
    forall u (k : kind u) (a b c : TSigT k),
      tmorphism k (tsigT a) (tsigT b) ->
      tmorphism k (tsigT b) (tsigT c) ->
      tmorphism k (tsigT a) (tsigT c).
  Proof using.
    clear.
    induction k; simpl.
    { intros.
      eapply (@IHk2 (@mkTSigT0 k2 (tsigT0 a x) ltac:(eapply a.(tsigProper0); eauto))
                    (@mkTSigT0 k2 (tsigT0 b y) ltac:(eapply b.(tsigProper0); eauto))
                    (@mkTSigT0 k2 (tsigT0 c y) ltac:(eapply c.(tsigProper0); eauto))).
      { eapply X; eassumption. }
      { eapply X0; eassumption. } }
    { destruct n.
      { intros. eapply path_trans; eassumption. }
      { intros. eapply path_trans; eassumption. } }
  Defined.

  Lemma tmorphism_TSigT_sym
  : forall u (k : kind u) (a b : TSigT k),
      tmorphism k (tsigT a) (tsigT b) ->
      tmorphism k (tsigT b) (tsigT a).
  Proof.
    induction k; simpl.
    { intros. simpl in *.
      eapply (@IHk2 (@mkTSigT0 k2 (tsigT0 a y) ltac:(eapply a.(tsigProper0); eauto))
                    (@mkTSigT0 k2 (tsigT0 b x) ltac:(eapply b.(tsigProper0); eauto))).
      clear IHk2. eapply X; try eassumption.
      eapply (@IHk1 (@mkTSigT0 k1 x X0) (@mkTSigT0 k1 y X1)). eapply X2. }
    { destruct n.
      { intros; eapply path_sym; eassumption. }
      { intros; eapply path_sym; eassumption. } }
  Defined.

  Lemma tmorphism_tapp
    : forall d c F G X Y,
      tmorphism (Karr d c) (tsigT0 F) (tsigT0 G) ->
      tmorphism d (tsigT0 X) (tsigT0 Y) ->
      tmorphism c (tsigT0 (tapp F X)) (tsigT0 (tapp G Y)).
  Proof.
    unfold tapp. simpl; intros.
    eapply X0; try eapply (@tmorphism_TSigT_refl U0).
    assumption.
  Defined.

  Lemma tmorphism_apply_Karrs
    : forall {ks r} X Y,
      ForallT2_hlist (fun (k : kind U0) x y => tmorphism k (tsigT0 x) (tsigT0 y)) X Y ->
      forall F G,
        tmorphism (Karrs ks r) (tsigT0 F) (tsigT0 G) ->
        tmorphism r (tsigT0 (apply_Karrs F X)) (tsigT0 (apply_Karrs G Y)).
  Proof.
    induction 1; simpl; auto.
    { intros. eapply IHX0.
      eapply tmorphism_tapp; eassumption. }
  Defined.

  Lemma typeD_type_lift:
    forall kus (ks ks' ks'' : list (kind U0)) u (k0 : kind u) (t : type kus (ks' ++ ks) k0)
      (Tus : Kuenv kus) (Ts : Kenv ks) (Ts' : Kenv ks') (Ts'' : Kenv ks''),
      (forall tu (m : member tu kus),
            tmorphism (Karrs tu.(Tuctx) tu.(Tukind))
                      (tsigT0 (hlist_get m Tus)) (tsigT0 (hlist_get m Tus))) ->
      tmorphism k0
                (tsigT (typeD (type_lift ks' ks'' ks t) Tus (hlist_app Ts' (hlist_app Ts'' Ts))))
                (tsigT (typeD t Tus (hlist_app Ts' Ts))).
  Proof.
    refine
      (fix rec kus ks ks' ks'' u k0 (t : type kus (ks' ++ ks) k0) {struct t} :=
         match t as t in type _ _ k
               return forall (Tus : Kuenv kus) (Ts : Kenv ks) (Ts' : Kenv ks') (Ts'' : Kenv ks''),
              (forall tu (m : member tu kus),
                  tmorphism (Karrs tu.(Tuctx) tu.(Tukind))
                            (tsigT0 (hlist_get m Tus)) (tsigT0 (hlist_get m Tus))) ->
             tmorphism k
                       (tsigT (typeD (type_lift ks' ks'' ks t) Tus (hlist_app Ts' (hlist_app Ts'' Ts))))
                       (tsigT (typeD t Tus (hlist_app Ts' Ts)))
         with
         | TArr l r => fun Tus Ts Ts' Ts'' X =>
                        _ (@rec kus ks ks' ks'' U0 _ l Tus Ts Ts' Ts'' X)
                          (@rec kus ks ks' ks'' _ _ r Tus Ts Ts' Ts'' X)
         | TApp l r => fun Tus Ts Ts' Ts'' X =>
                        _ (@rec kus ks ks' ks'' U0 _ l Tus Ts Ts' Ts'' X)
                          (@rec kus ks ks' ks'' _ _ r Tus Ts Ts' Ts'' X)
         | @TPi _ _ k _ r => fun Tus Ts Ts' Ts'' X =>
                            _ (fun x => @rec kus ks (k :: ks') ks'' _ _ r Tus Ts (Hcons x Ts') Ts'' X)
         | TVar m => fun Tus Ts Ts' Ts'' _ => _
         | TInj i => fun Tus _ _ _ _ => _
         | TUVar u xs => fun Tus Ts Ts' Ts'' X => _
         end).
    { simpl type_lift. intros.
      destruct u0; simpl in *; eapply path_arrow; eauto. }
    { simpl type_lift. intros.
      simpl in *. eapply x. 3: eapply x0. all: eapply (@tmorphism_TSigT_refl U0). }
    { simpl. unfold tpi. destruct u0; simpl; eapply path_all. }
    { simpl.
      rewrite hlist_get_member_lift.
      eapply (@tmorphism_TSigT_refl U0). }
    { simpl. eapply (@tmorphism_TSigT_refl U0). }
    { simpl. rewrite hlist_map_hlist_map.
      eapply tmorphism_apply_Karrs; [ | solve [ eauto ] ].
      induction xs; simpl; constructor.
      { eapply (@rec _ _ _ _ U0). eauto. }
      { eapply IHxs. } }
  Defined.

  Definition Umigrator_rec_spec kus kus' (u : Umigrator_rec kus kus')
             (Tus : Kuenv kus) (Tus' : Kuenv kus')
  : Type@{Usmall} :=
    ForallT_hlist@{Urefl Urefl Usmall}
                 (fun ku m =>
                    forall ks (Ts : Kenv ks),
                    forall Cs : hlist@{Urefl Urefl} (@type kus' ks U0) ku.(Tuctx),
                      tmorphism ku.(Tukind)
                                (tsigT0 (typeD (hlist_get m u _ Cs) Tus' Ts))
                                (tsigT0 (apply_Karrs
                                           (hlist_get m Tus)
                                           (hlist_map (fun (k : kind U0) (t : type _ _ k) =>
                                                         (typeD t Tus' Ts) : TSigT0 k) Cs))))
                 (members kus).

  Definition Umigrator_spec kus kus' (u : Umigrator kus kus')
             (Tus : Kuenv kus) (Tus' : Kuenv kus')
  : Type@{Usmall} :=
    ForallT_hlist@{Urefl Urefl Usmall}
                 (fun ku m =>
                    forall Cs,
                      tmorphism ku.(Tukind)
                                (tsigT0 (typeD (hlist_get m u) Tus' Cs))
                                (tsigT0 (apply_Karrs (hlist_get m Tus) Cs)))
                 (members kus).

  Definition type_subst_rec_mor
  : forall kus' (ks' : list (kind U0))
      uu (Z : kind uu) (t0 : type kus' ks' Z)
      kus ks
      (Tus : Kuenv kus) (Tus' : Kuenv kus') (Ts : Kenv ks) (Ts' : Kenv ks')
      (Subu : Umigrator_rec kus' kus)
      (Sub : hlist (fun x => type kus ks x) ks'),
      ForallT_hlist@{Urefl Urefl Usmall} (fun (k : kind U0) m =>
                       tmorphism k (tsigT0 (typeD (hlist_get m Sub) Tus Ts))
                                 (tsigT0 (hlist_get m Ts'))) (members ks') ->
      Umigrator_rec_spec Subu Tus' Tus ->
      tmorphism Z
                (tsigT (typeD (type_subst_rec Subu Sub t0) Tus Ts))
                (tsigT (typeD t0 Tus' Ts')).
  Proof using.
    clear.
    intros kus' ks' uu Z t0 kus.
    induction t0 using type_rect.
    { intros.
      specialize (IHt0_1 ks Tus Tus' Ts Ts' Subu Sub X X0).
      specialize (IHt0_2 ks Tus Tus' Ts Ts' Subu Sub X X0).
      destruct u; simpl in *;
        apply (path_arrow IHt0_1 IHt0_2). }
    { intros.
      specialize (IHt0_1 ks Tus Tus' Ts Ts' Subu Sub X X0).
      specialize (IHt0_2 ks Tus Tus' Ts Ts' Subu Sub X X0).
      clear - IHt0_1 IHt0_2.
      simpl in *.
      eapply IHt0_1. all: try eapply (@tmorphism_TSigT_refl U0).
      eapply IHt0_2. all: try eapply (@tmorphism_TSigT_refl U0). }
    { intros.
      assert (forall x,
                 ForallT_hlist@{Urefl Urefl Usmall}
           (fun (k0 : kind U0) (m : member k0 (k :: ks')) =>
            tmorphism k0
              (tsigT0
                 (typeD
                    (hlist_get@{Urefl Urefl} m
                       (Hcons@{Urefl Urefl} (TVar (MZ k ks))
                          (hlist_map@{Urefl Urefl Urefl}
                             (fun (k1 : kind U0) (t : type kus ks k1) =>
                              type_lift nil (k :: nil) ks t) Sub))) Tus (Hcons@{Urefl Usmall} x Ts)))
              (tsigT0 (hlist_get@{Urefl Usmall} m (Hcons@{Urefl Usmall} x Ts'))))
           (members (k :: ks'))).
      { intros. constructor.
        { eapply (@tmorphism_TSigT_refl U0). }
        { eapply ForallT_hlist_map.
          revert X.
          eapply ForallT_hlist_ap.
          eapply ForallT_hlist_pure. simpl.
          intros. rewrite hlist_get_hlist_map.
          eapply (@tmorphism_TSigT_trans U0); [ | eapply X ].
          simpl.
          match goal with
          | |- tmorphism _ (tsigT0 (typeD (type_lift _ _ _ ?Y) _ _)) (tsigT0 (typeD ?X _ _)) =>
            change Y with X ; generalize X
          end. clear.
          intros.
          eapply (@typeD_type_lift kus ks nil (k :: nil) _ _ t0 Tus Ts Hnil (Hcons x Hnil)).
          intros. eapply (@tmorphism_TSigT_refl U0). } }
      specialize (fun x => IHt0 (k :: ks) Tus Tus' (Hcons x Ts) (Hcons x Ts') Subu
                             (Hcons@{Urefl Urefl} (TVar (MZ k ks))
                                   (hlist_map@{Urefl Urefl Urefl}
                                             (fun (k0 : kind U0) (t : type kus ks k0) =>
                                                type_lift nil (k :: nil) ks t) Sub))
                             (X1 x) X0).
      destruct u; simpl in *; eapply path_all; eapply IHt0. }
    { intros. simpl.
      eapply ForallT_hlist_get with (m0:=m) in X.
      rewrite hlist_get_members in X.
      eassumption. }
    { intros.
      eapply tmorphism_TSigT_refl. }
    { intros. simpl.
      unfold type_subst. simpl.
      generalize X1. intro Xsave.
      eapply ForallT_hlist_get with (m0:=m) in X1.
      eapply (@tmorphism_TSigT_trans U0).
      specialize (X1 _ Ts (hlist_map@{Urefl Urefl Urefl} (@type_subst_rec kus' kus ks' ks Subu Sub U0) xs)).
      simpl. rewrite hlist_get_members in X1. eapply X1.
      rewrite hlist_map_hlist_map.
      eapply tmorphism_apply_Karrs; [ | eapply (@tmorphism_TSigT_refl U0) ].
      clear - X X0 Xsave.
      eapply ForallT2_hlist_map_l.
      eapply ForallT2_hlist_map_r.
      eapply ForallT2_hlist_same.
      revert X.
      eapply ForallT_hlist_ap.
      eapply ForallT_hlist_pure.
      simpl. intros.
      eapply X; clear X; eauto. }
  Defined.

  Lemma Umigrator_rec_id_sound : forall kus Tus,
      Umigrator_rec_spec (Umigrator_rec_id kus) Tus Tus.
  Proof.
    clear. red. intros.
    eapply ForallT_hlist_pure.
    intros.
    unfold Umigrator_rec_id. rewrite hlist_get_hlist_map.
    simpl. rewrite hlist_get_members.
    eapply (@tmorphism_TSigT_refl U0).
  Defined.

  Lemma hlist_map_hlist_get_members {T} {F : T -> Type} ls (hs : hlist F ls)
    : hlist_map (fun x m => hlist_get m hs) (members _) = hs.
  Proof.
    induction hs; simpl; auto.
    f_equal. rewrite hlist_map_hlist_map. simpl. assumption.
  Defined.

  Lemma Umigrator_id_sound : forall kus Tus,
      Umigrator_spec (Umigrator_id kus) Tus Tus.
  Proof.
    clear. red. intros.
    eapply ForallT_hlist_pure.
    intros.
    unfold Umigrator_id. rewrite hlist_get_hlist_map.
    simpl. rewrite hlist_get_members.
    rewrite hlist_map_hlist_map.
    eapply (tmorphism_apply_Karrs); [ | eapply (@tmorphism_TSigT_refl U0) ].
    simpl.
    rewrite hlist_map_hlist_get_members.
    eapply ForallT2_hlist_same.
    eapply ForallT_hlist_pure.
    intros.
    eapply (@tmorphism_TSigT_refl U0).
  Defined.

  Definition type_subst_mor
  : forall kus' (ks' : list (kind U0))
      uu (Z : kind uu) (t0 : type kus' ks' Z)
      kus ks
      (Tus : Kuenv kus) (Tus' : Kuenv kus') (Ts : Kenv ks) (Ts' : Kenv ks')
      (Subu : Umigrator kus' kus)
      (Sub : hlist (fun x => type kus ks x) ks'),
      ForallT_hlist@{Urefl Urefl Usmall} (fun (k : kind U0) m =>
                       tmorphism k (tsigT0 (typeD (hlist_get m Sub) Tus Ts))
                                 (tsigT0 (hlist_get m Ts'))) (members ks') ->
      Umigrator_spec Subu Tus' Tus ->
      tmorphism Z (tsigT (typeD (type_subst Subu Sub t0) Tus Ts)) (tsigT (typeD t0 Tus' Ts')).
  Proof using.
    clear.
    intros. eapply type_subst_rec_mor; eauto.
    generalize X0.
    eapply ForallT_hlist_ap. eapply ForallT_hlist_pure.
    intros.
    rewrite hlist_get_hlist_map.
    pose ((hlist_map@{Urefl Urefl Usmall}
              (fun (k : kind U0) (t1 : type kus ks0 k) => typeD t1 Tus Ts0) Cs)).
    specialize (X1 h).
    eapply (@tmorphism_TSigT_trans U0); [ clear X1 | eapply X1 ].
    eapply (type_subst_rec_mor).
    { clear. eapply ForallT_hlist_pure.
      intros. unfold h. rewrite hlist_get_hlist_map. eapply (@tmorphism_TSigT_refl U0). }
    { eapply Umigrator_rec_id_sound. }
  Defined.

  Lemma hlist_get_tvars_id:
    forall kus (ks : list (kind U0)) (k0 : kind U0) (x : member k0 ks),
      hlist_get@{Urefl Urefl} x (tvars_id kus ks) = TVar x.
  Proof using.
    clear.
    unfold tvars_id.
    intros. rewrite hlist_get_hlist_map. rewrite hlist_get_members. reflexivity.
  Defined.

  Definition tmorphism_into u (X Y : _)
             (mor : tmorphism (Kstar u) (tsigT X) (tsigT Y))
    : tsigT_star X -> tsigT_star Y.
  Proof using .
    destruct u; simpl in *; eapply mor.
  Defined.

  Fixpoint wtexprD kus ks tus tvs u t (e : @wtexpr kus ks tus tvs u t)
  : forall Tus Ts, Uenv tus Tus Ts -> Venv tvs Tus Ts -> tsigT_star (@typeD _ _ _ _ t Tus Ts).
  refine
    match e in @wtexpr _ _ _ _ u t
          return forall Tus Ts, Uenv tus Tus Ts -> Venv tvs Tus Ts ->
                           tsigT_star (@typeD _ _ _ _ t Tus Ts)
    with
    | wtVar v => fun _ _ _ Vs => hlist_get v Vs
    | wtInj s => fun _ _ _ _ => _
    | wtAbs e => fun Tus Ts Us Vs =>
      (fun E => exprAbs (fun x => E (Hcons _ Vs)))
        (@wtexprD _ _ _ _ _ _ e Tus Ts Us)
    | wtApp f x => fun Tus Ts Us Vs =>
      exprApp (@wtexprD _ _ _ _ _ _ f Tus Ts Us Vs)
              (@wtexprD _ _ _ _ _ _ x Tus Ts Us Vs)
    | wtTApp f t => fun Tus Ts Us Vs =>
      let T := @typeD _ _ _ _ t Tus Ts in
      _ (@wtexprD _ _ _ _ _ _ f Tus Ts Us Vs)
    | wtUVar u xs => fun Tus Ts Us Vs =>
      (hlist_get u Us)
        (hlist_map
           (fun t e => @wtexprD _ _ _ _ _ t e Tus Ts Us Vs)
           xs)
    end.
  { (* inj *)
    generalize (EsymbolD s).
    unfold type_weaken.
    generalize (@type_subst_mor nil _ _ _ t0 _ ks k Hnil k0 Hnil).
    simpl members. simpl hlist_map.
    intro.
    eapply tmorphism_into.
    eapply tmorphism_TSigT_sym. eapply X.
    constructor. constructor. }
  { (* Pi *)
    simpl in *.
    unfold tpi. destruct u0; simpl; refine (fun f => _ (f T)).
    { eapply (@type_subst_mor _ _ _ _ t0 _ ks Tus Tus Ts (Hcons T Ts)
                              (Umigrator_id _) (Hcons@{Urefl Urefl} t (tvars_id _ ks))).
      econstructor.
      { eapply (@tmorphism_TSigT_refl U0). }
      { eapply ForallT_hlist_map.
        lazymatch goal with
        | |- ForallT_hlist ?X _ =>
          change (ForallT_hlist X (members ks))
        end.
        simpl.
        eapply ForallT_hlist_pure. intros.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). }
      eapply Umigrator_id_sound. }
    { eapply (@type_subst_mor _ _ _ _ t0 _ ks Tus Tus Ts (Hcons T Ts)
                              (Umigrator_id _) (Hcons@{Urefl Urefl} t (tvars_id _ ks))).
      constructor.
      { eapply (@tmorphism_TSigT_refl U0). }
      { apply ForallT_hlist_map.
        lazymatch goal with
        | |- ForallT_hlist ?X _ =>
          change (ForallT_hlist X (members ks))
        end.
        simpl.
        eapply ForallT_hlist_pure. intros.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). }
      eapply Umigrator_id_sound. } }
  { eapply x. }
  Defined.

End simple_dep_types.

(** NOTE: For this to be a proper denotation function, it must be completely
 ** transparent.
 **)

Print Opaque Dependencies hlist_eta.