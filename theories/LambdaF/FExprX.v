Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.
Require Import MirrorCore.LambdaF.Paths.

Set Primitive Projections.
Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.


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

(*** Start the actual reified language. *)

(* This is the universe of the reified language *)
Universe Urefl.
(* These are the universes of the denotation *)
Universe Uhuge Ularge Usmall Utiny.

(** Universes **)
Inductive univ : Type@{Urefl} :=
| U1 | U0.

Definition univ_eq_dec (a b : univ) : {a = b} + {a <> b} :=
  match a as a , b as b return {a = b} + {a <> b} with
  | U1 , U1 => left eq_refl
  | U0 , U0 => left eq_refl
  | U0 , U1 => right (fun pf : U0 = U1 => match pf in _ = X return match X with
                                                     | U1 => False
                                                     | _ => True
                                                     end
                            with
                            | eq_refl => I
                            end)
  | U1 , U0 => right (fun pf : U1 = U0 => match pf in _ = X return match X with
                                                     | U0 => False
                                                     | _ => True
                                                     end
                            with
                            | eq_refl => I
                            end)
  end.

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

Definition Karr_injl : forall a b c d, Karr a b = Karr c d -> a = c :=
  fun a _ _ _ pf =>
    match pf in _ = X return match X with
                             | Karr c d => a = c
                             | _ => False
                             end
    with
    | eq_refl => eq_refl
    end.

Definition Karr_injr : forall a b c d, Karr a b = Karr c d -> b = d :=
  fun a b _ _ pf =>
    match pf in _ = X return match X with
                             | Karr c d => b = d
                             | _ => False
                             end
    with
    | eq_refl => eq_refl
    end.

Definition Karr_not_Kstar : forall a b, (Karr a b <> Kstar U0)%type :=
  fun _ _ pf => match pf in _ = X return match X with
                                      | Kstar _ => False
                                      | _ => True
                                      end
             with
             | eq_refl => I
             end.

Fixpoint kind_eq_dec {u} (k1 : kind u) : forall k2, {k1 = k2} + {k1 <> k2} :=
  match k1 as k1 in kind u
        return forall k2 : kind u, {k1 = k2} + {k1 <> k2}
  with
  | Karr l r => fun k2 =>
    match k2 as k2 in kind u
          return (forall k2, {l = k2} + {l <> k2}) ->
                 (forall k2, {r = k2} + {r <> k2}) ->
                 {match u as u return kind u -> Prop with
                  | U0 => fun k2 => Karr l r = k2
                  | _ => fun _ => False
                  end k2} + {match u as u return kind u -> Prop with
                             | U0 => fun k2 => Karr l r <> k2
                             | _ => fun _ => True
                             end%type k2}
    with
    | Karr l' r' => fun recl recr =>
      match recl l' , recr r' with
      | left pf , left pf' => left match pf , pf' with
                                  | eq_refl , eq_refl => eq_refl
                                  end
      | left _ , right pf => right (fun pf' => pf (@Karr_injr _ _ _ _ pf'))
      | right pf , _ => right (fun pf' => pf (@Karr_injl _ _ _ _ pf'))
      end
    | Kstar u => fun _ _ =>
      right match u as u1
                  return
                  (match u1 as u2 return (kind u2 -> Prop) with
                   | U1 => fun _ : kind U1 => True
                   | U0 => fun k3 : kind U0 => (Karr l r <> k3)%type
                   end (Kstar u1))
            with
            | U1 => I
            | U0 => fun pf => @Karr_not_Kstar _ _ pf
            end
    end (fun x => kind_eq_dec l x)
        (fun x => kind_eq_dec r x)
  | Kstar u => fun k2 =>
    match k2 as k2 in kind u
          return {Kstar u = k2} + {Kstar u <> k2}
    with
    | Kstar u' => left eq_refl
    | Karr _ _ => right (fun pf => @Karr_not_Kstar _ _ (eq_sym pf))
    end
  end.

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
  | TInj : forall u (k : kind u), Tsymbol k -> type kus ks k
  | TUVar : forall ku, member ku kus -> hlist (@type kus ks U0) ku.(Tuctx) -> type kus ks ku.(Tukind).
  Arguments TInj [_ _ _ _] _.
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
    Hypothesis Hinj : forall u ks' k m, @P ks' u k (TInj m).
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
    Hypothesis Hinj : forall u ks' k m, @P ks' u k (TInj m).
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

  Definition tvars_id kus ks
  : hlist (@type kus ks U0) ks := hlist_map (fun k m => TVar m) (members ks).

  Fixpoint type_substV kus {ks ks'}
           (sub : hlist (@type kus ks' U0) ks)
           {u} {ku : kind u}
           (t : type kus ks ku) {struct t}
  : type kus ks' ku :=
    match t in type _ _ Z
          return type kus ks' Z
    with
    | TArr a b => TArr (type_substV sub a) (type_substV sub b)
    | TApp a b => TApp (type_substV sub a) (type_substV sub b)
    | TPi t =>
      let sub' := hlist_map (fun k t => @type_lift kus nil (_::nil) ks' _ k t) sub in
      TPi (@type_substV kus (_::ks) _ (Hcons (TVar (@MZ _ _ _)) sub') _ _ t)
    | TVar v => hlist_get v sub
    | TInj x => TInj x
    | TUVar u xs => TUVar u (hlist_map (@type_substV kus ks ks' sub U0) xs)
    end.

  Fixpoint type_substU {kus kus'} {ks}
           (subu : hlist (fun ku => @type kus' (Tuctx ku) U0 (Tukind ku)) kus)
           {u} {ku : kind u}
           (t : type kus ks ku) {struct t}
  : type kus' ks ku :=
    match t in type _ _ Z
          return type kus' ks Z
    with
    | TArr a b => TArr (type_substU subu a) (type_substU subu b)
    | TApp a b => TApp (type_substU subu a) (type_substU subu b)
    | TPi t => TPi (@type_substU kus kus' (_::ks) subu _ _ t)
    | TVar v => TVar v
    | TInj x => TInj x
    | TUVar u xs =>
      type_substV (hlist_map (@type_substU kus kus' ks subu U0) xs)
                  (hlist_get u subu)
    end.

  (** TODO: This is generic *)
  Fixpoint member_post_weaken {T} (ls ls' : list T) {t} (m : member t ls)
  : member t (ls ++ ls') :=
    match m in member _ ls return member t (ls ++ ls') with
    | MZ _ _ => MZ _ _
    | MN _ m => MN _ (@member_post_weaken _ _ ls' _ m)
    end.

  Definition type_weaken kus kus' (ks' ks : list (kind U0)) (u : univ) (k : kind u) (t : type kus ks k)
  : type (kus ++ kus') (ks ++ ks') k :=
    type_substU
      (hlist_map@{Urefl Urefl Urefl}
                (fun k0 (x : member k0 kus) => TUVar (member_post_weaken kus' x) (tvars_id _ _))
                (members kus))
      (type_substV
      (hlist_map@{Urefl Urefl Urefl}
                (fun (k0 : kind U0) (x : member k0 ks) => TVar (member_post_weaken ks' x))
                (members ks)) t).


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
                (@type_substV kus _ _ (Hcons w (tvars_id kus _)) _ _ t)
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
    { simpl. eapply (@tmorphism_TSigT_refl _). }
    { simpl. rewrite hlist_map_hlist_map.
      eapply tmorphism_apply_Karrs; [ | solve [ eauto ] ].
      induction xs; simpl; constructor.
      { eapply (@rec _ _ _ _ U0). eauto. }
      { eapply IHxs. } }
  Defined.

  Definition Umigrator_spec kus kus' (u : hlist (fun ku => type kus' (Tuctx ku) (Tukind ku)) kus)
             (Tus : Kuenv kus) (Tus' : Kuenv kus')
  : Type@{Usmall} :=
    ForallT_hlist@{Urefl Urefl Usmall}
                 (fun ku m =>
                    forall Cs,
                      tmorphism ku.(Tukind)
                                (tsigT0 (typeD (hlist_get m u) Tus' Cs))
                                (tsigT0 (apply_Karrs (hlist_get m Tus) Cs)))
                 (members kus).

  Lemma hlist_map_hlist_get_members {T} {F : T -> Type} ls (hs : hlist F ls)
    : hlist_map (fun x m => hlist_get m hs) (members _) = hs.
  Proof.
    induction hs; simpl; auto.
    f_equal. rewrite hlist_map_hlist_map. simpl. assumption.
  Defined.

  Lemma tmorphism_tarr:
    forall (kus kus' : list Kuvar) (ks ks' : list (kind U0)) (u : univ)
      (t0_1 : type kus ks (Kstar U0)) (t0_2 : type kus ks (Kstar u))
      (t0_1' : type kus' ks' (Kstar U0)) (t0_2' : type kus' ks' (Kstar u))
      (Tus : Kuenv kus) (Tus' : Kuenv kus') (Ts : Kenv ks) (Ts' : Kenv ks'),
      tmorphism (Kstar U0) (tsigT (typeD t0_1 Tus Ts)) (tsigT (typeD t0_1' Tus' Ts')) ->
      tmorphism (Kstar u) (tsigT (typeD t0_2 Tus Ts)) (tsigT (typeD t0_2' Tus' Ts')) ->
      tmorphism (Kstar u) (tsigT (typeD (TArr t0_1 t0_2) Tus Ts))
                (tsigT (typeD (TArr t0_1' t0_2') Tus' Ts')).
  Proof.
    destruct u; simpl; intros; eapply path_arrow; eauto.
  Defined.

  Lemma tmorphism_tpi:
    forall (kus kus' : list Kuvar) (ks ks' : list (kind U0)) (k : kind U0) (u : univ)
      (t0 : type kus (k :: ks) (Kstar u)) (t0' : type kus' (k :: ks') (Kstar u))
      (Tus : Kuenv kus) (Tus' : Kuenv kus')
      (Ts : Kenv ks) (Ts' : Kenv ks'),
      (forall t t' : TSigT0 k,
          tmorphism (u:=U0) k (tsigT0 t) (tsigT0 t') ->
          tmorphism (Kstar u)
                    (tsigT (typeD t0 Tus (Hcons@{Urefl Usmall} t Ts)))
                    (tsigT (typeD t0' Tus' (Hcons@{Urefl Usmall} t' Ts')))) ->
      tmorphism (Kstar U1) (tsigT (typeD (TPi t0) Tus Ts))
                (tsigT (typeD (TPi t0') Tus' Ts')).
  Proof using.
    clear.
    destruct u; simpl; intros.
    { eapply path_all; intros.
      eapply (X x x).
      eapply (@tmorphism_TSigT_refl U0). }
    { eapply path_all; intros.
      eapply (X x x).
      eapply (@tmorphism_TSigT_refl U0). }
  Defined.

  Lemma tmorphism_tpi_pointwise:
    forall (kus kus' : list Kuvar) (ks ks' : list (kind U0)) (k : kind U0) (u : univ)
      (t0 : type kus (k :: ks) (Kstar u)) (t0' : type kus' (k :: ks') (Kstar u))
      (Tus : Kuenv kus) (Tus' : Kuenv kus')
      (Ts : Kenv ks) (Ts' : Kenv ks'),
      (forall t : TSigT0 k,
          tmorphism (Kstar u)
                    (tsigT (typeD t0 Tus (Hcons@{Urefl Usmall} t Ts)))
                    (tsigT (typeD t0' Tus' (Hcons@{Urefl Usmall} t Ts')))) ->
      tmorphism (Kstar U1) (tsigT (typeD (TPi t0) Tus Ts))
                (tsigT (typeD (TPi t0') Tus' Ts')).
  Proof using.
    clear.
    destruct u; simpl; intros.
    { eapply path_all; intros.
      eapply (X x). }
    { eapply path_all; intros.
      eapply (X x). }
  Defined.

  Definition type_substV_mor
  : forall kus (ks' : list (kind U0))
      uu (Z : kind uu) (t0 : type kus ks' Z)
      ks
      (Tus : Kuenv kus) (Ts : Kenv ks) (Ts' : Kenv ks')
      (Sub : hlist (fun x => type kus ks x) ks'),
      ForallT_hlist@{Urefl Urefl Usmall} (fun (k : kind U0) m =>
                       tmorphism k (tsigT0 (typeD (hlist_get m Sub) Tus Ts))
                                 (tsigT0 (hlist_get m Ts'))) (members ks') ->
      tmorphism Z (tsigT (typeD (type_substV Sub t0) Tus Ts)) (tsigT (typeD t0 Tus Ts')).
  Proof using.
    clear.
    induction t0 using type_rect.
    { intros; eapply tmorphism_tarr.
      - eapply IHt0_1; eauto.
      - eapply IHt0_2; eauto. }
    { simpl. intros.
      eapply (@tmorphism_tapp k1 k2).
      eapply IHt0_1; eauto.
      eapply IHt0_2; eauto. }
    { intros.
      simpl type_substV.
      eapply tmorphism_tpi.
      intros.
      eapply IHt0. simpl.
      constructor.
      { simpl. assumption. }
      { apply ForallT_hlist_map.
        revert X.
        eapply ForallT_hlist_ap.
        eapply ForallT_hlist_pure.
        intros.
        simpl.
        rewrite hlist_get_hlist_map.
        eapply (@tmorphism_TSigT_trans U0); [ clear X | eapply X ].
        eapply (@typeD_type_lift kus ks nil (k :: nil) U0 _ (hlist_get f Sub) Tus Ts Hnil
                                 (Hcons@{Urefl Usmall} _ Hnil)).
        intros. eapply (@tmorphism_TSigT_refl U0). } }
    { simpl; intros.
      clear - X.
      generalize (ForallT_hlist_get X m).
      rewrite hlist_get_members. tauto. }
    { simpl. intros.
      eapply tmorphism_TSigT_refl. }
    { simpl. intros.
      eapply tmorphism_apply_Karrs.
      { rewrite hlist_map_hlist_map.
        apply ForallT2_hlist_map_l.
        apply ForallT2_hlist_map_r.
        apply ForallT2_hlist_same.
        revert X.
        eapply ForallT_hlist_ap.
        eapply ForallT_hlist_pure.
        intros. eapply X. eapply X0. }
      { apply (@tmorphism_TSigT_refl U0). } }
  Defined.

  Definition type_substU_mor
  : forall kus ks
      uu (Z : kind uu) (t0 : type kus ks Z)
      kus'
      (Tus : Kuenv kus) (Tus' : Kuenv kus') (Ts : Kenv ks)
      (Subu : hlist _ kus),
      Umigrator_spec Subu Tus Tus' ->
      tmorphism Z (tsigT (typeD (type_substU Subu t0) Tus' Ts)) (tsigT (typeD t0 Tus Ts)).
  Proof using.
    clear.
    induction t0 using type_rect.
    { intros; eapply tmorphism_tarr.
      - eapply IHt0_1; eauto.
      - eapply IHt0_2; eauto. }
    { simpl. intros.
      eapply (@tmorphism_tapp k1 k2).
      eapply IHt0_1; eauto.
      eapply IHt0_2; eauto. }
    { intros.
      simpl type_substU.
      eapply tmorphism_tpi_pointwise.
      intros. eapply IHt0 in X. eapply X. }
    { simpl; intros.
      eapply (@tmorphism_TSigT_refl U0). }
    { simpl. intros.
      eapply tmorphism_TSigT_refl. }
    { simpl. intros.
      eapply (@tmorphism_TSigT_trans U0).
      eapply type_substV_mor
        with (Ts := Ts)
             (Ts':=hlist_map (fun (x : kind U0) (y : type kus ks' x) => typeD (u:=U0) y Tus Ts : TSigT0 x ) xs).
      { eapply ForallT_hlist_pure. intros.
        do 2 rewrite hlist_get_hlist_map.
        eapply (@ForallT_hlist_get _ _ _ _ _ X _ f).
        eauto. }
      { simpl.
        red in X0.
        generalize (@ForallT_hlist_get _ _ _ _ _ X0 _ m); clear X0.
        rewrite hlist_get_members. refine (fun x => x _). } }
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
  Definition tmorphism_outof u (X Y : _)
             (mor : tmorphism (Kstar u) (tsigT X) (tsigT Y))
  : tsigT_star Y -> tsigT_star X.
  Proof using .
    eapply tmorphism_into. eapply tmorphism_TSigT_sym. assumption.
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
    unfold type_weaken. simpl.
    eapply tmorphism_outof.
    generalize (@type_substU_mor _ _ _ _ (type_substV Hnil t0) _ Hnil k k0 Hnil).
    intros.
    eapply tmorphism_TSigT_trans. eapply X. constructor.
    eapply (@type_substV_mor _ _ _ _ t0 _ Hnil _ _ Hnil). constructor. }
  { (* Pi *)
    simpl in *.
    unfold tpi. destruct u0; simpl; refine (fun f => _ (f T)).
    { eapply (@tmorphism_outof U1).
      apply (@type_substV_mor kus _ _ _ t0 _ Tus Ts
                                   (Hcons@{Urefl Usmall} T Ts)
                                   (Hcons t (tvars_id kus ks))).
      simpl. constructor.
      { simpl. eapply (@tmorphism_TSigT_refl U0). }
      { eapply ForallT_hlist_map.
        eapply ForallT_hlist_pure. simpl.
        intros.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). } }
    { eapply (@tmorphism_outof U0).
      apply (@type_substV_mor kus _ _ _ t0 _ Tus Ts
                                   (Hcons@{Urefl Usmall} T Ts)
                                   (Hcons t (tvars_id kus ks))).
      simpl. constructor.
      { simpl. eapply (@tmorphism_TSigT_refl U0). }
      { eapply ForallT_hlist_map.
        eapply ForallT_hlist_pure. simpl.
        intros.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). } } }
  { eapply x. }
  Defined.

  (** This is unification **)

  Definition Umigrator (m : Type@{Urefl} -> Type@{Urefl}) tus tus' : Type@{Urefl} :=
    hlist (fun x => m (type tus' (Tuctx x) (Tukind x))) tus.

  (** TODO: Using the concrete type `Umigrator` is problematic here. **)
  Fixpoint inst_type {tus tus'} (inst : Umigrator (fun x => x) tus tus')
           {ts} {u} {k : kind u} (t : type tus ts k)
  : type tus' ts k :=
    match t in @type _ _ _ k
          return type tus' ts k
    with
    | TArr a b => TArr (inst_type inst a) (inst_type inst b)
    | TApp a b => TApp (inst_type inst a) (inst_type inst b)
    | TPi a => TPi (inst_type inst a)
    | TVar x => TVar x
    | TInj x => TInj x
    | TUVar u vs => type_substV (hlist_map (@inst_type _ _ inst _ _) vs) (hlist_get u inst)
    end.

  Section with_applicative.
    Variable m : Type@{Urefl} -> Type@{Urefl}.
    Context {Applicative_m : ExtLib.Structures.Applicative.Applicative m}.

    Section hlist_traverse.
      Variable T : Type.
      Variable F : T -> Type.
      Variable G : T -> Type.
      Variable ff : forall t : T, F t -> m (G t).

      Fixpoint hlist_traverse {ls} (h : hlist F ls) : m (hlist G ls) :=
        match h in hlist _ ls return m (hlist G ls) with
        | Hnil => pure (@Hnil _ _)
        | Hcons h hs => ap (T:=m) (ap (T:=m) (pure (T:=m) (@Hcons _ _ _ _)) (ff h)) (hlist_traverse hs)
        end.
    End hlist_traverse.

  Fixpoint inst_typeA {tus tus'} (inst : forall t, member t tus -> m (type tus' (Tuctx t) (Tukind t)))
           {ts} {u} {k : kind u} (t : type tus ts k)
  : m (type tus' ts k) :=
    match t in @type _ _ _ k
          return m (type tus' ts k)
    with
    | TArr a b => ap (ap (T:=m) (pure (@TArr _ _ _)) (inst_typeA inst a)) (inst_typeA inst b)
    | TApp a b => ap (ap (T:=m) (pure (@TApp _ _ _ _)) (inst_typeA inst a)) (inst_typeA inst b)
    | TPi a => ap (T:=m) (pure (@TPi _ _ _ _)) (inst_typeA inst a)
    | TVar x => pure (TVar x)
    | TInj x => pure (TInj x)
    | TUVar u vs => ap (ap (T:=m)
                          (pure (fun h t => @type_substV _ _ _ h _ _ t))
                          (@hlist_traverse _ _ _ (@inst_typeA _ _ inst _ _) _ vs))
                      (inst _ u)
    end.

  End with_applicative.

  Definition TUnifiable {tus tus'} (inst : Umigrator id tus tus')
             {ts} {u} {k : kind u} (t t' : type tus ts k) : Prop :=
    inst_type inst t = inst_type inst t'.

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

  Inductive Inst (kus : list Kuvar) : list Kuvar -> Type@{Urefl} :=
  | Done   : Inst kus kus
  | SetOne : forall Z ku (m : member ku kus),
      type (del_member m) (Tuctx ku) (Tukind ku) ->
      Inst (del_member m) Z ->
      Inst kus Z.

  Theorem Inst_length_leq : forall a b (i : Inst a b), length b <= length a.
  Proof using.
    clear.
    induction 1.
    { reflexivity. }
    { etransitivity. eapply IHi.
      apply PeanoNat.Nat.lt_le_incl.
      apply lenth_del_member. }
  Defined. (** too many dependencies *)

  Arguments Done {_}.
  Arguments SetOne {_ _} [_] _ _ _.

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

  End member_heq.

  Instance Applicative_id : Applicative id :=
  { pure := fun _ x => x
  ; ap := fun _ _ f x => f x
  }.

  Definition to_type {ku kus} (m : member ku kus + (type kus (Tuctx ku) (Tukind ku)))
  : type kus (Tuctx ku) (Tukind ku) :=
    match m with
    | inl m => TUVar m (tvars_id _ _)
    | inr z => z
    end.

  Fixpoint lookupInst {kus kus'} (i : Inst kus kus') {ku} (m : member ku kus) {struct i}
  : member ku kus' + (type kus' (Tuctx ku) (Tukind ku)).
  refine
    match i in Inst _ kus'
          return member ku kus' + type kus' (Tuctx ku) (Tukind ku)
    with
    | @Done _ => inl m
    | @SetOne _ kus' _ m' t i' =>
      match member_heq m' m with
      | inl z => @lookupInst _ _ i' _ z
      | inr pf => inr match pf in _ = X return type kus' (Tuctx X) (Tukind X) with
                     | eq_refl => inst_typeA (m:=id)
                                            (fun z m => to_type (@lookupInst _ _ i' _ m)) t
                     end
      end
    end.
  Defined.

  Local Existing Instance Option.Applicative_option.

  Fixpoint setInst {kus kus'} (i : Inst kus kus')
  : forall {ku} (m : member ku kus') (t : type kus' (Tuctx ku) (Tukind ku)),
      option (Inst kus (del_member m)) :=
    match i in Inst _ kus'
          return forall {ku} (m : member ku kus') (t : type kus' (Tuctx ku) (Tukind ku)),
        option (Inst kus (del_member m))
    with
    | Done => fun _ m t =>
      ap (pure (fun x => SetOne m x Done)) (inst_typeA (fun _ m' => match member_heq m m' with
                                                              | inl z => pure (TUVar z (tvars_id _ _))
                                                              | inr _ => None
                                                              end) t)
    | SetOne u t' i' => fun _ m t => ap (pure (SetOne u t')) (@setInst _ _ i' _ _ t)
    end.

  Arguments lookupInst [_ _] _ [_] _.

  Variable Tsymbol_eq_dec : forall u (k : kind u) (t1 t2 : Tsymbol k), {t1 = t2} + {t1 <> t2}.
  Variable Esymbol_eq_dec : forall u t (e1 e2 : @Esymbol u t), {e1 = e2} + {e1 <> e2}.

  Arguments MZ {_ _ _}.

  Definition inj_Karr (l l' r r' : kind U0) (pf : Karr l r = Karr l' r')
    : l = l' /\ r = r' :=
    match pf in _ = X
          return l = match X with
                     | Karr l' _ => l'
                     | _ => Kstar U0
                     end /\ r = match X with
                               | Karr _ r' => r'
                               | _ => Kstar U0
                               end
    with
    | eq_refl => conj eq_refl eq_refl
    end.

  Fixpoint kind_heq {u1 u2} (k1 : kind u1) (k2 : kind u2)
  : option { pf : u2 = u1 & k1 = match pf with
                                 | eq_refl => k2
                                 end }.
  refine
    match k1 as k1 in kind u1 , k2 as k2 in kind u2
          return option { pf : u2 = u1 & k1 = match pf with
                                 | eq_refl => k2
                                 end }
    with
    | Kstar U0 , Kstar U0 => Some (@existT _ _ eq_refl eq_refl)
    | Kstar U1 , Kstar U1 => Some (@existT _ _ eq_refl eq_refl)
    | Karr a b , Karr a' b' =>
      match kind_eq_dec a a' , kind_eq_dec b b' with
      | left pf , left pf' => Some (@existT _ _ eq_refl match pf , pf' with
                                                       | eq_refl , eq_refl => eq_refl
                                                       end)
      | _ , _ => None
      end
    | _ , _ => None
    end.
  Defined.

  Fixpoint type_check_eq {kus ks u k}
           (t1 : @type kus ks u k)
  : forall k', @type kus ks u k' -> option (k = k').
  refine
    match t1 in @type _ _ u k
          return forall k' : kind u, @type kus ks u k' -> option (k = k')
    with
    | TArr l r => fun _ t2 =>
      match t2 in @type _ _ u k
            return (forall k' : kind U0, type kus ks k' -> option (Kstar U0 = k')) ->
                   (forall k' : kind u, type kus ks k' -> option (Kstar u = k')) -> _
      with
      | TArr l' r' => fun recl recr =>
        match @recl _ l' , @recr _ r' with
        | Some pfl , Some pfr => Some pfr
        | _ , _ => None
        end
      | _ => fun _ _ => None
      end (@type_check_eq _ _ _ _ l) (@type_check_eq _ _ _ _ r)
    | @TApp _ _ kd kc l r => fun _ t2 =>
      match t2 in @type _ _ u k
            return (forall k' : kind U0, type kus ks k' -> option (Karr kd _ = k')) ->
                   (forall k' : kind _, type kus ks k' -> option (_ = k')) ->
                   option (match u as u return kind u -> Prop with
                           | U0 => fun k => kc = k
                           | U1 => fun _ => False
                           end k)
      with
      | TApp l' r' => fun recl recr =>
        match @recl _ l' , @recr _ r' with
        | Some pfl , Some pfr => Some (proj2 (inj_Karr pfl))
        | _ , _ => None
        end
      | _ => fun _ _ => None
      end (@type_check_eq _ _ _ _ l) (@type_check_eq _ _ _ _ r)
    | @TPi _ _ k u t => fun _ t2 =>
      match t2 in (@type _ _ u1 k1)
         return
           ((forall x : kind u, type kus (k :: ks) x -> option (Kstar u = x)) ->
            option (Kstar u1 = k1))
      with
      | @TPi _ _ k' u' t' => fun rect =>
        match univ_eq_dec u' u , kind_eq_dec k' k with
        | left pfu , left pfk =>
          match @rect _ match pfu in _ = U
                                    , pfk in _ = K
                                      return @type kus (K :: ks) U _
                                with
                                | eq_refl , eq_refl => t'
                                end
          with
          | Some pf => Some eq_refl
          | _ => None
          end
        | _ , _ => None
        end
      | _ => fun _ => None
      end (@type_check_eq _ _ _ _ t)
    | TVar m => fun _ t' =>
      match t' in @type _ _ u k return option (match u as u return kind u -> Prop with
                                               | U0 => fun k => _ = k
                                               | _ => fun _ => False
                                               end k) with
      | TVar m' =>
        match member_heq m m' with
        | inl _ => None
        | inr pf => Some pf
        end
      | _ => None
      end
    | @TInj _ _ _ k s => fun _ t' =>
      match t' in @type _ _ u k' return forall k, Tsymbol k -> option (k = k') with
      | @TInj _ _ _ k' s' => fun k s =>
        match kind_eq_dec k k' with
        | left pf => match pf in _ = X return Tsymbol k -> Tsymbol X -> option (k = _) with
                    | eq_refl => fun s s' => match Tsymbol_eq_dec s s' with
                                         | left pf => Some eq_refl
                                         | right _ => None
                                         end
                    end s s'
        | right _ => None
        end
      | _ => fun _ _ => None
      end k s
    | @TUVar _ _ ku u xs => fun _ t' =>
      match t' in @type _ _ u k' return option (match u with
                                                | U0 => fun k' => Tukind _ = k'
                                                | _ => fun _ => False
                                                end k') with
      | TUVar u' xs' =>
        match member_heq u u' with
        | inl _ => None
        | inr pf =>
          match pf in _ = X
                return hlist (@type _ _ _) (Tuctx X) ->
                       option (Tukind ku = Tukind X)
          with
          | eq_refl => fun xs' =>
            match hlist_foldM (m:=option)
                              (A:=fun _ => option (Tukind ku = Tukind _))
                              (fun _ o _ acc => match o with
                                             | None => None
                                             | Some _ => Some acc
                                             end)
                              (hlist_zipWith (fun _ t1 t2 => @type_check_eq _ _ _ _ t1 _ t2) xs xs')
                              (Some eq_refl) with
            | Some pf => Some eq_refl
            | None => None
            end
          end xs'
        end
      | _ => None
      end
    end.
  Defined.

  (** TODO: `option` could be generalized to `Applicative` with a zero. *)
  Fixpoint pattern_type {tus} {tvs tvs'} {u} {k : kind u} (t : type tus tvs k)
           (hs : hlist (@type tus tvs U0) tvs') (** TODO: This could be more efficient *)
  : option (type tus tvs' k).
  refine (
      match match u as u return forall k : kind u, type tus tvs k -> option (type tus tvs' k) with
            | U0 => fun k t => @DepUtil.find_in_hlist _ _ _ (type_check_eq t) _ _ hs (fun v => TVar v)
            | U1 => fun _ _ => None
            end k t
      with
      | Some v => Some v
      | None =>
        match t in @type _ _ u k
              return option (type tus tvs' k)
        with
        | TArr l r =>
          match @pattern_type _ _ _ _ _ l hs
                , @pattern_type _ _ _ _ _ r hs
          with
          | Some l' , Some r' => Some (TArr l' r')
          | _ , _ => None
          end
        | TApp l r =>
          match @pattern_type _ _ _ _ _ l hs
                , @pattern_type _ _ _ _ _ r hs
          with
          | Some l' , Some r' => Some (TApp l' r')
          | _ , _ => None
          end
        | @TPi _ _ k u t =>
          let ff (t : kind U0) (X : type tus tvs t) : type tus (_ :: tvs) t :=
              @type_lift _ nil (k :: nil) tvs _ _ X
          in
          match @pattern_type _ _ _ _ _ t (Hcons (TVar MZ) (hlist_map ff hs)) with
          | Some t' => Some (@TPi _ _ k u t')
          | _ => None
          end
        | TInj s => Some (TInj s)
        | TVar _ => None
        | TUVar u vs =>
          match
            hlist_traverse _ (fun (k : kind U0) (t : @type tus tvs U0 k) => @pattern_type _ _ _ _ _ t hs) vs
          with
          | None => None
          | Some vs' => Some (TUVar u vs')
          end
        end
      end).
  Defined.

  Fixpoint appInst {a b c} (i : Inst a b) : Inst b c -> Inst a c :=
    match i in Inst _ b return Inst b c -> Inst a c with
    | Done => fun x => x
    | SetOne m t i' => fun x => SetOne m t (appInst i' x)
    end.

  (** TODO: This is a hack, I should avoid using the concrete type Umigrator. *)
  Definition Inst_to_Umigrator {tus tus'} (i : Inst tus tus') : Umigrator id tus tus' :=
    hlist_map (fun t m => to_type (lookupInst i m)) (members _).

  Section tunify.
    Context {tus : list Kuvar}.

    Variable rec_smaller
    : forall tus' (pf : length tus' < length tus)
        {ts} {u} {k : kind u} (t1 : type tus' ts k)
        (t2 : type tus' ts k) {tus''} (s : Inst tus' tus''),
      option { tus''' : _ & Inst tus' tus''' }.

    Theorem lookupInst_success_smaller : forall {tus tus'} (i : Inst tus tus')
                                           {ku} (m : member ku tus) t,
        lookupInst i m = inr t ->
        length tus' < length tus.
    Proof.
      clear.
      induction i; simpl.
      { inversion 1. }
      { intros.
        destruct (member_heq m m0).
        { eapply IHi in H.
          etransitivity. eapply H. eapply lenth_del_member. }
        { eapply PeanoNat.Nat.le_lt_trans.
          eapply (Inst_length_leq i).
          eapply lenth_del_member. } }
    Defined.

    Definition trySet {ts} {ku : Kuvar} (u : member ku tus)
               (xs : hlist (@type tus ts U0) (Tuctx ku))
               (t2 : type tus ts (Tukind ku)) {tus'} (i : Inst tus tus')
      : option { tus'' : _ & Inst tus tus'' }.
      refine
        (match lookupInst i u as z return lookupInst i u = z -> _ with
        | inl m => fun _ =>
          match @pattern_type _ _ _ _ _ t2 xs with
          | Some t2' =>
            match @setInst _ _ i _ m (type_substU (Inst_to_Umigrator i) t2') with
            | Some i' => Some (@existT _ _ _ i')
            | None => None
            end
          | None => None
          end
        | inr t => fun pf =>
          let um := Inst_to_Umigrator i in
          let t' := type_substU um t2 in
          let ts := type_substV (hlist_map (@type_substU _ _ _ um _) xs) t in
          match @rec_smaller _ (lookupInst_success_smaller _ _ pf) _ _ _ ts t' _ Done with
          | Some (existT _ tuss i') => Some (@existT _ _ tuss (appInst i i'))
          | None => None
          end
        end eq_refl).
    Defined.

  Fixpoint tunify_rec {ts} {u} {k : kind u} (t1 : type tus ts k) {struct t1}
  : forall (t2 : type tus ts k) {tus'} (s : Inst tus tus'),
      option { tus'' : _ & Inst tus tus'' }.
  refine
    match t1 in @type _ _ u k
          return forall (t2 : @type tus ts u k) {tus'} (s : Inst tus tus'),
            option { tus'' : _ & Inst tus tus'' }
    with
    | @TArr _ _ u l r => fun b : @type tus ts u (Kstar u) =>
      match b in @type _ _ u' k'
            return
            @type tus ts u' k' ->
            (type tus ts (Kstar U0) -> forall {tus'} (s : Inst tus tus'),
                        option { tus'' : _ & Inst tus tus'' }) ->
            (type tus ts k' -> forall {tus'} (s : Inst tus tus'),
                        option { tus'' : _ & Inst tus tus'' }) ->
            forall {tus'} (s : Inst tus tus'),
              option { tus'' : _ & Inst tus tus'' }
      with
      | TArr l' r' => fun _ recl recr tus' s =>
        match recl l' tus' s with
        | Some (existT _ tus'' i') => recr r' tus'' i'
        | None => None
        end
      | TUVar u xs => fun X _ _ tus' s => trySet u xs X s
      | _ => fun _ _ _ _ _ => None
      end (TArr l r)
          (fun x : @type tus ts U0 (Kstar U0) => @tunify_rec _ U0 _ l x)
          (fun x : @type tus ts u (Kstar u) => @tunify_rec _ _ _ r x)
    | @TApp _ _ k1 k2 l r => fun b : @type tus ts _ k2 =>
      match b in @type _ _ u' k'
            return
            @type tus ts u' k' ->
            (match u' as u' return kind u' -> Type with
             | U0 => fun k' => type tus ts (Karr k1 k') -> forall {tus'} (s : Inst tus tus'),
                        option { tus'' : _ & Inst tus tus'' }
             | _ => fun _ => unit
             end k') ->
            (type tus ts k1 -> forall {tus'} (s : Inst tus tus'),
                        option { tus'' : _ & Inst tus tus'' }) ->
            forall {tus'} (s : Inst tus tus'),
              option { tus'' : _ & Inst tus tus'' }
      with
      | @TApp _ _ k1' k2' l' r' => fun _ =>
        match kind_eq_dec k1' k1 with
        | left pf =>
          match pf in _ = X
                return (type tus ts (Karr X k2') -> forall {tus'} (s : Inst tus tus'),
                           option { tus'' : _ & Inst tus tus'' }) ->
                       (type tus ts X -> forall {tus'} (s : Inst tus tus'),
                           option { tus'' : _ & Inst tus tus'' }) ->
                       forall {tus'} (s : Inst tus tus'),
                         option { tus'' : _ & Inst tus tus'' }
          with
          | eq_refl => fun recl recr tus' s =>
                        match recl l' tus' s with
                        | Some (existT _ tus'' i') => recr r' tus'' i'
                        | None => None
                        end
          end
        | right _ => fun _ _ _ _ => None
        end
      | TUVar u xs => fun X _ _ tus' s => trySet u xs X s
      | _ => fun _ _ _ _ _ => None
      end (TApp l r)
          (fun x => @tunify_rec _ _ _ l x)
          (fun x => @tunify_rec _ _ _ r x)
    | @TPi _ _ k u t => fun b : @type tus ts U1 (Kstar U1) =>
      match b in @type _ _ u' k'
            return @type tus ts u' k' ->
                   (type tus (k :: ts) (Kstar u) -> forall {tus'} (s : Inst tus tus'),
                       option { tus'' : _ & Inst tus tus'' }) ->
                   forall {tus'} (s : Inst tus tus'),
                     option { tus'' : _ & Inst tus tus'' }
      with
      | @TPi _ _ k' u' t' => fun _ =>
        match kind_eq_dec k' k , univ_eq_dec u' u with
        | left pf , left pf' =>
          match pf , pf' with
          | eq_refl , eq_refl => fun rec tus i =>
            rec t' tus i
          end
        | _ , _ => fun _ _ _ => None
        end
      | TUVar u xs => fun X _ _ s => trySet u xs X s
      | _ => fun _ _ _ _ => None
      end (TPi t) (fun x => @tunify_rec _ _ _ t x)
    | @TVar _ _ k v => fun b : @type tus ts U0 k =>
      match b in @type _ _ u' k'
            return @type tus ts u' k' -> _
      with
      | TVar v' => fun _ =>
        match member_heq v v' with
        | inr pf => fun tus i => Some (@existT _ _ tus i)
        | inl _ => fun _ _ => None
        end
      | TUVar u xs => fun X tus i => trySet u xs X i
      | _ => fun _ _ _ => None
      end (TVar v)
    | @TInj _ _ u k s => fun b : @type tus ts _ k =>
      match b in @type _ _ u' k'
            return Tsymbol k' -> _
      with
      | TInj s' => fun s =>
        match Tsymbol_eq_dec s s' with
        | left _ => fun tus i => Some (@existT _ _ tus i)
        | right _ => fun _ _ => None
        end
      | TUVar u xs => fun s tus i => trySet u xs (TInj s) i
      | _ => fun _ _ _ => None
      end s
    | @TUVar _ _ k u xs => fun b : @type tus ts U0 (Tukind k) =>
      match b in @type _ _ u' k' return type tus ts k' -> _ with
      | @TUVar _ _ k' u' xs' => fun a =>
        match member_heq u u' with
        | inr pf => match pf in _ = k'
                         return hlist@{Urefl Urefl} (type tus ts (u:=U0)) (Tuctx k') ->
                                _
                   with
                   | eq_refl => fun xs' tus' i =>
                     hlist_foldM (m:=option)
                                 (F:=fun _ => forall tus', Inst tus tus' -> option { tus'' : _ & Inst tus tus''})
                                 (A:=fun _ => { tus'' : _ & Inst tus tus'' })
                                 (fun _ v _ acc => v _ (projT2 acc))
                                 (hlist_zipWith (fun t => @tunify_rec _ _ _) xs xs')
                                 (existT _ _ i)
                   end xs'
        | inl _ => fun tus' i =>
          match trySet u xs b i with
          | Some z => Some z
          | None => trySet u' xs' a i
          end
        end
      | X => fun _ tus i => trySet u xs X i
      end (TUVar u xs)
    end.
  Defined.

  End tunify.

  Require Import ExtLib.Recur.Measure.

  Definition tunify {tus}
  : forall {ts} {u} {k : kind u} (t1 : type tus ts k) (t2 : type tus ts k)
      {tus'} (s : Inst tus tus'),
      option { tus'' : _ & Inst tus tus'' }.
  refine
    (@Fix _ (mlt (@length _)) (well_founded_mlt _)
          (fun tus =>
             forall {ts} {u} {k : kind u} (t1 : type tus ts k) (t2 : type tus ts k)
               {tus'} (s : Inst tus tus'),
               option { tus'' : _ & Inst tus tus'' })
          (fun tus rec ts u k t1 t2 tus' s =>
             @tunify_rec tus rec ts u k t1 t2 tus' s)
          tus).
  Defined.

  Arguments MN {_ _ _ _} _.

  (** DEMO **)
  Definition t1 {tus} : type tus (Kstar U0 :: Kstar U0 :: nil) (Kstar U0) :=
    TVar MZ.

  Definition t2 {tus} : type tus (Kstar U0 :: Kstar U0 :: nil) (Kstar U0) :=
    TVar (MN MZ).

  Definition tu : type ({| Tuctx := Kstar U0 :: nil ; Tukind := Kstar U0 |} :: nil)
                       (Kstar U0 :: Kstar U0 :: nil) (Kstar U0) :=
    TUVar (@MZ _ {| Tuctx := Kstar U0 :: nil ; Tukind := Kstar U0 |} _)
          (Hcons@{Urefl Urefl} (TVar MZ) Hnil).

  Eval compute in tunify tu (TArr (TVar MZ) (TVar MZ)) Done.

  Example demo :
    let a := tu in
    let b := TArr (TVar MZ) (TVar MZ) in
    match tunify a b Done with
    | None => False
    | Some (existT _ _ i) =>
      TUnifiable (Inst_to_Umigrator i) a b
    end.
  Proof. compute. reflexivity. Defined.

End simple_dep_types.

(** NOTE: For this to be a proper denotation function, it must be completely
 ** transparent.
 **)

Print Opaque Dependencies hlist_eta.