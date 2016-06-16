Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.

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

(* This is the universe of the reified language *)
Universe Urefl.
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

Polymorphic Record KSigT'@{a b} : Type@{a} := mkKSigT'
{ ksigT : Type@{b}
}.

Definition KSigT (u : univ) : Type@{Uhuge} :=
  match u as u return Type@{Uhuge} with
  | U0 => KSigT'@{Ularge Usmall}
  | U1 => KSigT'@{Uhuge Ularge}
  end.

Fixpoint kindD {u} (k : kind u) : KSigT u :=
  match k in kind u return KSigT u with
  | Karr a b =>
    let a := kindD a in
    let b := kindD b in
    @mkKSigT'
             (a.(ksigT) -> b.(ksigT))
  | Kstar U0 =>
    @mkKSigT' Type@{Utiny}
  | Kstar U1 =>
    @mkKSigT' Type@{Usmall}
  end.

(*
Definition karr {a b : univ} : kind a -> kind b -> Type@{Uhuge} :=
  match a as a , b as b
        return kind a -> kind b -> Type@{Uhuge}
  with
  | U0 , U0 => fun k1 k2 => kindD k1 -> kindD k2
  | U1 , U0 => fun k1 k2 => kindD k1 -> kindD k2
  | U0 , U1 => fun k1 k2 => kindD k1 -> kindD k2
  | U1 , U1 => fun k1 k2 => kindD k1 -> kindD k2
  end.
*)

Section simple_dep_types.
  Variable Tsymbol : forall u, kind u -> Type@{Urefl}.

  Inductive type (ks : list (kind U0)) : forall u, kind u -> Type@{Urefl} :=
  | TArr : forall u, type ks (Kstar U0) -> type ks (Kstar u) -> type ks (Kstar u)
  | TApp : forall k1 k2, type ks (Karr k1 k2) -> type ks k1 -> type ks k2
  | TPi  : forall (k : kind U0) u, type (k :: ks) (Kstar u) -> type ks (Kstar U1)
  | TVar : forall k, member k ks -> type ks k
  | TInj : forall (k : kind U0), Tsymbol k -> type ks k.
  Arguments TInj [_ _] _.

  Definition mx (a b : univ) : univ :=
    match a with
    | U1 => U1
    | _ => b
    end.

  Definition ksigTu {u : univ} (K : KSigT u) : univD u.
  destruct u; apply K.(ksigT).
  Defined.

  Fixpoint tmorphism (u : univ) (k : kind u) {struct k}
  : ksigTu (kindD k) -> ksigTu (kindD k) ->
    univD u.
  refine
    match k  as k in kind u
          return ksigTu (kindD k) -> ksigTu (kindD k) ->
                 univD u
    with
    | Karr k1 k2 => fun f g =>
      forall x y : ksigTu (kindD k1),
        tmorphism _ k1 x x ->
        tmorphism _ k1 y y ->
        tmorphism _ k1 x y ->
        tmorphism _ k2 (f x) (g y)
    | Kstar U0 => path
    | Kstar U1 => path
    end.
  Defined.
  Arguments tmorphism [_] _ _ _.

  Record TSigT0 (k : kind U0) : Type@{Usmall} := mkTSigT0
  { tsigT0      : (kindD k).(ksigT)
  ; tsigProper0 : tmorphism k tsigT0 tsigT0
  }.

  Record TSigT1 (k : kind U1) : Type@{Ularge} := mkTSigT1
  { tsigT1      : (kindD k).(ksigT)
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
  : TSigT (Karr a b) -> TSigT a -> TSigT b.
  simpl. intros.
  exists (X.(tsigT0) X0.(tsigT0)).
  eapply X.(tsigProper0). eapply X0.(tsigProper0).
  eapply X0.(tsigProper0).
  eapply X0.(tsigProper0).
  Defined.

  Definition tpi {a} {k : kind U0}
  : (TSigT k -> TSigT (Kstar a)) ->
    TSigT (Kstar U1).
  refine
    match a as a
          return (TSigT k -> TSigT (Kstar a)) ->
                 TSigT (Kstar U1)
    with
    | U0 => fun X => _
    | U1 => fun X => _
    end.
  { simpl.
    exists (forall x : TSigT0 k, (X x).(tsigT1)).
    apply path_refl. }
  { simpl.
    exists (forall x : TSigT0 k, (X x).(tsigT0)).
    apply path_refl. }
  Defined.

  Variable TsymbolD : forall u (k : kind u),
      Tsymbol k -> TSigT k.

  Definition Kenv (ks : list (kind U0)) : Type@{Ularge} :=
    hlist@{Urefl Usmall} TSigT0 ks.

  Fixpoint typeD {ks u} {k : kind u} (t : type ks k)
  : Kenv ks -> TSigT k.
  refine
    match t in @type _ u k
          return Kenv ks -> TSigT k
    with
    | TArr a b => fun us => tarr (@typeD _ _ _ a us) (@typeD _ _ _ b us)
    | TApp f x => fun us => tapp (@typeD _ _ _ f us) (@typeD _ _ _ x us)
    | @TPi _ k0 _ t => fun us =>
      tpi (fun x : @TSigT U0 k0 => @typeD _ _ _ t (Hcons _ us))
    | TVar m   => fun us => hlist_get m us
    | TInj s   => fun _  => TsymbolD s
    end.
  { exact x. }
  Defined.

  Record Tuvar (ks : list (kind U0)) : Type@{Urefl} :=
  { Uctx  : list (type ks (Kstar U0))
  ; Utype : type ks (Kstar U0)
  }.


  Definition Venv (ks : list (kind U0)) (tvs : list (type ks (Kstar U0)))
             (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t : type ks (Kstar U0) =>
                           tsigT0 (@typeD _ U0 _ t Ks)) tvs.


  Definition Uenv (ks : list (kind U0)) (tus : list (Tuvar ks))
             (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t =>
                           @Venv ks t.(Uctx) Ks ->
                           tsigT0 (@typeD _ U0 _ t.(Utype) Ks)) tus.

  Unset Elimination Schemes.

  Fixpoint type_lift ks ks' ks'' u (k : kind u) (t : type (ks ++ ks'') k)
  : type (ks ++ ks' ++ ks'') k :=
    match t in @type _ u k
          return @type (ks ++ ks' ++ ks'') u k
    with
    | TArr a b => TArr (@type_lift _ _ _ _ _ a) (@type_lift _ _ _ _ _ b)
    | TApp f x => TApp (@type_lift _ _ _ _ _ f) (@type_lift _ _ _ _ _ x)
    | TVar v => TVar (member_lift _ _ _ v)
    | TPi t => TPi (@type_lift (_::_) _ _ _ _ t)
    | TInj x => TInj x
    end.


(*
  Definition type_weaken ks' {ks} {u} {k : kind u} (t : type ks k)
  : type (ks ++ ks') k :=
    match app_nil_r_trans ks in _ = X
        , app_nil_r_trans ks' in _ = Y
          return (type X _ -> type (_ ++ Y) _)
    with
    | eq_refl , eq_refl => @type_lift ks ks' nil u k
    end t.
*)

  Fixpoint type_subst {ks ks' u} {ku : kind u}
           (xs : hlist (@type ks' U0) ks)
           (t : type ks ku) {struct t}
  : type ks' ku :=
    match t in type _ Z
          return type ks' Z
    with
    | TArr a b => TArr (@type_subst _ _ _ _ xs a) (@type_subst _ _ _ _ xs b)
    | TApp a b => TApp (@type_subst _ _ _ _ xs a) (@type_subst _ _ _ _ xs b)
    | TPi t =>
      let xs' := hlist_map (fun k t => @type_lift nil (_::nil) ks' _ k t) xs in
      TPi (@type_subst (_::ks) _ _ _ (Hcons (TVar (@MZ _ _ _)) xs') t)
    | TVar v => hlist_get v xs
    | TInj x => TInj x
    end.

  Fixpoint members {T} (ls : list T) : hlist (fun x => member x ls) ls :=
    match ls as ls
          return hlist (fun x => member x ls) ls
    with
    | nil => Hnil
    | l :: ls => Hcons (MZ _ _) (hlist_map (fun t m => @MN _ _ _ _ m) (@members _ ls))
    end.

  Fixpoint member_post_weaken {T} (ls ls' : list T) {t} (m : member t ls)
  : member t (ls ++ ls') :=
    match m in member _ ls return member t (ls ++ ls') with
    | MZ _ _ => MZ _ _
    | MN _ m => MN _ (@member_post_weaken _ _ ls' _ m)
    end.

  Definition type_weaken (ks' ks : list (kind U0)) (u : univ) (k : kind u) (t : type ks k)
  : type (ks ++ ks') k :=
    type_subst
      (hlist_map@{Urefl Urefl Urefl}
                (fun (k0 : kind U0) (x : member k0 ks) => TVar (member_post_weaken ks' x)) 
                (members ks)) t.

  Fixpoint tvars_id ks
  : hlist (@type ks U0) ks :=
    match ks as ks
          return hlist (@type ks U0) ks
    with
    | nil => Hnil
    | k :: ks =>
      Hcons (TVar (@MZ _ _ _))
            (hlist_map (fun k t => @type_lift nil (_::nil) _ _ k t)
                       (tvars_id ks))
    end.

  Variable Esymbol : forall u (t : type nil (Kstar u)), Type@{Urefl}.

  Inductive wtexpr (ks : list (kind U0))
            (tus : list (Tuvar ks))
            (tvs : list (type ks (Kstar U0)))
  : forall u, type ks (Kstar u) -> Type@{Urefl} :=
  | wtVar : forall t, member t tvs -> wtexpr tus tvs t
  | wtInj : forall u (t : type nil (Kstar u)),
      Esymbol t -> wtexpr tus tvs (type_weaken _ t)
  | wtApp : forall u d r,
      wtexpr tus tvs (TArr d r) ->
      wtexpr tus tvs d -> wtexpr tus tvs (u:=u) r
  | wtTApp : forall k u t,
      wtexpr tus tvs (@TPi ks k u t) ->
      forall w : type ks k,
        @wtexpr ks tus tvs u (@type_subst _ _ _ _ (Hcons w (tvars_id _)) t)
  | wtAbs : forall u d (r : type ks (Kstar u)),
      wtexpr tus (d :: tvs) r -> wtexpr tus tvs (TArr d r)
  | wtUVar : forall tst, member tst tus ->
                    hlist (@wtexpr ks tus tvs U0) tst.(Uctx) ->
                    wtexpr tus tvs tst.(Utype).
  Set Elimination Schemes.
  Arguments wtVar {_ _ _} [_] _.
  Arguments wtInj {_ _ _} [_ _] _.
  Arguments wtApp {_ _ _} [_ _ _] _ _.
  Arguments wtAbs {_ _ _} [_ _ _] _.
  Arguments wtTApp {_ _ _} [_ _ _] _ _.
  Arguments wtUVar {_ _ _} [_] _ _.

  Definition tsigT_star (u : univ) : TSigT (Kstar u) -> Type@{Ularge} :=
    match u as u return TSigT (Kstar u) -> Type@{Ularge} with
    | U0 => fun x => x.(tsigT0)
    | U1 => fun x => x.(tsigT1)
    end.

  Definition tsigT (u : univ) (k : kind u) : TSigT k -> ksigTu (kindD k).
  destruct u.
  { refine (fun x => x.(tsigT1)). }
  { refine (fun x => x.(tsigT0)). }
  Defined.

  Arguments tsigT_star [_] _.
  Arguments tsigT [_ _] _.


  Definition exprApp {ks : list (kind U0)} {u0 : univ} {t0 : type ks (Kstar U0)}
             {t1 : type ks (Kstar u0)} {Ts : Kenv ks}
  : tsigT_star (typeD (TArr t0 t1) Ts) ->
    tsigT_star (typeD t0 Ts) ->
    tsigT_star (typeD t1 Ts).
  { simpl in *.
    destruct u0; refine (fun x => x). }
  Defined.

  Definition exprAbs {ks : list (kind U0)}
             {u0 : univ} {t0 : type ks (Kstar U0)} {t1 : type ks (Kstar u0)}
             {Ts : Kenv ks}
    : (tsigT (typeD t0 Ts) -> tsigT_star (typeD t1 Ts)) ->
      tsigT_star (typeD (TArr t0 t1) Ts).
    destruct u0; simpl; refine (fun f x => f x).
  Defined.

  Lemma exprInst {ks : list (kind U0)} {k : kind U0} {u0 : univ}
        {t0 : type (k :: ks) (Kstar u0)} {t : type ks k}
        {Ts : Kenv ks}
  : tsigT_star (typeD (TPi t0) Ts) ->
    forall x : TSigT0 k,
      tsigT_star (typeD t0 (Hcons@{Urefl Usmall} x Ts)).
  Proof.
    clear. simpl in *. unfold tpi.
    destruct u0; exact (fun x => x).
  Defined.

  (** TODO(gmalecha): Move this *)
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

  Variable EsymbolD : forall u t, @Esymbol u t -> tsigT_star (@typeD _ _ _ t Hnil).

  Lemma tmorphism_TSigT_refl:
    forall u (k : kind u) (t : TSigT k), tmorphism k (tsigT t) (tsigT t).
  Proof.
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

  Lemma typeD_type_lift:
    forall (ks ks' ks'' : list (kind U0)) u (k0 : kind u) (t : type (ks' ++ ks) k0)
      (Ts : Kenv ks) (Ts' : Kenv ks') (Ts'' : Kenv ks''),
      tmorphism k0
                (tsigT (typeD (type_lift ks' ks'' ks t) (hlist_app Ts' (hlist_app Ts'' Ts))))
                (tsigT (typeD t (hlist_app Ts' Ts))).
  Proof.
    refine
      (fix rec ks ks' ks'' u k0 (t : type (ks' ++ ks) k0) {struct t} :=
         match t as t in type _ k
               return forall (Ts : Kenv ks) (Ts' : Kenv ks') (Ts'' : Kenv ks''),
             tmorphism k
                       (tsigT (typeD (type_lift ks' ks'' ks t) (hlist_app Ts' (hlist_app Ts'' Ts))))
                       (tsigT (typeD t (hlist_app Ts' Ts)))
         with
         | TArr l r => fun Ts Ts' Ts'' =>
                        _ (@rec ks ks' ks'' U0 _ l Ts Ts' Ts'')
                          (@rec ks ks' ks'' _ _ r Ts Ts' Ts'')
         | TApp l r => fun Ts Ts' Ts'' =>
                        _ (@rec ks ks' ks'' U0 _ l Ts Ts' Ts'')
                          (@rec ks ks' ks'' _ _ r Ts Ts' Ts'')
         | @TPi _ k _ r => fun Ts Ts' Ts'' =>
                            _ (fun x => @rec ks (k :: ks') ks'' _ _ r Ts (Hcons x Ts') Ts'')
         | TVar m => fun Ts Ts' Ts'' => _
         | TInj i => fun _ _ _ => _
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
  Defined.

  Lemma type_subst_mor:
    forall (ks' : list (kind U0))
      uu (Z : kind uu) (t0 : type ks' Z)
      ks
      (Ts : Kenv ks) (Ts' : Kenv ks')
      (Sub : hlist (fun x => type ks x) ks'),
      (forall (k : kind U0) (m : member k ks'),
          tmorphism k (tsigT0 (typeD (hlist_get m Sub) Ts)) (tsigT0 (hlist_get m Ts'))) ->
      tmorphism Z (tsigT (typeD (type_subst Sub t0) Ts)) (tsigT (typeD t0 Ts')).
  Proof.
    clear.
    induction t0.
    { intros.
      specialize (IHt0_1 ks0 Ts Ts' Sub X).
      specialize (IHt0_2 ks0 Ts Ts' Sub X).
      destruct u; simpl in *;
        apply (path_arrow IHt0_1 IHt0_2). }
    { intros.
      specialize (IHt0_1 ks0 Ts Ts' Sub X).
      specialize (IHt0_2 ks0 Ts Ts' Sub X).
      clear - IHt0_1 IHt0_2.
      simpl in *.
      eapply IHt0_1. all: try eapply (@tmorphism_TSigT_refl U0).
      eapply IHt0_2. all: try eapply (@tmorphism_TSigT_refl U0). }
    { intros.
      specialize (fun x => IHt0 (k :: ks0) (Hcons x Ts) (Hcons x Ts')
                             (Hcons@{Urefl Urefl} (TVar (MZ k ks0))
                                   (hlist_map@{Urefl Urefl Urefl}
                                             (fun (k0 : kind U0) (t : type ks0 k0) =>
                                                type_lift nil (k :: nil) ks0 t) Sub))).
      destruct u; simpl in *.
      { eapply path_all. intros; eapply IHt0.
        intros.
        destruct (member_caseT m).
        { destruct s. subst. simpl. eapply (@tmorphism_TSigT_refl U0). }
        { destruct s. subst. simpl.
          rewrite hlist_get_hlist_map.
          eapply (@tmorphism_TSigT_trans U0); [ | eapply X ].
          simpl.
          match goal with
          | |- tmorphism _ (tsigT0 (typeD (type_lift _ _ _ ?Y) _)) (tsigT0 (typeD ?X _)) =>
            change Y with X ; generalize X
          end. clear.
          intros. apply (@typeD_type_lift ks0 nil (k :: nil) _ _ t Ts Hnil (Hcons x Hnil)). } }
      { eapply (@path_all@{Utiny Usmall}). intros; eapply IHt0.
        intros.
        destruct (member_caseT m).
        { destruct s. subst. simpl. eapply (@tmorphism_TSigT_refl U0). }
        { destruct s. subst. simpl.
          rewrite hlist_get_hlist_map.
          eapply (@tmorphism_TSigT_trans U0); [ | eapply X ].
          simpl.
          match goal with
          | |- tmorphism _ (tsigT0 (typeD (type_lift _ _ _ ?Y) _)) (tsigT0 (typeD ?X _)) =>
            change Y with X ; generalize X
          end. clear.
          intros. apply (@typeD_type_lift ks0 nil (k :: nil) _ _ t Ts Hnil (Hcons x Hnil)). } } }
    { intros. simpl.
      eapply (@tmorphism_TSigT_trans U0); [ | eapply X ].
      eapply tmorphism_TSigT_refl. }
    { intros.
      eapply tmorphism_TSigT_refl. }
  Defined.

  Lemma hlist_get_tvars_id:
    forall (ks : list (kind U0)) (k0 : kind U0) (x : member k0 ks),
      hlist_get@{Urefl Urefl} x (tvars_id ks) = TVar x.
  Proof.
    induction x; simpl.
    { reflexivity. }
    { rewrite hlist_get_hlist_map.
      match goal with
      | H : ?Y = _ |- type_lift _ _ _ ?X = _ =>
        change X with Y ; rewrite H
      end.
      reflexivity. }
  Defined.

  Fixpoint wtexprD ks tus tvs u t (e : @wtexpr ks tus tvs u t)
  : forall Ts, Uenv tus Ts -> Venv tvs Ts -> tsigT_star (@typeD _ _ _ t Ts).
  refine
    match e in @wtexpr _ _ _ u t
          return forall Ts, Uenv tus Ts -> Venv tvs Ts ->
                       tsigT_star (@typeD _ _ _ t Ts)
    with
    | wtVar v => fun _ _ Vs => hlist_get v Vs
    | wtInj s => fun _ _ _ => _
    | wtAbs e => fun Ts Us Vs =>
      (fun E => exprAbs (fun x => E (Hcons _ Vs)))
        (@wtexprD _ _ _ _ _ e Ts Us)
    | wtApp f x => fun Ts Us Vs =>
      exprApp (@wtexprD _ _ _ _ _ f Ts Us Vs)
              (@wtexprD _ _ _ _ _ x Ts Us Vs)
    | wtTApp f t => fun Ts Us Vs =>
      let T := @typeD _ _ _ t Ts in
      _ (@wtexprD _ _ _ _ _ f Ts Us Vs)
    | wtUVar u xs => fun Ts Us Vs =>
      _ (hlist_get u Us)
        (hlist_map
           (fun t e => @wtexprD _ _ _ _ t e Ts Us Vs)
           xs)
    end.
  { (** inj *)
    generalize (EsymbolD s).
    unfold type_weaken.
    generalize (@type_subst_mor nil _ _ t0 ks k Hnil Hnil).
    simpl members. simpl hlist_map.
    Definition tmorphism_into u (X Y : _)
               (mor : tmorphism (Kstar u) (tsigT X) (tsigT Y))
      : tsigT_star X -> tsigT_star Y.
    Proof using .
    destruct u; simpl in *; eapply mor.
    Defined.
    intro.
    eapply tmorphism_into.
    eapply tmorphism_TSigT_sym. eapply X.
    clear. intros.
    exfalso. clear - m.
    eapply (member_case m). }
  { (* Pi *)
    simpl in *.
    unfold tpi. destruct u0; simpl; refine (fun f => _ (f T)).
    { eapply (@type_subst_mor _ _ _ t0 ks Ts (Hcons T Ts) (Hcons@{Urefl Urefl} t (tvars_id ks))).
      intros.
      destruct (member_caseT m).
      { destruct s; subst. simpl. eapply (@tmorphism_TSigT_refl U0). }
      { destruct s; subst. simpl.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). } }
    { eapply (@type_subst_mor _ _ _ t0 ks Ts (Hcons T Ts) (Hcons@{Urefl Urefl} t (tvars_id ks))).
      intros.
      destruct (member_caseT m).
      { destruct s; subst. simpl. eapply (@tmorphism_TSigT_refl U0). }
      { destruct s; subst. simpl.
        rewrite hlist_get_tvars_id.
        eapply (@tmorphism_TSigT_refl U0). } } }
  { eapply x. }
  { (* UVar *)
    eapply todo. (* admit. *) }
  Defined.

End simple_dep_types.
