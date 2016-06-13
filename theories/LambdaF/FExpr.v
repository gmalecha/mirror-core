Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.LambdaWt.DepUtil.

Set Implicit Arguments.
Set Strict Implicit.
Set Printing Universes.

Polymorphic Axiom todo : forall X : Type, X.

Polymorphic Inductive path@{t u} (x : Type@{t}) : Type@{t} -> Type@{u} :=
| path_refl : path x x.

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

Polymorphic Record KSigT'@{a b c} : Type@{a} := mkKSigT'
{ ksigT : Type@{b}
; ksigR : ksigT -> ksigT -> Type@{c} }.

Definition KSigT (u : univ) : Type@{Uhuge} :=
  match u as u return Type@{Uhuge} with
  | U0 => KSigT'@{Ularge Usmall Usmall}
  | U1 => KSigT'@{Uhuge Ularge Ularge}
  end.

Fixpoint kindD {u} (k : kind u) : KSigT u :=
  match k in kind u return KSigT u with
  | Karr a b =>
    let a := kindD a in
    let b := kindD b in
    @mkKSigT' 
             (a.(ksigT) -> b.(ksigT))
             (fun l r => forall x y, a.(ksigR) x y -> b.(ksigR) (l x) (r y))
  | Kstar U0 =>
    @mkKSigT' Type@{Utiny} path
  | Kstar U1 =>
    @mkKSigT' Type@{Usmall} path
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
  | TPi  : forall k u, type (k :: ks) (Kstar u) -> type ks (Kstar U1)
  | TVar : forall k, member k ks -> type ks k
  | TInj : forall (k : kind U0), Tsymbol k -> type ks k.
  Arguments TInj [_ _] _.

  Definition mx (a b : univ) : univ :=
    match a with
    | U1 => U1
    | _ => b
    end.

(*
  Definition univD_to_Type {u : univ} (v : univD u) : Type@{Ularge}.
    destruct u; apply v.
  Defined.
*)
(*
  
  Definition typeD_to_Type {u} {k : kind u} (td : univD_to_Type (kindD k))
  : Type@{Uhuge}.
  Admitted.

  Fixpoint tmorphism (u : univ) (k : kind u) {struct k}
  : univD_to_Type (kindD k) -> univD_to_Type (kindD k) ->
    univD u.
  refine
    match k  as k in kind u
          return univD_to_Type (kindD k) -> univD_to_Type (kindD k) ->
                 univD u
    with
    | Karr k1 k2 => fun f g =>
      forall x y : kindD k1, tmorphism _ k1 x y -> tmorphism _ k2 (f x) (g y)
    | Kstar u => _
    end.
  unfold univD_to_Type.
  all: simpl.
  destruct u; refine (fun x y => path x y)%type.
  Defined.
*)

  (** NOTE: This will not work because the type is too large *)
  Record TSigT0 (k : KSigT U0) : Type@{Usmall} := mkTSigT0
  { tsigT0      : k.(ksigT)
  ; tsigProper0 : k.(ksigR) tsigT0 tsigT0
  }.

  Record TSigT1 (k : KSigT U1) : Type@{Ularge} := mkTSigT1
  { tsigT1      : k.(ksigT)
  ; tsigProper1 : k.(ksigR) tsigT1 tsigT1
  }.

  Definition TSigT {u} : KSigT u -> Type@{Ularge} :=
    match u as u return KSigT u -> Type@{Ularge} with
    | U0 => TSigT0
    | U1 => TSigT1
    end.

  Definition tarr {a b}
  : TSigT (kindD (Kstar a)) ->
    TSigT (kindD (Kstar b)) ->
    TSigT (kindD (Kstar (mx a b))).
  refine
    match a as a
        , b as b
          return TSigT (kindD (Kstar a)) ->
                 TSigT (kindD (Kstar b)) ->
                 TSigT (kindD (Kstar (mx a b)))
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
  : TSigT (kindD (Karr a b)) -> TSigT (kindD a) -> TSigT (kindD b).
  simpl. intros.
  exists (X.(tsigT0) X0.(tsigT0)).
  eapply X.(tsigProper0). eapply X0.(tsigProper0).
  Defined.

  Definition tpi {a} {k : kind U0}
  : (TSigT (kindD k) -> TSigT (kindD (Kstar a))) ->
    TSigT (kindD (Kstar U1)).
  refine
    match a as a
          return (TSigT (kindD k) -> TSigT (kindD (Kstar a))) ->
                 TSigT (kindD (Kstar U1))
    with
    | U0 => fun X => _
    | U1 => fun X => _
    end.
  { simpl.
    exists (forall x : TSigT0 (kindD k), (X x).(tsigT1)).
    apply path_refl. }
  { simpl.
    exists (forall x : TSigT0 (kindD k), (X x).(tsigT0)).
    apply path_refl. }
  Defined.

  Variable TsymbolD : forall u (k : kind u),
      Tsymbol k -> TSigT (kindD k).


  Fixpoint typeD {ks u k} (t : type ks k)
  : hlist@{Urefl Uhuge} (fun k => TSigT (@kindD U0 k)) ks ->
    TSigT (@kindD u k).
  refine
    match t in @type _ u k
          return hlist@{Urefl Uhuge} (fun k => TSigT (@kindD U0 k)) ks ->
                 TSigT (@kindD u k)
    with
    | TArr a b => fun us => tarr (@typeD _ _ _ a us) (@typeD _ _ _ b us)
    | TApp f x => fun us => tapp (@typeD _ _ _ f us) (@typeD _ _ _ x us)
    | @TPi _ k0 _ t => fun us =>
      tpi (fun x : @TSigT U0 (kindD k0) => @typeD _ _ _ t (Hcons _ us))
    | TVar m   => fun us => hlist_get m us
    | TInj s   => fun _  => TsymbolD s
    end.
  { exact x. }
  Defined.


  Definition typeD_to_Type {u} (td : univD_to_Type (kindD (Kstar u)))
  : Type@{Uhuge}.
    destruct u; simpl in *; apply td.
  Defined.

  Definition Kenv (ks : list (kind U0)) : Type@{Ularge} :=
    hlist@{Urefl Usmall} (@kindD U0) ks.

  Definition Uenv (ks : list (kind U0)) (tus : list (Tuvar ks))
             (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t => typeD_to_Type (@typeD _ _ _ (snd t) Ks)) tus.

  Definition Venv (ks : list (kind U0)) (tvs : list (type ks (Kstar U0)))
             (Ks : Kenv ks) : Type@{Uhuge} :=
    hlist@{Urefl Uhuge} (fun t => typeD_to_Type (@typeD _ _ _ t Ks)) tvs.


  Unset Elimination Schemes.

  Variable Esymbol : forall u (t : type nil (Kstar u)), Type@{Urefl}.

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

  Definition type_weaken ks' {ks} {u} {k : kind u} (t : type ks k)
  : type (ks ++ ks') k :=
    match app_nil_r_trans ks in _ = X
        , app_nil_r_trans ks' in _ = Y
          return (type X _ -> type (_ ++ Y) _)
    with
    | eq_refl , eq_refl => @type_lift ks ks' nil u k
    end t.

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

(*
  Inductive wtexpr (ks : list (kind U0))
            (tus : list (Tuvar ks))
            (tvs : list (type ks (Kstar U0)))
  : forall (Sub : hlist (fun k => @type ks _ k) ks),
      forall u, type ks (Kstar u) -> Type@{Urefl} :=
  | wtVar : forall Sub t, member t tvs -> wtexpr tus tvs Sub t
(*  | wtInj : forall u (t : type nil (Kstar u)),
      Esymbol t -> wtexpr tus tvs (type_weaken _ t)
  | wtApp : forall u d r,
      wtexpr tus tvs (TArr d r) ->
      wtexpr tus tvs d -> wtexpr tus tvs (u:=u) r
*)
  | wtTApp : forall Sub k u t,
      wtexpr tus tvs Sub (@TPi ks k u t) ->
      forall w : type ks k,
        @wtexpr (k :: ks) (tus tvs (Hcons w Sub) u t
(*
  | wtAbs : forall u d (r : type ks (Kstar u)),
      wtexpr tus (d :: tvs) r -> wtexpr tus tvs (TArr d r)
  | wtUVar : forall ts t, member (ts, t) tus ->
                          hlist (@wtexpr ks tus tvs U0) ts -> wtexpr tus tvs t
*).
*)


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
  | wtUVar : forall ts t, member (ts, t) tus ->
                          hlist (@wtexpr ks tus tvs U0) ts -> wtexpr tus tvs t.
  Set Elimination Schemes.
  Arguments wtVar {_ _ _ _} _.
  Arguments wtInj {_ _ _ _ _} _.
  Arguments wtApp {_ _ _ _ _ _} _ _.
  Arguments wtAbs {_ _ _ _ _ _} _.
  Arguments wtTApp {_ _ _ _ _ _} _ _.

  Definition exprApp {ks : list (kind U0)} {u0 : univ} {t0 : type ks (Kstar U0)}
             {t1 : type ks (Kstar u0)} {Ts : Kenv ks}
  : typeD_to_Type (typeD (TArr t0 t1) Ts) ->
    typeD_to_Type (typeD t0 Ts) ->
    typeD_to_Type (typeD t1 Ts).
    destruct u0; simpl in *; refine (fun f x => f x).
  Defined.

  Definition exprAbs {ks : list (kind U0)}
             {u0 : univ} {t0 : type ks (Kstar U0)} {t1 : type ks (Kstar u0)}
             {Ts : Kenv ks}
    : (typeD_to_Type (typeD t0 Ts) -> typeD_to_Type (typeD t1 Ts)) ->
      typeD_to_Type (typeD (TArr t0 t1) Ts).
    destruct u0; simpl; refine (fun f x => f x).
  Defined.

  Lemma exprInst {ks : list (kind U0)} {k : kind U0} {u0 : univ}
        {t0 : type (k :: ks) (Kstar u0)} {t : type ks k}
        {Ts : Kenv ks}
  : typeD_to_Type (typeD (TPi t0) Ts) ->
    forall x : univD_to_Type (kindD k),
      typeD_to_Type (typeD t0 (Hcons@{Urefl Usmall} x Ts)).
  Proof.
    clear. simpl in *. unfold tpi.
    destruct u0; exact (fun x => x).
  Defined.

(*       (typeD (type_subst (Hcons t (tvars_id ks)) t0) Ts). *)


  Hypothesis TsymbolD_morphism
    : forall u (k : kind u) t,
      univD_to_Type (tmorphism k (TsymbolD t) (TsymbolD t)).

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

  Lemma typeD_subst
  : forall ks u (t : type ks (Kstar u)) ks' Sub (Ts : Kenv ks) (Ts' : Kenv ks'),
      (forall k (m : member k ks),
          tmorphism k (hlist_get m Ts) (typeD (hlist_get m Sub) Ts')) ->
      univD_to_Type (tmorphism _ (typeD t Ts) (typeD (type_subst Sub t) Ts')).
  Proof.
    induction t.
    { intros.
      specialize (IHt1 _ Sub Ts Ts').
      specialize (IHt2 _ Sub Ts Ts').
      destruct u; simpl in *; intros.
      { tauto. }
      { tauto. } }
    { intros.
      specialize (IHt1 _ Sub Ts Ts').
      specialize (IHt2 _ Sub Ts Ts').
      simpl in *.
      eapply IHt1; eauto. }
    { intros.
      simpl.
      specialize (fun Z =>
                    IHt _ (Hcons@{Urefl Urefl} (TVar (MZ k ks'))
                                (hlist_map@{Urefl Urefl Urefl}
                                          (fun (k0 : kind U0) (t0 : type ks' k0) =>
                                             type_lift nil (k :: nil) ks' t0) Sub))
                        (Hcons Z Ts) (Hcons Z Ts')).
      assert (forall Z,
                 (forall (k0 : kind U0) (m : member k0 (k :: ks)),
         tmorphism k0 (hlist_get@{Urefl Usmall} m (Hcons@{Urefl Usmall} Z Ts))
           (typeD
              (hlist_get@{Urefl Urefl} m
                 (Hcons@{Urefl Urefl} (TVar (MZ k ks'))
                    (hlist_map@{Urefl Urefl Urefl}
                       (fun (k1 : kind U0) (t0 : type ks' k1) =>
                        type_lift nil (k :: nil) ks' t0) Sub)))
              (Hcons@{Urefl Usmall} Z Ts')))).
      { clear - X.
        intros. revert X. revert Ts Ts'. revert Sub.

        destruct (member_caseT m).
        { destruct s. subst. simpl.
          admit. }
        { admit. } }
      specialize (fun Z => IHt Z (X0 Z)).
      clear X0 X.
      destruct u; simpl in *; intros.
      { split.
        { intros.
          eapply IHt.
          eapply X. }
        { intros. eapply IHt.
          intros. eapply X. } }
      { split.
        { intros.
          eapply IHt.
          eapply X. }
        { intros. eapply IHt.
          intros. eapply X. } } }
    { simpl in *. intros.
      eapply X. }
    { simpl; intros; eauto.
      exact (@TsymbolD_morphism _ k t). }
  Defined.

  Fixpoint wtexprD ks tus tvs u t (e : @wtexpr ks tus tvs u t)
  : forall Ts, Uenv tus Ts -> Venv tvs Ts -> typeD_to_Type (@typeD _ _ _ t Ts).
  refine
    match e in @wtexpr _ _ _ u t
          return forall Ts, Uenv tus Ts -> Venv tvs Ts ->
                            typeD_to_Type (@typeD _ _ _ t Ts)
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
      _ (@wtexprD _ _ _ _ _ f Ts Us Vs)
        (@typeD _ _ _ t Ts)
    | wtUVar u xs => fun Ts Us Vs =>
      _ (hlist_get u Us)
        (hlist_map
           (fun t e => @wtexprD _ _ _ _ t e Ts Us Vs)
           xs)
    end.
  { (** inj *)
    Check type_weaken.

    eapply todo. (* admit. *) }
  { (* Pi *)
    simpl in *.
    destruct u0; simpl.
    { generalize (@typeD_subst _ _ t0 ks
                               (Hcons@{Urefl Urefl} t (tvars_id ks))); intro X.
      specialize (X (Hcons@{Urefl Usmall} (typeD t Ts) Ts) Ts).
      simpl in *.
      assert ((forall (k0 : kind U0) (m : member k0 (k :: ks)),
                  tmorphism k0
                            (hlist_get@{Urefl Usmall} m (Hcons@{Urefl Usmall} (typeD t Ts) Ts))
                            (typeD
                               (hlist_get@{Urefl Urefl} m (Hcons@{Urefl Urefl} t (tvars_id ks)))
                               Ts))).
      { eapply todo. (* admit. *) }
      specialize (X X0); clear X0.
      destruct X. intros.
      eapply t2. eapply x. }
    { generalize (@typeD_subst _ _ t0 ks
                               (Hcons@{Urefl Urefl} t (tvars_id ks))); intro X.
      specialize (X (Hcons@{Urefl Usmall} (typeD t Ts) Ts) Ts).
      simpl in *.
      assert ((forall (k0 : kind U0) (m : member k0 (k :: ks)),
                  tmorphism k0
                            (hlist_get@{Urefl Usmall} m (Hcons@{Urefl Usmall} (typeD t Ts) Ts))
                            (typeD
                               (hlist_get@{Urefl Urefl} m (Hcons@{Urefl Urefl} t (tvars_id ks)))
                               Ts))).
      { eapply todo. (* admit. *) }
      specialize (X X0); clear X0.
      destruct X. intros.
      eapply t2. eapply x. }
  }
  { eapply x. }
  { (* UVar *)
    eapply todo. (* admit. *) }
  Defined.

(*
  Eval simpl in fun t : type nil (Kstar U0) =>
      wtexprD
        (wtApp (tvs:=nil) (tus:=nil)
               (wtAbs (wtVar (@MZ _ (TArr t t) _)))
               (wtAbs (wtVar (@MZ _ t _)))) (Ts:=Hnil) Hnil Hnil.
*)


  Definition exprT ks (tus : list (Tuvar ks)) (tvs : list (type ks (Kstar U0)))
             (T : Type@{Uhuge})
  : Type@{Uhuge} :=
    forall Ts, Uenv tus Ts -> Venv tvs Ts -> T.


  Definition exprApp {a b

(*
  Definition codom a (t : type (Kstar a)) : type (Kstar U0) :=
    match t with
    | TArr _ c => c
    | _ => t
    end.

  Definition dom (t : type Kstar) : type Kstar :=
    match t with
    | TArr d _ => d
    | _ => t
    end.
*)

End simple_dep_types.


  Focus 2.
  clear. destruct u0; simpl; intros f x.
  Check @tarr.

  Set Printing Universes.
