Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.

(** Auxiliary Definitions for members **)
Section member_functions.
  Context {T : Type}.
  Fixpoint mLift {ls ls' : list T} {t : T} (t' : T) {struct ls}
  : member t (ls ++ ls') -> member t (ls ++ t' :: ls') :=
    match ls as l return member t (l ++ ls') -> member t (l ++ t' :: ls') with
    | nil => fun m0 => MN t' m0
    | t0 :: ls0 => fun m0 =>
      match m0 in member _ (X :: Y)
            return (member t Y -> member t (ls0 ++ t' :: ls')) ->
                   member t (X :: ls0 ++ t' :: ls')
      with
      | MZ _ ls1 => fun _ => MZ t (ls0 ++ t' :: ls')
      | @MN _ _ l ls1 m1 => fun rec => MN l (rec m1)
      end (mLift t')
    end.

  Fixpoint mSubst {ls ls'} {l l' : T} {struct ls}
    : member l (ls ++ l' :: ls') -> member l (ls ++ ls') + (l = l') :=
    match ls as l0
          return (member l (l0 ++ l' :: ls') -> member l (l0 ++ ls') + (l = l'))
    with
    | nil =>
      fun m : member l (l' :: ls') =>
        match
          m in member _ (X :: Y)
          return (member l Y + (l = X))%type
        with
        | MZ _ ls0 => inr eq_refl
        | @MN _ _ l0 ls0 m0 => inl m0
        end
    | t :: ls0 =>
      fun m : member l (t :: ls0 ++ l' :: ls') =>
        match m in member _ (X :: Y)
              return (member l Y -> member l (ls0 ++ ls') + (l = l')) ->
                     member l (X :: ls0 ++ ls') + (l = l')
        with
        | MZ _ ls1 => fun _ => inl (MZ l (ls0 ++ ls'))
        | @MN _ _ l0 ls1 m0 =>
          fun rec : member l ls1 -> member l (ls0 ++ ls') + (l = l') =>
            match rec m0 with
            | inl m1 => inl (MN l0 m1)
            | inr pf => inr pf
            end
        end mSubst
    end.
End member_functions.

(** * The proposed meta-theory **)

(*
(kinds)        k := k -> k | *
(large types)  l := forall x : k , l | [s]
(small types)  s := s -> s | s s | x | [b]
(expr)         e := \ x : s. e | e e | x | e s | [b]
*)

Set Printing Universes.

Universes U2 U1 U0.
Constraint U1 < U2.
Constraint U0 < U1.

(** * Kinds **)
Inductive kind : Set :=
| kArr (_ _ : kind)
| kStar : kind.

Fixpoint kindD (k : kind) : Type@{U2} :=
  match k with
  | kStar => Type@{U1}
  | kArr a b => kindD a -> kindD b
  end.

Fixpoint kindDs (k : kind) : Type@{U1} :=
  match k with
  | kStar => Type@{U0}
  | kArr a b => kindDs a -> kindDs b
  end.

(** * Types **)
(* Small Types *)
(* NOTE: It seems like more things should be large types and then we can inject
   where we need to
 *)
Inductive type (ks : list kind) : kind -> Set :=
| tApp : forall d r : kind, type ks (kArr d r) -> type ks d -> type ks r
| tVar : forall k, member k ks -> type ks k.

(* Large Types *)
Inductive ltype (ks : list kind) : Set :=
| tPi : forall k : kind, ltype (k :: ks) -> ltype ks
| tArr : ltype ks -> ltype ks -> ltype ks
| tSm : type ks kStar -> ltype ks.

Arguments tPi {_ _} _.
Arguments tArr {_} _ _.
Arguments tApp {_} {_ _} _ _.
Arguments tVar {_ _} _.
Arguments tSm {_} _.

Fixpoint typeD {ks k} (t : type ks k) : hlist kindDs ks -> kindDs k :=
  match t in type _ k0 return hlist kindDs ks -> kindDs k0 with
  | @tApp _ d r t1 t2 => fun tenv => typeD t1 tenv (typeD t2 tenv)
  | @tVar _ _ m => hlist_get m
  end.

Fixpoint ltypeD {ks} (t : ltype ks) : hlist kindDs ks -> kindD kStar :=
  match t with
  | @tPi _ k t0 => fun tenv : hlist kindDs ks => forall x : kindDs k, ltypeD t0 (Hcons x tenv)
  | tArr t1 t2 => fun tenv => ltypeD t1 tenv -> ltypeD t2 tenv
  | tSm t0 => fun tenv : hlist kindDs ks => typeD t0 tenv
  end.

(** Lifting and substitution **)
Fixpoint tLift (ks ks' : list kind) (k k' : kind) (t : type (ks ++ ks') k) : type (ks ++ k' :: ks') k :=
  match t in (type _ k0) return (type (ks ++ k' :: ks') k0) with
  | @tApp _ d r t1 t2 => tApp (tLift ks ks' (kArr d r) k' t1) (tLift ks ks' d k' t2)
  | @tVar _ k0 m => tVar (mLift k' m)
  end.

Fixpoint tSubst (ks ks' : list kind) (k k' : kind) (t : type (ks ++ k' :: ks') k) (w : type (ks ++ ks') k') :
  type (ks ++ ks') k :=
  match t in (type _ k0) return (type (ks ++ ks') k0) with
  | @tApp _ d r t1 t2 => tApp (tSubst ks ks' (kArr d r) k' t1 w) (tSubst ks ks' d k' t2 w)
  | @tVar _ k0 m =>
    match mSubst m with
    | inl m0 => tVar m0
    | inr e =>
      match e in _ = y
            return (member k0 (ks ++ y :: ks') -> type (ks ++ ks') y -> type (ks ++ ks') k0)
      with
      | eq_refl => fun (_ : member k0 (ks ++ k0 :: ks')) (w0 : type (ks ++ ks') k0) => w0
      end m w
    end
  end.

Fixpoint ltLift (ks ks' : list kind) k' (t : ltype (ks ++ ks')) : ltype (ks ++ k' :: ks') :=
  match t with
  | @tPi _ r t0 => tPi (ltLift (r :: ks) ks' k' t0)
  | tArr t1 t2 => tArr (ltLift ks ks' k' t1) (ltLift ks ks' k' t2)
  | tSm x => tSm (tLift ks ks' kStar k' x)
  end.

Fixpoint ltSubst (ks ks' : list kind) (k' : kind) (t : ltype (ks ++ k' :: ks')) (w : type (ks ++ ks') k') :
  ltype (ks ++ ks') :=
  match t with
  | @tPi _ r t0 => tPi (ltSubst (r :: ks) ks' k' t0 (tLift nil (ks ++ ks') k' r w))
  | tArr t1 t2 => tArr (ltSubst ks ks' k' t1 w) (ltSubst ks ks' k' t2 w)
  | tSm x => tSm (tSubst ks ks' kStar k' x w)
  end.

(** * Expressions **)
Inductive expr (ks : list kind) (ts : list (type ks kStar)) : type ks kStar -> Set :=
| eVar  : forall t, member t ts -> expr ks ts t.

Inductive lexpr (ks : list kind) (ts : list (type ks kStar)) : ltype ks -> Set :=
| eAbs : forall t (u : ltype ks), lexpr ks (t :: ts) u -> lexpr ks ts (tArr (tSm t) u)
| eApp : forall t u, lexpr ks ts (tArr t u) -> lexpr ks ts t -> lexpr ks ts u
| eAppT : forall k t, lexpr ks ts (@tPi _ k t) -> forall t' : type ks k, lexpr ks ts (ltSubst nil _ _ t t')
| eSm  : forall t, expr ks ts t -> lexpr ks ts (tSm t).

Print hlist.

(*
Section tenv.
  Inductive tenv : forall ks : list kind, hlist kindDs ks -> list type ks -> Type :=
  | Tnil : tenv nil Hnil
  | T
*)

Section hlist2.
  Context {T : Type} {F : T -> Type} (G : forall t : T, F t -> Type).
  Inductive hlist2 : forall ts : list T, hlist F ts -> Type :=
  | Hnil2 : hlist2 nil Hnil
  | Hcons2 : forall t ts x xs, G t x -> hlist2 ts xs -> hlist2 (t :: ts) (Hcons x xs).
End hlist2.


Fixpoint exprD {ks} {ts} {t} (e : expr ks ts t)
: forall (kenv : hlist kindDs ks)
         (tenv : hlist (fun t => @typeD ks kStar t kenv) ts),
    typeD t kenv :=
  match e in expr _ _ t0
    return forall kenv : hlist kindDs ks,
      hlist (fun t1 : type ks kStar => typeD t1 kenv) ts -> typeD t0 kenv
  with
  | eVar _ _ t0 m => fun kenv => hlist_get m
  end.

Fixpoint liftNil_skip {k k0} ks t' kenv x {struct t'}
  : typeD (tLift nil ks k k0 t')
          (Hcons x kenv) =
    typeD t' kenv.
Proof.
  destruct t'.
  - simpl.
    generalize (liftNil_skip _ k0 ks t'1 kenv x).
    generalize (liftNil_skip _ k0 ks t'2 kenv x).
    intros.
    Require Import ExtLib.Tactics.
    change_rewrite H.
    change_rewrite H0.
    reflexivity.
  - reflexivity.
Defined.

Polymorphic Record Iso@{t} (A B : Type@{t}) : Type :=
{ into : A -> B ; outof : B -> A }.

Arguments into {_ _} _ _.
Arguments outof {_ _} _ _.

Definition Iso_lift@{t} {A B : Type@{t}} :
  Iso A B -> Iso A B :=
  fun x => {| into := x.(into) ; outof := x.(outof) |}.

Definition Iso_forall {T} {F G : T -> Type}
           (i : forall x, Iso (F x) (G x))
  : Iso (forall x, F x) (forall x, G x) :=
{| into := fun (X : forall x : T, F x) (x : T) =>
             (fun X0 : forall x0 : T, F x0 -> G x0 => X0 x (X x))
               (fun x0 : T => into (i x0))
; outof := fun (X : forall x : T, G x) (x : T) =>
             (fun X0 : forall x0 : T, G x0 -> F x0 => X0 x (X x))
               (fun x0 : T => outof (i x0))
|}.

(** NOTE: This is relevant **)
(** NOTE: This type does not seem to work.
 ** In particular, Iso does not carry the right information.
 **)
Fixpoint ksIso (k : kind) : kindDs k -> kindDs k -> Type@{U1} :=
  match k as k return kindDs k -> kindDs k -> Type@{U1} with
  | kArr a b => fun f g => (forall x y, ksIso a x y -> ksIso b (f x) (g y))
  | kStar => fun f g => Iso f g
  end%type.

Definition ksIso_apply d r f g f' g' :
  ksIso (kArr d r) f' g' ->
  ksIso d f g ->
  ksIso r (f' f) (g' g).
  simpl. intros. apply X. assumption.
Defined.

Fixpoint kIso (k : kind) : kindD k -> kindD k -> Type@{U2} :=
  match k as k return kindD k -> kindD k -> Type@{U2} with
  | kArr a b => fun f g => (forall x y, kIso a x y -> kIso b (f x) (g y))
  | kStar => fun f g => Iso f g
  end%type.

Definition kIso_apply d r f g f' g' :
  kIso (kArr d r) f' g' ->
  kIso d f g ->
  kIso r (f' f) (g' g).
  simpl. intros. apply X. assumption.
Defined.

(*
      Definition Transitive_ksIso {k A B C} : ksIso k A B -> ksIso k B C -> ksIso k A C.
      Admitted.
      eapply Transitive_ksIso.
      Focus 2.
      instantiate (1 := match
          match
            m as m0 in (member _ iV)
            return
              (match
                 iV as iV0 return (member k0 iV0 -> Type)
               with
               | nil => fun _ : member k0 nil => IDProp
               | X :: Y =>
                   fun _ : member k0 (X :: Y) => (member k0 Y + (k0 = X))%type
               end m0)
          with
          | MZ _ ls0 => inr eq_refl
          | @MN _ _ l0 ls0 m0 => inl m0
          end
        with
        | inl m0 => typeD (tVar m0) kenv
        | inr e =>
            typeD (match
                      e in (_ = y)
                      return (member k0 (y :: ks) -> type ks y -> type ks k0)
                    with
                    | eq_refl => fun (_ : member k0 (k0 :: ks)) (w0 : type ks k0) => w0
                    end m t') kenv
        end).
      simpl.
      Definition member_case {T} (k k0 : T) (F : forall ks, member k ks -> Type) ks
                 (here : F (k :: ks) (MZ _ _))
                 (there : forall k' m, F (k' :: ks) (@MN T _ k' _ m))
                 (x : member k (k0 :: ks)) : F _ x.
      Proof.
        refine
          (match x as x in member _ Z
                 return match Z as Z return member k Z -> Type with
                        | nil => fun _ => unit
                        | z :: zs => fun m => zs = ks -> F (z :: zs) m
                        end x
           with
           | MZ _ _ => _
           | MN _ _ => _
           end eq_refl).
        intros; subst. apply here.
        intros; subst. apply there.
      Defined.
      match goal with
      | |- ksIso _ match ?X with _ => _ end (typeD match ?Y with _ => _ end _) =>
        assert (X = Y)
      end.
      reflexivity.
      generalize dependent (k :: ks).
      refine (@member_case _ k0 k _ ks _ _ m).
*)


Fixpoint typeD_inst {ks' ks : list kind} {k k'}
         (t : type (ks' ++ k :: ks) k') (t' : type (ks' ++ ks) k)
         {kenv' : hlist kindDs ks'} {kenv : hlist kindDs ks}
         {struct t}
: ksIso k'
       (@typeD (ks' ++ k :: ks) k' t
               (hlist_app kenv' (Hcons (@typeD _ k t' (hlist_app kenv' kenv)) kenv)))
       (@typeD (ks' ++ ks) _ (tSubst ks' ks k' _ t t') (hlist_app kenv' kenv)).
  destruct t.
  { simpl.
    generalize (typeD_inst ks' ks k _ t2 t' kenv' kenv).
    generalize (typeD_inst ks' ks k _ t1 t' kenv' kenv).
    eapply ksIso_apply. }
  { simpl.
    clear - m.
    (** TODO: This case is difficult! **)
    induction kenv'; simpl.
    - simpl in *.
      admit.
    - admit. }
Admitted.

Fixpoint ltypeD_inst {ks' ks : list kind} {k}
         (t : ltype (ks' ++ k :: ks)) (t' : type (ks' ++ ks) k)
         {kenv' : hlist kindDs ks'} {kenv : hlist kindDs ks}
         {struct t}
: kIso kStar
       (@ltypeD (ks' ++ k :: ks) t (hlist_app kenv' (Hcons (@typeD _ k t' (hlist_app kenv' kenv)) kenv)))
       (@ltypeD (ks' ++ ks) (ltSubst ks' ks k t t') (hlist_app kenv' kenv)).
  destruct t.
  { simpl. intros.
    specialize (@ltypeD_inst (k0 :: ks') ks k t (tLift nil (ks' ++ ks) k k0 t')).
    eapply Iso_forall.
    intro.
    specialize (ltypeD_inst (Hcons x kenv') kenv).
    simpl in *.
    revert ltypeD_inst.
    generalize (@liftNil_skip _ _ _ t' (hlist_app kenv' kenv) x).
    intro.
    change_rewrite H.
    exact (fun x => x). }
  { simpl.
    generalize (ltypeD_inst _ _ _ t1 t' kenv' kenv).
    generalize (ltypeD_inst _ _ _ t2 t' kenv' kenv).
    clear. constructor.
    - intros. eapply X. eapply X1. eapply X0. assumption.
    - intros. eapply X. eapply X1. eapply X0. assumption. }
  { simpl. clear ltypeD_inst.
    specialize (@typeD_inst ks' ks k kStar t t' kenv' kenv).
    simpl.
    exact (fun x => {| into := x.(into) ; outof := x.(outof) |}). }
Defined.



Fixpoint lexprD {ks} {ts} {t} (e : lexpr ks ts t)
: forall (kenv : hlist kindDs ks)
         (tenv : hlist (fun t => @typeD ks kStar t kenv) ts),
    ltypeD t kenv.
  destruct e.
  { simpl. intros.
    eapply (lexprD _ _ _ e).
    eapply Hcons. eassumption. exact tenv. }
  { intros.
    eapply ((lexprD _ _ _ e1 kenv tenv) (lexprD _ _ _ e2 kenv tenv)). }
  { intros.
    pose (lexprD _ _ _ e kenv tenv (typeD t' kenv)).
    generalize (@ltypeD_inst nil ks k t t' Hnil kenv).
    simpl.
    refine (fun x => x.(into) l). }
  { eapply exprD. eassumption. }
Defined.
