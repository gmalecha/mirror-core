Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

(* This is the universe of the reified language *)
Universe Urefl.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.

  Inductive type : Type :=
  | TArr : type -> type -> type
  | TInj : Tsymbol -> type.

  Fixpoint typeD (t : type) : Type@{Urefl} :=
    match t with
    | TArr a b => typeD a -> typeD b
    | TInj s => TsymbolD s
    end.

  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  (** TODO: If we move to a weaker notion of types, e.g. with reduction,
   ** we're going to need a weaker equivalence relation
   **)
  Fixpoint type_eq_dec (t t' : type) : {t = t'} + {t <> t'}.
  refine
    match t as t , t' as t' return {t = t'} + {t <> t'} with
    | TInj a , TInj b => match Tsymbol_eq_dec a b with
                         | left pf => left (f_equal _ pf)
                         | right pf => right _
                         end
    | TArr d c , TArr d' c' => match type_eq_dec d d'
                                   , type_eq_dec c c'
                               with
                               | left pf , left pf' => left _
                               | _ , _ => right _
                               end
    | _ , _ => right _
    end; try congruence.
  Defined.

  Variable Esymbol : type -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD t.

  Definition Tuvar : Type := list type * type.

  (** A guaranteed well-typed expr **)
  Unset Elimination Schemes.
  Inductive wtexpr (tus : list Tuvar) (tvs : list type) : type -> Type :=
  | wtVar : forall t, member t tvs -> wtexpr tus tvs t
  | wtInj : forall t, Esymbol t -> wtexpr tus tvs t
  | wtApp : forall d r, wtexpr tus tvs (TArr d r) ->
                        wtexpr tus tvs d -> wtexpr tus tvs r
  | wtAbs : forall d r, wtexpr tus (d :: tvs) r -> wtexpr tus tvs (TArr d r)
  | wtUVar : forall ts t, member (ts, t) tus ->
                          hlist (wtexpr tus tvs) ts -> wtexpr tus tvs t.
  Set Elimination Schemes.

  Arguments wtInj {_ _ _} _.
  Arguments wtVar {_ _ _} _.

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

  Section ind.
    Variable tus : list Tuvar.
    Variable P : forall tvs t, wtexpr tus tvs t -> Prop.
    Hypothesis Hvar : forall tvs t m, @P tvs t (wtVar m).
    Hypothesis Hinj : forall tvs t m, @P tvs t (wtInj m).
    Hypothesis Happ : forall tvs d c f x,
        @P tvs (TArr d c) f -> @P tvs d x -> @P tvs c (wtApp f x).
    Hypothesis Habs : forall tvs d c f,
        @P (d :: tvs) c f -> @P tvs (TArr d c) (wtAbs f).
    Hypothesis Huvar : forall tvs ts t (u : member (ts,t) tus) xs,
        hlist_Forall (@P tvs) xs ->
        @P tvs t (wtUVar u xs).
    Fixpoint wtexpr_ind {tvs t} (e : wtexpr tus tvs t)
    : P e :=
      match e as e in wtexpr _ _ t return P e with
      | wtVar v => Hvar v
      | wtInj f => Hinj _ f
      | wtApp f x => Happ (wtexpr_ind f) (wtexpr_ind x)
      | wtAbs f => Habs (wtexpr_ind f)
      | wtUVar u xs =>
        Huvar u ((fix rec {ls} (xs : hlist _ ls) {struct xs}
                  : hlist_Forall (@P tvs) xs :=
                    match xs as xs return hlist_Forall (@P tvs) xs with
                    | Hnil => hlist_Forall_nil
                    | Hcons x xs => hlist_Forall_cons (wtexpr_ind x) (rec xs)
                    end) _ xs)
      end.
  End ind.

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


  Section equiv.
    Context {tus : list Tuvar}.
    Variables R : forall tvs t, wtexpr tus tvs t -> wtexpr tus tvs t -> Prop.
    Unset Elimination Schemes.
    Inductive wtexpr_equiv (tvs : list type)
    : forall t, wtexpr tus tvs t -> wtexpr tus tvs t -> Prop :=
    | eqVar : forall {t} m, @wtexpr_equiv tvs t (wtVar m) (wtVar m)
    | eqInj : forall {t} f, @wtexpr_equiv tvs t (wtInj f) (wtInj f)
    | eqApp : forall d c f x g y,
        @wtexpr_equiv tvs (TArr d c) f g ->
        @wtexpr_equiv tvs d x y ->
        @wtexpr_equiv tvs c (wtApp f x) (wtApp g y)
    | eqAbs : forall d c f g,
        @wtexpr_equiv (d :: tvs) c f g ->
        @wtexpr_equiv tvs (TArr d c) (wtAbs f) (wtAbs g)
    | eqUVar : forall ts t (u : member (ts,t) tus) xs ys,
        hlist_Forall2 (@wtexpr_equiv tvs) xs ys ->
        @wtexpr_equiv tvs t (wtUVar u xs) (wtUVar u ys)
    | eqConv : forall t a b,
        @R tvs t a b ->
        @wtexpr_equiv tvs t a b
    | eqTrans : forall t a b c,
        @wtexpr_equiv tvs t a b ->
        @wtexpr_equiv tvs t b c ->
        @wtexpr_equiv tvs t a c.
    Set Elimination Schemes.

    Section wtexpr_equiv_ind.
      Variable P : forall tvs t (e1 e2 : wtexpr tus tvs t),
        @wtexpr_equiv tvs t e1 e2 -> Prop.
      Hypothesis Hvar : forall tvs t m,
          @P tvs t (wtVar m) (wtVar m) (eqVar m).
      Hypothesis Hinj : forall tvs t f,
          @P tvs t (wtInj f) (wtInj f) (eqInj _ f).
      Hypothesis Happ : forall tvs d c f f' x x' pf pf',
          @P tvs (TArr d c) f f' pf ->
          @P tvs d x x' pf' ->
          @P tvs c (wtApp f x) (wtApp f' x') (eqApp pf pf').
      Hypothesis Habs : forall tvs d c e e' pf,
          @P (d :: tvs) c e e' pf ->
          @P tvs (TArr d c) (wtAbs e) (wtAbs e') (eqAbs pf).
      Hypothesis Huvar : forall tvs ts t (u : member (ts,t) tus) xs xs'
                                (pfs : hlist_Forall2 (@wtexpr_equiv tvs) xs xs'),
          hlist_Forall2_dep (@P tvs) pfs ->
          @P tvs t (wtUVar u xs) (wtUVar u xs') (eqUVar u pfs).
      Hypothesis Hconv : forall tvs t a b pf,
          @P tvs t a b (eqConv pf).
      Hypothesis Htrans : forall tvs t a b c pf pf',
          @P tvs t a b pf ->
          @P tvs t b c pf' ->
          @P tvs t a c (eqTrans pf pf').

      Theorem wtexpr_equiv_ind : forall tvs t a b pf,
          @P tvs t a b pf.
      Proof.
        refine (fix rec (tvs : list type) (t : type) (a b : wtexpr tus tvs t)
                    (pf : wtexpr_equiv a b) {struct pf} : P pf :=
                  match pf as pf in @wtexpr_equiv _ t a b
                        return P pf
                  with
                  | eqVar _ => Hvar _
                  | eqInj _ _ => Hinj _ _
                  | eqApp l r => Happ (rec _ _ _ _ l) (rec _ _ _ _ r)
                  | eqAbs e => Habs (rec _ _ _ _ e)
                  | @eqUVar _ ts t u xs xs' pfs =>
                    Huvar _
                          ((fix rec' ls (xs xs' : hlist _ ls) (pfs : hlist_Forall2 (wtexpr_equiv (tvs:=tvs)) xs xs')
                                {struct pfs}
                            : hlist_Forall2_dep (P (tvs:=tvs)) pfs :=
                              match pfs as pfs in hlist_Forall2 _ _ _
                                    return hlist_Forall2_dep (P (tvs:=tvs)) pfs
                              with
                              | hlist_Forall2_nil _ => hlist_Forall2_dep_nil _
                              | hlist_Forall2_cons _ _ _ _ _ =>
                                hlist_Forall2_dep_cons _ _ _ _ (rec _ _ _ _ _) (rec' _ _ _ _)
                              end) ts _ _ _)
                  | eqConv r => Hconv r
                  | eqTrans a b => Htrans (rec _ _ _ _ a) (rec _ _ _ _ b)
                  end).
      Defined.

    End wtexpr_equiv_ind.

    Global Instance Reflexive_wtexpr_equiv : forall tvs t,
        Reflexive (@wtexpr_equiv tvs t).
    Proof.
      red.
      induction x; constructor; eauto.
      clear - H.
      induction H; constructor; eauto.
    Qed.

    Global Instance Symmetric_wtexpr_equiv :
      (forall tvs t, Symmetric (@R tvs t)) ->
      forall tvs t, Symmetric (@wtexpr_equiv tvs t).
    Proof using Tsymbol Esymbol R.
      induction 2; try solve [ constructor; eauto ].
      - constructor.
        clear - H0.
        induction H0; constructor; eauto.
      - constructor. symmetry. assumption.
      - eapply eqTrans; eauto.
    Qed.

    Global Instance Transitive_wtexpr_equiv : forall tvs t,
        Transitive (@wtexpr_equiv tvs t).
    Proof.
      red. eapply eqTrans.
    Qed.

  End equiv.

  Definition exprT (tus : list Tuvar) (tvs : list type) (t : Type) : Type :=
    hlist (fun tst => hlist typeD (fst tst) -> typeD (snd tst)) tus ->
    hlist typeD tvs ->
    t.

  Global Instance Applicative_exprT {tus tvs} : Applicative (exprT tus tvs) :=
  { pure := fun _ x _ _ => x
  ; ap   := fun _ _ f x us vs => (f us vs) (x us vs) }.

  Definition Pure_exprT {tus} {tvs} {t} (val : typeD t) : exprT tus tvs (typeD t) :=
    fun _ _ => val.
  Definition Ap_exprT {tus} {tvs} {d c} (f : exprT tus tvs (typeD (TArr d c)))
    (x : exprT tus tvs (typeD d)) : exprT tus tvs (typeD c) :=
    fun us vs => (f us vs) (x us vs).
  Definition Abs_exprT {tus} {tvs} {d c} (f : exprT tus (d :: tvs) (typeD c))
  : exprT tus tvs (typeD (TArr d c)) :=
    fun us vs x => f us (Hcons x vs).
  Definition Var_exprT {tus} {tvs} {t} (m : member t tvs) : exprT tus tvs (typeD t) :=
    fun _ => hlist_get m.
  Definition UVar_exprT {tus} {tvs} {ts} {t} (m : member (ts,t) tus)
             (es : hlist (fun t => exprT tus tvs (typeD t)) ts)
  : exprT tus tvs (typeD t) :=
    fun us vs =>
      let u := hlist_get m us in
      u (hlist_map (fun t (v : exprT tus tvs (typeD t)) => v us vs) es).

  Fixpoint wtexprD (tus : list Tuvar) (tvs : list type) (t : type)
           (e : wtexpr tus tvs t)
  : exprT tus tvs (typeD t) :=
    match e in wtexpr _ _ t return exprT tus tvs (typeD t) with
    | wtVar x => Var_exprT x
    | wtInj s => Pure_exprT (EsymbolD s)
    | wtApp f x => Ap_exprT (wtexprD f) (wtexprD x)
    | wtAbs e => Abs_exprT (wtexprD e)
    | wtUVar x es => UVar_exprT x (hlist_map (@wtexprD _ _) es)
    end.

  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

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
      Fixpoint member_weaken {ls} ls'
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


  Definition codom (t : type) : type :=
    match t with
    | TArr _ c => c
    | _ => t
    end.

  Definition dom (t : type) : type :=
    match t with
    | TArr d _ => d
    | _ => t
    end.

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

(*
  Fixpoint member_check_eq {tus} {ts ts' : list type} {t : type}
           (m1 : member (ts,t) tus)
  : forall m2 : member (ts',t) tus, {exists pf : ts' = ts,
                                        m1 = match pf with
                                             | eq_refl => m2
                                             end} +
                                    {ts' <> ts \/
                                     exists pf : ts' = ts,
                                       not (eq m1 match pf with
                                                  | eq_refl => m2
                                                  end)} :=
      match m1 in member _ tus
            return forall m2 : member (ts',t) tus,
                     {exists pf : ts' = ts,
                         m1 = match pf with
                              | eq_refl => m2
                              end} +
                     {ts' <> ts \/
                      exists pf : ts' = ts,
                        not (eq m1 match pf with
                                   | eq_refl => m2
                                   end)}
      with
      | MZ _ _ => fun m2 =>
        match m2 in member _ (x :: xs)
              return (ts,t) = x -> option (ts = ts')
        with
        | MZ _ _ => fun pf => Some (f_equal fst pf)
        | MN _ _ => fun _ => None
        end eq_refl
      | MN _ m1' => fun m2 =>
        match m2 in member _ (x :: xs)
              return _
        with
        | MZ _ _ => fun _ => None
        | MN _ m2' => fun rec => rec m2'
        end (fun m2' => @member_check_eq _ _ _ _ m1' m2')
      end.
*)

  Fixpoint member_check_eq {tus} {ts ts' : list type} {t : type}
           (m1 : member (ts,t) tus)
  : member (ts',t) tus -> option (ts = ts') :=
      match m1 in member _ tus
            return member (ts',t) tus -> option (ts = ts')
      with
      | MZ _ _ => fun m2 =>
        match m2 in member _ (x :: xs)
              return (ts,t) = x -> option (ts = ts')
        with
        | MZ _ _ => fun pf => Some (f_equal fst pf)
        | MN _ _ => fun _ => None
        end eq_refl
      | MN _ m1' => fun m2 =>
        match m2 in member _ (x :: xs)
              return _
        with
        | MZ _ _ => fun _ => None
        | MN _ m2' => fun rec => rec m2'
        end (fun m2' => @member_check_eq _ _ _ _ m1' m2')
      end.

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

  Lemma wtVar_inj : forall tus tvs t v v',
      @wtVar tus tvs t v = wtVar v' ->
      v = v'.
  Proof.
    do 4 intro.
    inversion 1.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply type_eq_dec.
  Defined.
  Lemma wtInj_inj : forall tus tvs t v v',
      @wtInj tus tvs t v = wtInj v' ->
      v = v'.
  Proof.
    do 4 intro.
    inversion 1.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply type_eq_dec.
  Defined.
  Lemma wtAbs_inj : forall tus tvs d c e e',
      @wtAbs tus tvs d c e = wtAbs e' ->
      e = e'.
  Proof.
    intros. inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    all: eapply type_eq_dec.
  Defined.
  Lemma wtApp_inj : forall tus tvs d c f f' x x',
      @wtApp tus tvs d c f x = wtApp f' x' ->
      f = f' /\ x = x'.
  Proof.
    intros; inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
    all: eapply type_eq_dec.
  Defined.
  Lemma wtUVar_inj : forall tus tvs ts t u u' xs xs',
      @wtUVar tus tvs ts t u xs = wtUVar u' xs' ->
      u = u' /\ xs = xs'.
  Proof.
    intros; inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
    all: try apply list_eq_dec; eapply type_eq_dec.
  Defined.

  Fixpoint wtexpr_eq_dec {tus tvs t} (a : wtexpr tus tvs t)
  : forall b, {a = b} + {a <> b}.
  refine
    match a as a in wtexpr _ _ t
          return forall b, {a = b} + {a <> b}
    with
    | wtVar v => fun b =>
      match b in wtexpr _ _ t'
            return forall x : member t' tvs,
          { wtVar x = b } + { wtVar x <> b }
      with
      | wtVar v' => fun v =>
        match member_eq_dec (T_dec:=type_eq_dec) v v' with
        | left pf => left _
        | right pf => right _
        end
      | _ => fun _ => right _
      end v
    | wtInj s => fun b =>
      match b in wtexpr _ _ t'
            return forall s : Esymbol t', { wtInj s = b } + { wtInj s <> b }
      with
      | wtInj s' => fun s => match Esymbol_eq_dec s s' with
                             | left pf => left (f_equal _ pf)
                             | right _ => right _
                             end
      | _ => fun _ => right _
      end s
    | @wtApp _ _ d c f x => fun b =>
      match b in wtexpr _ _ t'
            return forall (f : wtexpr _ _ (TArr d t'))
                          (x : wtexpr _ _ d),
          (forall f', {f = f'} + {f <> f'}) ->
          (forall x', {x = x'} + {x <> x'}) ->
          { wtApp f x = b } + { wtApp f x <> b }
      with
      | @wtApp _ _ d' c' f' x' => fun f x rec_f rec_x =>
        match type_eq_dec d' d with
        | left pf =>
          match rec_f match pf with
                      | eq_refl => f'
                      end
              , rec_x match pf with
                      | eq_refl => x'
                      end with
          | left pf , left pf' => left _
          | _ , _ => right _
          end
        | right _ => right _
        end
      | _ => fun _ _ _ _ => right _
      end f x
          (fun a => wtexpr_eq_dec _ _ _ f a)
          (fun a => wtexpr_eq_dec _ _ _ x a)
    | @wtAbs _ _ d c e => fun b =>
      match b as b in wtexpr _ _ t
            return forall e : wtexpr _ _ (codom t),
          (forall e', {e = e'} + {e <> e'}) ->
          {match t as t return wtexpr _ (dom t :: _) (codom t) -> wtexpr _ _ t -> Prop with
           | TArr _ _ => fun e b => wtAbs e = b
           | _ => fun _ _ => False
           end e b} + {match t as t return wtexpr _ (dom t :: _) (codom t) -> wtexpr _ _ t -> Prop with
                       | TArr _ _ => fun e b => (wtAbs e <> b)%type
                       | _ => fun _ _ => True
                       end e b}
      with
      | wtAbs e' => fun _ rec => match rec e' with
                                 | left pf => left _
                                 | right _ => right _
                                 end
      | _ => fun _ _ => right _
      end e (fun x => wtexpr_eq_dec _ _ _ e x)
    | @wtUVar _ _ ts t u xs => fun b =>
      match b as b in wtexpr _ _ t
            return forall (u : member (_,t) tus)
                          (xs : hlist (wtexpr tus tvs) _),
                      (forall xs', {xs = xs'} + {xs <> xs'}) ->
                      {wtUVar u xs = b} + {wtUVar u xs <> b}
      with
      | @wtUVar _ _ ts' t' u' xs' => fun u xs rec =>
        match list_eq_dec type_eq_dec ts' ts with
        | left pf =>
          match member_eq_dec u match pf with
                                | eq_refl => u'
                                end
              , rec match pf with
                    | eq_refl => xs'
                    end
          with
          | left _ , left _ => left _
          | _ , _ => right _
          end
        | right _ => right _
        end
      | _ => fun _ _ _ => right _
      end u xs (fun xs' => hlist_eq_dec (wtexpr_eq_dec _ _) xs xs')
    end; try solve [ clear; intro H; inversion H | subst; reflexivity | congruence ].
  - intro. eapply wtVar_inj in H. auto.
  - intro. eapply wtInj_inj in H. auto.
  - intro. subst. eapply wtApp_inj in H. tauto.
  - intro; subst. eapply wtApp_inj in H. tauto.
  - intro. inversion H. clear - n H1. congruence.
  - destruct t0; auto; clear. intro H; inversion H.
  - destruct t0; auto; clear. intro H; inversion H.
  - destruct t1; auto; clear. intro H; inversion H.
  - intro. eapply wtAbs_inj in H. tauto.
  - destruct t0; auto. clear; intro H; inversion H.
  - eapply pair_eq_dec. eapply list_eq_dec. eapply type_eq_dec. eapply type_eq_dec.
  - subst. intro. apply wtUVar_inj in H. tauto.
  - subst. intro. apply wtUVar_inj in H; tauto.
  - intro. inversion H. congruence.
  Defined.


  (** Lifting **)
  Fixpoint wtexpr_lift {tus tvs t} tvs' tvs'' (a : wtexpr tus (tvs'' ++ tvs) t)
  : wtexpr tus (tvs'' ++ tvs' ++ tvs) t :=
    match a in wtexpr _ _ t return wtexpr _ _ t with
    | wtVar v => wtVar (member_lift _ _ _ v)
    | wtApp f x => wtApp (wtexpr_lift tvs' tvs'' f)
                         (wtexpr_lift tvs' tvs'' x)
    | wtAbs e => wtAbs (wtexpr_lift tvs' (_ :: tvs'') e)
    | wtInj s => wtInj s
    | wtUVar u xs =>
      wtUVar u (hlist_map (fun t x => wtexpr_lift tvs' tvs'' x) xs)
    end.


  Fixpoint find_in_hlist {tus tvs ts t} (xs : hlist (wtexpr tus tvs) ts)
           (x : wtexpr tus tvs t) : option (wtexpr tus ts t) :=
    match xs in hlist _ ts
          return option (wtexpr tus ts t)
    with
    | Hnil => None
    | @Hcons _ _ t' _ x' xs =>
      match type_eq_dec t' t with
      | left pf =>
        if wtexpr_eq_dec x match pf with
                           | eq_refl => x'
                           end
        then Some match pf with
                  | eq_refl => wtVar (MZ _ _)
                  end
        else match find_in_hlist xs x with
             | Some e => Some (wtexpr_lift (_ :: nil) nil e)
             | None => None
             end
      | _ => match find_in_hlist xs x with
             | Some e => Some (wtexpr_lift (_ :: nil) nil e)
             | None => None
             end
      end
    end.

  Fixpoint pattern_expr {tus tvs t} (e : wtexpr tus tvs t)
           ts (xs : hlist (wtexpr tus tvs) ts)
  : option (wtexpr tus ts t) :=
    match find_in_hlist xs e with
    | Some res => Some res
    | None =>
      match e in wtexpr _ _ t
            return option (wtexpr tus ts t)
      with
      | wtVar v => None
      | wtInj f => Some (wtInj f)
      | wtApp f x => match pattern_expr f xs
                         , pattern_expr x xs
                     with
                     | Some a , Some b => Some (wtApp a b)
                     | _ , _ => None
                     end
      | @wtAbs _ _ d c e =>
        match pattern_expr e
                           (Hcons (wtVar (MZ _ _)) (hlist_map (fun t v => wtexpr_lift (d::nil) nil v) xs))
        with
        | Some e' => Some (wtAbs e')
        | None => None
        end
      | wtUVar _ _ => None
      end
    end.

  (** Full Subst **)
  Fixpoint subst {tus} {tvs tvs'} {t}
           (xs : hlist (wtexpr tus tvs) tvs')
           (e : wtexpr tus tvs' t)
  : wtexpr tus tvs t :=
    match e in wtexpr _ _ t return wtexpr tus tvs t
    with
    | wtVar v => hlist_get v xs
    | wtInj s => wtInj s
    | wtApp f x => wtApp (subst xs f) (subst xs x)
    | wtAbs e =>
      let xs' :=
          Hcons (wtVar (MZ _ _))
                (hlist_map (fun t e => @wtexpr_lift _ _ t (_ :: nil) nil e) xs)
      in wtAbs (subst xs' e)
    | wtUVar u ys => wtUVar u (hlist_map (fun t => subst xs) ys)
    end.

  (** Instantiation **)
  Fixpoint inst {tus tus'} {tvs} {t}
           (xs : hlist (fun tst => forall tvs,
                            hlist (wtexpr tus tvs) (fst tst) ->
                            wtexpr tus' tvs (snd tst)) tus)
           (e : wtexpr tus tvs t)
  : wtexpr tus' tvs t :=
    match e in wtexpr _ _ t return wtexpr tus' tvs t
    with
    | wtVar v => wtVar v
    | wtInj s => wtInj s
    | wtApp f x => wtApp (inst xs f) (inst xs x)
    | wtAbs e => wtAbs (inst xs e)
    | wtUVar u ys => hlist_get u xs _ ys
    end.

(*
  Definition Unifiable_eq {tus} s tvs t a b : Prop :=
    @Unifiable tus s tvs t a b \/ @Unifiable tus s tvs t b a.
*)

(*
  (** Unification **)
  Section unify.
    Variable Inst : list Tuvar -> Type.
    Variable Inst_lookup : forall {tus},
        Inst tus -> forall {ts t}, member (ts,t) tus ->
                                    option (wtexpr tus ts t).
    Variable Inst_set : forall {tus ts t},
        member (ts,t) tus -> wtexpr tus ts t -> Inst tus -> Inst tus.

    Inductive Unifiable {tus} (s : Inst tus) (tvs : list type) (t : type)
    : wtexpr tus tvs t -> wtexpr tus tvs t -> Prop :=
    | Unif_UVar : forall ts (u : member (ts,t) tus) xs e,
        Inst_lookup s u = Some e ->
        @Unifiable tus s tvs t (wtUVar u xs) (subst xs e).

    Definition Unifiable_eq {tus} s tvs t a b : Prop :=
      @Unifiable tus s tvs t a b \/ @Unifiable tus s tvs t b a.

    (** This is probably not an ideal definition **)
    Definition Inst_evolves {tus} (i1 i2 : Inst tus) : Prop :=
      forall tvs t (e1 e2 : wtexpr tus tvs t),
        wtexpr_equiv (Unifiable_eq i1) e1 e2 ->
        wtexpr_equiv (Unifiable_eq i2) e1 e2.

    Definition check_set {tus tvs} {ts t}
               (unify : wtexpr tus tvs t -> Inst tus -> option (Inst tus))
               (u : member (ts, t) tus) (xs : hlist (wtexpr tus tvs) ts)
               (e : wtexpr tus tvs t) (s : Inst tus)
    : option (Inst tus) :=
      match Inst_lookup s u with
      | None => match pattern_expr e xs with
                | None => None
                | Some e' => Some (Inst_set u e' s)
                end
      | Some e' => unify (subst xs e') s
      end.

    Definition unify_spec {tus} (i i' : Inst tus) {tvs t}
               (e1 e2 : wtexpr tus tvs t)
    : Prop :=
      Inst_evolves i i' /\ wtexpr_equiv (Unifiable_eq i') e1 e2.

    Lemma find_in_hlist_ok : forall tus R tvs ts t e xs e',
        @find_in_hlist tus tvs ts t xs e = Some e' ->
        wtexpr_equiv R e (subst xs e').
    Proof.
      induction xs; simpl; intros; try congruence.
      destruct (type_eq_dec l t); try congruence.
      subst.
      destruct (wtexpr_eq_dec e f).
      - inv_all; subst.
        simpl. eapply wtexpr_equiv_refl.
      - destruct (find_in_hlist xs e); try congruence.
        inv_all. subst.
        specialize (IHxs _ eq_refl).
        admit.
    Admitted.

    Lemma pattern_expr_ok : forall tus R tvs t e ts xs e',
        @pattern_expr tus tvs t e ts xs = Some e' ->
        wtexpr_equiv R e (subst xs e').
    Proof.
      admit.
    Admitted.

    Lemma check_set_ok : forall tus tvs ts t unify u xs e s s',
        @check_set tus tvs ts t unify u xs e s = Some s' ->
        (forall e' s s',
            unify e' s = Some s' ->
            unify_spec s s' e' e) ->
        unify_spec s s' (wtUVar u xs) e.
    Proof.
      unfold check_set; intros.
      consider (Inst_lookup s u).
      { intros. eapply H0 in H1.
        red. destruct H1; split; auto.
        assert (wtexpr_equiv (Unifiable_eq s) (wtUVar u xs) (subst xs w)).
        { econstructor. econstructor. econstructor. eassumption. }
        eapply H1 in H3.
        eapply eqTrans; eassumption. }
      { intro X; clear X.
        consider (pattern_expr e xs); intros; try congruence.
        inv_all. subst.
        eapply pattern_expr_ok with (R := Unifiable_eq (Inst_set u w s)) in H.
        split.
        { admit. }
        { eapply eqTrans.
          2: eapply wtexpr_equiv_symm; [| eassumption ].
          constructor. constructor. admit.
          destruct 1; [ right | left]; eassumption. } }
    Admitted.

    Section unify_list.
      Context {tus : list Tuvar} {tvs : list type}.
      Variable unify : forall {t}, wtexpr tus tvs t -> wtexpr tus tvs t ->
                                   Inst tus -> option (Inst tus).

      Fixpoint unify_list {ts} (e1 e2 : hlist (wtexpr tus tvs) ts)
               (s : Inst tus) {struct e1}
        : option (Inst tus) :=
        match e1 in hlist _ ts
              return hlist (wtexpr tus tvs) ts -> option (Inst tus)
        with
        | Hnil => fun _ => Some s
        | Hcons e1 es1 => fun e2 =>
                            match unify e1 (hlist_hd e2) s with
                            | Some s' => unify_list es1 (hlist_tl e2) s'
                            | None => None
                            end
        end e2.
    End unify_list.

    Variable unifyRec : forall {tus tvs t} (e1 e2 : wtexpr tus tvs t)
                               (s : Inst tus), option (Inst tus).



    Fixpoint unify {tus tvs t} (e1 e2 : wtexpr tus tvs t) (s : Inst tus)
             {struct e1}
      : option (Inst tus).
    refine
    (match e1 in wtexpr _ _ t
           return wtexpr tus tvs t -> option (Inst tus)
     with
     | wtVar x => fun e2 =>
                      match e2 in wtexpr _ _ t
                            return member t tvs -> option _
                      with
                      | wtVar y => fun x =>
                        match member_eq_dec (T_dec:=type_eq_dec) x y with
                        | left _ => Some s
                        | right _ => None
                        end
                      | wtUVar u xs => fun x =>
                                         check_set (unifyRec (wtVar x))
                                                   u xs (wtVar x) s
                      | _ => fun _ => None
                      end x
     | wtInj f => fun e2 =>
       match e2 in wtexpr _ _ t
             return Esymbol t -> option (Inst tus)
       with
       | wtInj f' => fun f => if Esymbol_eq_dec f f' then Some s else None
       | wtUVar u xs => fun f => check_set (unifyRec (wtInj f))
                                           u xs (wtInj f) s
       | _ => fun _ => None
       end f
     | @wtApp _ _ d c f x => fun e2 =>
       match e2 in wtexpr _ _ t
             return (forall tu, member (tu,t) tus ->
                                hlist (wtexpr tus tvs) tu ->
                                Inst tus -> option (Inst tus)) ->
             (wtexpr tus tvs (TArr d t) -> Inst tus -> option (Inst tus)) ->
                    option (Inst tus)
       with
       | @wtApp _ _ d' c' f' x' =>
         match type_eq_dec d' d with
         | left pf => fun _ rec =>
                        match rec match pf with
                                  | eq_refl => f'
                                  end s with
                        | Some s' => unify _ _ _ x match pf with
                                                   | eq_refl => x'
                                                   end s'
                        | None => None
                        end
         | _ => fun _ _ => None
         end
       | wtUVar u xs => fun cs _ => cs _ u xs s
       | _ => fun _ _ => None
       end (fun z (u : member (z,c) tus) xs s =>
              check_set (unifyRec (wtApp f x)) u xs (wtApp f x) s)
           (fun x => unify _ _ _ f x)
     | @wtAbs _ _ d r e => fun e2 =>
       match e2 in wtexpr _ _ t'
             return (forall tu, member (tu,t') tus ->
                                hlist (wtexpr tus tvs) tu ->
                                Inst tus -> option (Inst tus)) ->
                    (wtexpr tus (match t' with
                                 | TArr a _ => a
                                 | _ => t'
                                 end :: tvs) match t' with
                                             | TArr _ b => b
                                             | _ => t'
                                             end -> Inst tus -> option (Inst tus)) ->
                    option (Inst tus)
       with
       | @wtAbs _ _ d' r' e' =>
         match type_eq_dec d' d with
         | left pf => fun _ rec => rec match pf with
                                     | eq_refl => e'
                                     end s
         | right _ => fun _ _ => None
         end
       | wtUVar u xs => fun cs _ => cs _ u xs s
       | _ => fun _ _ => None
       end (fun (z : list type) (u : member (z,TArr d r) tus) xs s =>
              check_set (unifyRec (wtAbs e)) u xs (wtAbs e) s)
           (fun x => @unify _ _ _ e x)
     | @wtUVar _ _ ts t u xs => fun b =>
       match b in wtexpr _ _ t
             return member (ts,t) tus ->
                    hlist (wtexpr tus tvs) ts ->
                    option (Inst tus)
       with
       | wtUVar u' xs' => fun u xs =>
         match member_check_eq u' u with
         | Some pf => unify_list (@unify _ _) xs match pf with
                                                 | eq_refl => xs'
                                                 end s
         | None =>
           (** TODO: In reality, we should heuristic the order of this
            ** unification.
            **)
           check_set (fun e' s =>
                        check_set (unifyRec e')
                                  u' xs' e' s)
                     u xs (wtUVar u' xs') s
         end
       | x => fun u xs => check_set (unifyRec x) u xs x s
       end u xs
     end e2).
    Defined.

    Hypothesis unifyRec_ok : forall tus tvs t a b s s',
        @unifyRec tus tvs t a b s = Some s' ->
        unify_spec s s' a b.
    Theorem unify_ok : forall tus tvs t a b s s',
        @unify tus tvs t a b s = Some s' ->
        unify_spec s s' a b.
    Proof.
      (** By induction on [a]. Need to factor out some pieces to reduce
       ** the proof burden
       **)
    Admitted.

  End unify.
*)

End simple_dep_types.


(* Reduction Oriented Substitutions...
  (** Substitution **)
  Inductive Subst (tus : list Tuvar) : list type -> list type -> Type :=
  | Send : Subst tus nil nil
  | Sterm : forall {t ts ts'},
      wtexpr tus ts' t ->
      Subst tus ts ts' ->
      Subst tus (t :: ts) ts'
  | Sskip : forall {t ts ts'},
      Subst tus ts ts' ->
      Subst tus (t :: ts) (t :: ts').

  Section subst.
    Context {tus : list Tuvar}.

    Fixpoint Subst_get {ls ls' t} (s : Subst tus ls ls')
             (v : member t ls) : wtexpr tus ls' t.
    refine (
      match v in member _ ls
            return Subst tus ls ls' -> wtexpr tus ls' t
      with
      | MZ _ _ =>
        fun s => match s in Subst _ (t :: l) ls'
                       return wtexpr tus ls' t
                 with
                 | Sterm t _ => t
                 | Sskip _ => wtVar (MZ _ _)
                 end
      | MN _ _ => _
      end s).
    refine (fun s => match s in Subst _ (t' :: l) ls'
                           return wtexpr tus ls' t
                     with
                     | Sterm t _ => _
                     | Sskip _ => _
                     end).

  Fixpoint subst {tvs tvs' : list type} (s : Subst tus tvs tvs') {t}
           (e : wtexpr tus tvs t) {struct e}
  : wtexpr tus tvs' t.
  refine
    match e in wtexpr _ _ t return wtexpr tus tvs' t with
    | wtVar v => _
    | wtInj s => wtInj s
    | wtUVar u xs => wtUVar u (hlist_map (@subst tvs tvs' s) xs)
    | wtApp f x => wtApp (@subst tvs tvs' s _ f) (@subst tvs tvs' s _ x)
    | wtAbs f => wtAbs (@subst (_ :: tvs) (_ :: tvs') (Sskip s) _ f)
    end.
Print wtexpr.
*)
