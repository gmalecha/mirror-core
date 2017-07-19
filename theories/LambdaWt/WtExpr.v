Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.DepUtil.
Require Import MirrorCore.LambdaWt.WtType.

Set Implicit Arguments.
Set Strict Implicit.

(* This is the universe of the reified language *)
Universe Urefl.

Section simple_dep_types.
  Variable Tsymbol : Type.
  Variable TsymbolD : Tsymbol -> Type@{Urefl}.

  Variable Tsymbol_eq_dec : forall a b : Tsymbol, {a = b} + {a <> b}.

  Variable Esymbol : type Tsymbol -> Type.
  Variable EsymbolD : forall t, Esymbol t -> typeD TsymbolD t.

  Definition Tuvar : Type := list (type Tsymbol) * type Tsymbol.

  (** A guaranteed well-typed expr **)
  Unset Elimination Schemes.
  Inductive wtexpr (tus : list Tuvar) (tvs : list (type Tsymbol))
  : type Tsymbol -> Type :=
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

  Section ind_app.
    Variable tus : list Tuvar.
    Variable tvs : list (type Tsymbol).
    Variable P : forall tvs' t, wtexpr tus (tvs' ++ tvs) t -> Prop.
    Hypothesis Hvar : forall tvs t m, @P tvs t (wtVar m).
    Hypothesis Hinj : forall tvs t m, @P tvs t (wtInj m).
    Hypothesis Happ : forall tvs d c f x,
        @P tvs (TArr d c) f -> @P tvs d x -> @P tvs c (wtApp f x).
    Hypothesis Habs : forall tvs d c f,
        @P (d :: tvs) c f -> @P tvs (TArr d c) (wtAbs f).
    Hypothesis Huvar : forall tvs ts t (u : member (ts,t) tus) xs,
        hlist_Forall (@P tvs) xs ->
        @P tvs t (wtUVar u xs).
    Fixpoint wtexpr_ind_app {tvs' t} (e : wtexpr tus (tvs' ++ tvs) t)
    : P _ e :=
      match e as e in wtexpr _ _ t return P tvs' e with
      | wtVar v => Hvar _ v
      | wtInj f => Hinj _ f
      | wtApp f x => Happ (wtexpr_ind_app f) (wtexpr_ind_app x)
      | wtAbs f => Habs (@wtexpr_ind_app (_ :: tvs') _ f)
      | wtUVar u xs =>
        Huvar u ((fix rec {ls} (xs : hlist _ ls) {struct xs}
                  : hlist_Forall (@P tvs') xs :=
                    match xs as xs return hlist_Forall (@P tvs') xs with
                    | Hnil => hlist_Forall_nil
                    | Hcons x xs => hlist_Forall_cons (wtexpr_ind_app x) (rec xs)
                    end) _ xs)
      end.
  End ind_app.

  Section equiv.
    Context {tus : list Tuvar}.
    Variables R : forall tvs t, wtexpr tus tvs t -> wtexpr tus tvs t -> Prop.
    Unset Elimination Schemes.
    Inductive wtexpr_equiv (tvs : list (type Tsymbol))
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
        refine (fix rec (tvs : list (type Tsymbol))
                    (t : type Tsymbol) (a b : wtexpr tus tvs t)
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

  Definition Uenv : list Tuvar -> Type :=
    hlist (fun tst => hlist (typeD TsymbolD) (fst tst) ->
                      typeD TsymbolD (snd tst)).

  Definition Venv : list (type Tsymbol) -> Type :=
    hlist (typeD TsymbolD).

  Definition exprT (tus : list Tuvar) (tvs : list (type Tsymbol)) (t : Type)
  : Type :=
    Uenv tus -> Venv tvs -> t.

  Global Instance Applicative_exprT {tus tvs} : Applicative (exprT tus tvs) :=
  { pure := fun _ x _ _ => x
  ; ap   := fun _ _ f x us vs => (f us vs) (x us vs) }.

  Definition Pure_exprT {tus} {tvs} {t} (val : typeD TsymbolD t)
  : exprT tus tvs (typeD TsymbolD t) :=
    fun _ _ => val.
  Definition Ap_exprT {tus} {tvs} {d c} (f : exprT tus tvs (typeD TsymbolD (TArr d c)))
    (x : exprT tus tvs (typeD TsymbolD d)) : exprT tus tvs (typeD TsymbolD c) :=
    fun us vs => (f us vs) (x us vs).
  Definition Abs_exprT {tus} {tvs} {d c} (f : exprT tus (d :: tvs) (typeD TsymbolD c))
  : exprT tus tvs (typeD TsymbolD (TArr d c)) :=
    fun us vs x => f us (Hcons x vs).
  Definition Var_exprT {tus} {tvs} {t} (m : member t tvs)
  : exprT tus tvs (typeD TsymbolD t) :=
    fun _ => hlist_get m.
  Definition UVar_exprT {tus} {tvs} {ts} {t} (m : member (ts,t) tus)
             (es : hlist (fun t => exprT tus tvs (typeD TsymbolD t)) ts)
  : exprT tus tvs (typeD TsymbolD t) :=
    fun us vs =>
      let u := hlist_get m us in
      u (hlist_map (fun t (v : exprT tus tvs (typeD TsymbolD t)) => v us vs) es).

  Fixpoint wtexprD (tus : list Tuvar) (tvs : list (type Tsymbol)) (t : type Tsymbol)
           (e : wtexpr tus tvs t)
  : exprT tus tvs (typeD TsymbolD t) :=
    match e in wtexpr _ _ t return exprT tus tvs (typeD _ t) with
    | wtVar x => Var_exprT x
    | wtInj s => Pure_exprT (EsymbolD s)
    | wtApp f x => Ap_exprT (wtexprD f) (wtexprD x)
    | wtAbs e => Abs_exprT (wtexprD e)
    | wtUVar x es => UVar_exprT x (hlist_map (@wtexprD _ _) es)
    end.

  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  Fixpoint member_check_eq {tus} {ts ts' : list (type Tsymbol)}
           {t : type Tsymbol}
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

  Lemma wtVar_inj : forall tus tvs t v v',
      @wtVar tus tvs t v = wtVar v' ->
      v = v'.
  Proof.
    do 4 intro.
    inversion 1.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply type_eq_dec.
    eapply Tsymbol_eq_dec.
  Defined.
  Lemma wtInj_inj : forall tus tvs t v v',
      @wtInj tus tvs t v = wtInj v' ->
      v = v'.
  Proof.
    do 4 intro.
    inversion 1.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply type_eq_dec.
    eapply Tsymbol_eq_dec.
  Defined.
  Lemma wtAbs_inj : forall tus tvs d c e e',
      @wtAbs tus tvs d c e = wtAbs e' ->
      e = e'.
  Proof.
    intros. inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    all: eapply type_eq_dec; eapply Tsymbol_eq_dec.
  Defined.
  Lemma wtApp_inj : forall tus tvs d c f f' x x',
      @wtApp tus tvs d c f x = wtApp f' x' ->
      f = f' /\ x = x'.
  Proof.
    intros; inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
    all: eapply type_eq_dec; eapply Tsymbol_eq_dec.
  Defined.
  Lemma wtUVar_inj : forall tus tvs ts t u u' xs xs',
      @wtUVar tus tvs ts t u xs = wtUVar u' xs' ->
      u = u' /\ xs = xs'.
  Proof.
    intros; inversion H.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H1; auto.
    eapply Eqdep_dec.inj_pair2_eq_dec in H2; auto.
    all: try apply List.list_eq_dec; eapply type_eq_dec; eapply Tsymbol_eq_dec.
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
        match member_eq_dec (T_dec:=type_eq_dec Tsymbol_eq_dec) v v' with
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
        match type_eq_dec Tsymbol_eq_dec d' d with
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
        match List.list_eq_dec (type_eq_dec Tsymbol_eq_dec) ts' ts with
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
  - destruct t0; auto; clear. intro H; inversion H.
  - destruct t0; auto; clear. intro H; inversion H.
  - destruct t1; auto; clear. intro H; inversion H.
  - intro. eapply wtAbs_inj in H. tauto.
  - destruct t0; auto. clear; intro H; inversion H.
  - eapply pair_eq_dec; try eapply List.list_eq_dec; eapply type_eq_dec; eapply Tsymbol_eq_dec.
  - subst. intro. apply wtUVar_inj in H. tauto.
  - subst. intro. apply wtUVar_inj in H; tauto.
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

  Definition wtexpr_jeq_dec {us vs} {a b : type Tsymbol}
             (t1 : wtexpr us vs a) (t2 : wtexpr us vs b)
  : { exists pf : a = b , match pf with
                     | eq_refl => t1
                     end = t2 } + { True }.
  refine
    match type_eq_dec Tsymbol_eq_dec a b with
    | left pf => match wtexpr_eq_dec match pf with
                                    | eq_refl => t1
                                    end t2 with
                | left pf' => left (@ex_intro _ _ pf pf')
                | _ => right I
                end
    | right pf => right I
    end.
  Defined.

  Fixpoint pattern_expr {tus tvs t} (e : wtexpr tus tvs t)
           ts (xs : hlist (wtexpr tus tvs) ts)
  : option (wtexpr tus ts t) :=
    match find_in_hlist (fun t (e' : wtexpr _ _ t) =>
                           match wtexpr_jeq_dec e e' with
                           | left pf => Some match pf with
                                            | ex_intro _ y _ => y
                                            end
                           | right _ => None
                           end) xs (wtVar)
    with
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

  Lemma wtexprD_wtexpr_lift
  : forall tus tvs tvs' tvs'' t (e : wtexpr tus (tvs'' ++ tvs) t),
      forall us (vs : Venv tvs) (vs' : Venv tvs') (vs'' : Venv tvs''),
        wtexprD (wtexpr_lift tvs' tvs'' e) us (hlist_app vs'' (hlist_app vs' vs)) = wtexprD e us (hlist_app vs'' vs).
  Proof using.
    clear. intros tus tvs tvs' tvs'' t.
    intro.
    eapply wtexpr_ind_app with (e:=e); simpl; intros.
    { unfold Var_exprT.
      eapply hlist_get_member_lift. }
    { unfold Pure_exprT. reflexivity. }
    { unfold Ap_exprT.
      rewrite (H us vs vs' vs'').
      rewrite (H0 us vs vs' vs''). reflexivity. }
    { unfold Abs_exprT.
      eapply FunctionalExtensionality.functional_extensionality.
      intros.
      eapply (H us vs vs' (Hcons x vs'')). }
    { unfold UVar_exprT.
      repeat rewrite hlist_map_hlist_map.
      f_equal.
      clear - H.
      induction H.
      - reflexivity.
      - simpl. f_equal; eauto. }
  Qed.

  Lemma wtexprD_subst
  : forall tus tvs t
           (e : wtexpr tus tvs t)
           tvs'
           (hl : hlist (wtexpr tus tvs') tvs),
      forall us vs,
        wtexprD (@subst tus tvs' tvs t hl e) us vs =
        (wtexprD e) us (hlist_map (fun _ e => wtexprD e us vs) hl).
  Proof.
    induction e; simpl; intros.
    { unfold Var_exprT. rewrite hlist_get_hlist_map. reflexivity. }
    { reflexivity. }
    { unfold Ap_exprT. rewrite <- IHe1. rewrite <- IHe2. reflexivity. }
    { unfold Abs_exprT.
      eapply FunctionalExtensionality.functional_extensionality.
      intros. rewrite IHe. simpl. rewrite hlist_map_hlist_map.
      f_equal. f_equal.
      eapply hlist_map_ext.
      intros.
      eapply wtexprD_wtexpr_lift with (vs'' := Hnil) (vs' := Hcons x Hnil) (vs:=vs). }
    { unfold UVar_exprT. f_equal.
      repeat rewrite hlist_map_hlist_map.
      clear - H.
      induction H; simpl.
      - reflexivity.
      - f_equal; eauto. }
  Qed.

  Lemma subst_wtexpr_lift
  : forall (tus : list Tuvar)
           (tvs tvs'' : list (type Tsymbol)) (t : type Tsymbol)
           (e : wtexpr tus (tvs ++ tvs'') t) tvs' Z,
    forall (vs : hlist _ tvs) (vs' : hlist _ tvs') (vs'' : hlist _ tvs''),
      subst (hlist_app vs (hlist_app vs' vs''))
            (wtexpr_lift tvs' tvs e) =
      subst (tvs:=Z) (hlist_app vs vs'') e.
  Proof.
    clear.
    intros tus tvs tvs'' t e.
    eapply wtexpr_ind_app with (e:=e); simpl; intros; auto.
    { rewrite hlist_get_member_lift. reflexivity. }
    { rewrite H. rewrite H0. reflexivity. }
    { f_equal.
      remember (fun (t0 : type Tsymbol)
                    (e0 : wtexpr tus Z t0) =>
                  wtexpr_lift (d :: nil) nil e0).
      specialize (H tvs' _ (Hcons (wtVar (MZ d Z))
                                  (hlist_map w vs))
                    (hlist_map w vs') (hlist_map w vs'')). simpl in H.
      repeat rewrite hlist_app_hlist_map.
      eauto. }
    { rewrite hlist_map_hlist_map. f_equal.
      clear - H.
      induction H; simpl; eauto.
      f_equal; eauto. }
  Qed.

End simple_dep_types.

Arguments wtVar {_ _ _} [_ _] _.
Arguments wtInj {_ _ _} [_ _] _.

Export WtType.

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
