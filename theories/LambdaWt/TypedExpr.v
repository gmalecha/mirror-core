Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.

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

  (** TODO: If we move to a stronger notion of types, e.g. with reduction,
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
  Inductive wtexpr (tus : list Tuvar) (tvs : list type) : type -> Type :=
  | wtVar : forall t, member t tvs -> wtexpr tus tvs t
  | wtInj : forall t, Esymbol t -> wtexpr tus tvs t
  | wtApp : forall d r, wtexpr tus tvs (TArr d r) ->
                        wtexpr tus tvs d -> wtexpr tus tvs r
  | wtAbs : forall d r, wtexpr tus (d :: tvs) r -> wtexpr tus tvs (TArr d r)
  | wtUVar : forall ts t, member (ts, t) tus ->
                          hlist (wtexpr tus tvs) ts -> wtexpr tus tvs t.

  Definition exprT (tus : list Tuvar) (tvs : list type) (t : type) : Type :=
    hlist (fun tst => let '(ts,t) := tst in  hlist typeD ts -> typeD t) tus ->
    hlist typeD tvs ->
    typeD t.

  Definition Pure_exprT {tus} {tvs} {t} (val : typeD t) : exprT tus tvs t :=
    fun _ _ => val.
  Definition Ap_exprT {tus} {tvs} {d c} (f : exprT tus tvs (TArr d c))
    (x : exprT tus tvs d) : exprT tus tvs c :=
    fun us vs => (f us vs) (x us vs).
  Definition Abs_exprT {tus} {tvs} {d c} (f : exprT tus (d :: tvs) c)
  : exprT tus tvs (TArr d c) :=
    fun us vs x => f us (Hcons x vs).
  Definition Var_exprT {tus} {tvs} {t} (m : member t tvs) : exprT tus tvs t :=
    fun _ => hlist_get m.
  Definition UVar_exprT {tus} {tvs} {ts} {t} (m : member (ts,t) tus)
             (es : hlist (exprT tus tvs) ts)
  : exprT tus tvs t :=
    fun us vs =>
      let u := hlist_get m us in
      u (hlist_map (fun t (v : exprT tus tvs t) => v us vs) es).

  Fixpoint wtexprD (tus : list Tuvar) (tvs : list type) (t : type)
           (e : wtexpr tus tvs t)
  : exprT tus tvs t :=
    match e in wtexpr _ _ t return exprT tus tvs t with
    | wtVar _ x => Var_exprT x
    | wtInj _ _ s => Pure_exprT (EsymbolD s)
    | wtApp f x => Ap_exprT (wtexprD f) (wtexprD x)
    | wtAbs e => Abs_exprT (wtexprD e)
    | wtUVar x es => UVar_exprT x (hlist_map (@wtexprD _ _) es)
    end.

  Variable Esymbol_eq_dec : forall {t} (a b : Esymbol t), {a = b} + {a <> b}.

  (** * Auxiliary Functions **)

  Require Import ExtLib.Tactics.

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

  Arguments wtInj {_ _ _} _.
  Arguments wtVar {_ _ _} _.

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
                           (hlist_map (fun t v => wtexpr_lift (d::nil) nil v) xs)
        with
        | Some e' => Some (wtAbs (wtexpr_lift (d::nil) nil e'))
        | None => None
        end
      | wtUVar _ _ => None
      end
    end.

  (** Substitution **)
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

  (** Unification **)
  Section unify.
    Variable Subst : list Tuvar -> Type.
    Variable Subst_lookup : forall {tus},
        Subst tus -> forall {ts t}, member (ts,t) tus ->
                                    option (wtexpr tus ts t).
    Variable Subst_set : forall {tus ts t},
        member (ts,t) tus -> wtexpr tus ts t -> Subst tus -> Subst tus.

    Definition check_set {tus tvs} {ts t}
               (unify : wtexpr tus tvs t -> Subst tus -> option (Subst tus))
               (u : member (ts, t) tus) (xs : hlist (wtexpr tus tvs) ts)
               (e : wtexpr tus tvs t) (s : Subst tus)
    : option (Subst tus) :=
      match Subst_lookup s u with
      | None => match pattern_expr e xs with
                | None => None
                | Some e' => Some (Subst_set u e' s)
                end
      | Some e' => unify (subst xs e') s
      end.

    Section unify_list.
      Context {tus : list Tuvar} {tvs : list type}.
      Variable unify : forall {t}, wtexpr tus tvs t -> wtexpr tus tvs t ->
                                   Subst tus -> option (Subst tus).

      Fixpoint unify_list {ts} (e1 e2 : hlist (wtexpr tus tvs) ts)
               (s : Subst tus) {struct e1}
        : option (Subst tus) :=
        match e1 in hlist _ ts
              return hlist (wtexpr tus tvs) ts -> option (Subst tus)
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
                               (s : Subst tus), option (Subst tus).



  Fixpoint unify {tus tvs t} (e1 e2 : wtexpr tus tvs t) (s : Subst tus)
           {struct e1}
  : option (Subst tus).
  refine
    (match e1 in wtexpr _ _ t
           return wtexpr tus tvs t -> option (Subst tus)
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
             return Esymbol t -> option (Subst tus)
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
                                Subst tus -> option (Subst tus)) ->
             (wtexpr tus tvs (TArr d t) -> Subst tus -> option (Subst tus)) ->
                    option (Subst tus)
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
                                Subst tus -> option (Subst tus)) ->
                    (wtexpr tus (match t' with
                                 | TArr a _ => a
                                 | _ => t'
                                 end :: tvs) match t' with
                                             | TArr _ b => b
                                             | _ => t'
                                             end -> Subst tus -> option (Subst tus)) ->
                    option (Subst tus)
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
                    option (Subst tus)
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

  End unify.

End simple_dep_types.