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

  (** Unification **)
  Axiom Subst : list Tuvar -> Type.
  Axiom Subst_lookup : forall tus, Subst tus ->
                                   forall ts t, member (ts,t) tus -> option (wtexpr tus ts t).
  Axiom Subst_set : forall tus ts t, member (ts,t) tus -> wtexpr tus ts t ->
                                     Subst tus -> Subst tus.

  Axiom member_eq_dec : forall {T} ts (t : T) (a b : member t ts), {a = b} + {a <> b}.

  Parameter wtexpr_eq_dec : forall tus tvs t (a b : wtexpr tus tvs t), {a = b} + {a <> b}.

  Parameter wtexpr_lift : forall {tus tvs t} tvs', wtexpr tus tvs t -> wtexpr tus (tvs' ++ tvs) t.

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
                  | eq_refl => wtVar _ (MZ _ _)
                  end
        else match find_in_hlist xs x with
             | Some e => Some (wtexpr_lift (_ :: nil) e)
             | None => None
             end
      | _ => match find_in_hlist xs x with
             | Some e => Some (wtexpr_lift (_ :: nil) e)
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
      | wtVar _ _ => None
      | wtInj _ _ f => Some (wtInj _ _ f)
      | wtApp f x => match pattern_expr f xs
                         , pattern_expr x xs
                     with
                     | Some a , Some b => Some (wtApp a b)
                     | _ , _ => None
                     end
      | @wtAbs _ _ d c e =>
        match pattern_expr e
                           (hlist_map (fun t v => wtexpr_lift (d::nil) v) xs)
        with
        | Some e' => Some (wtAbs (wtexpr_lift (d::nil) e'))
        | None => None
        end
      | wtUVar _ _ => None
      end
    end.

  (** NOTE: This does not yet handle the actual unification **)
  Fixpoint unify {tus tvs t} (e1 e2 : wtexpr tus tvs t) (s : Subst tus) {struct e1}
  : option (Subst tus).
  refine
    (match e1 in wtexpr _ _ t
           return wtexpr tus tvs t -> option (Subst tus)
     with
     | wtVar _ x => fun e2 =>
                      match e2 in wtexpr _ _ t
                            return member t tvs -> option _
                      with
                      | wtVar _ y => fun x =>
                                       match member_eq_dec x y with
                                       | left _ => Some s
                                       | right _ => None
                                       end
                      | _ => fun _ => None
                      end x
     | wtInj _ _ f => fun e2 =>
       match e2 in wtexpr _ _ t
             return Esymbol t -> option (Subst tus)
       with
       | wtInj _ _ f' => fun f => if Esymbol_eq_dec f f' then Some s else None
       | _ => fun _ => None
       end f
     | @wtApp _ _ d c f x => fun e2 =>
       match e2 in wtexpr _ _ t
             return (wtexpr tus tvs (TArr d t) -> Subst tus -> option (Subst tus)) ->
                    option (Subst tus)
       with
       | @wtApp _ _ d' c' f' x' =>
         match type_eq_dec d' d with
         | left pf => fun rec =>
                        match rec match pf with
                                  | eq_refl => f'
                                  end s with
                        | Some s' => unify _ _ _ x match pf with
                                                   | eq_refl => x'
                                                   end s'
                        | None => None
                        end
         | _ => fun _ => None
         end
       | _ => fun _ => None
       end (unify _ _ _ f)
     | @wtAbs _ _ d r e => fun e2 =>
       match e2 in wtexpr _ _ t'
             return (wtexpr tus (match t' with
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
         | left pf => fun rec => rec match pf with
                                     | eq_refl => e'
                                     end s
         | right _ => fun _ => None
         end
       | _ => fun _ => None
       end (@unify _ _ _ e)
     | wtUVar t u => fun _ => None
     end e2).
  Defined.

End simple_dep_types.