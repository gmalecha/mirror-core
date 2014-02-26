Require Import Coq.FSets.FMapPositive.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Subst2.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Import FMapPositive.PositiveMap.

  Let uvar := nat.
  Variables typ expr : Type.
  Variable typD : list Type -> typ -> Type.
  Variable Expr_expr : @Expr typ typD expr.

  Variable mentionsU : expr -> uvar -> Prop.

  Definition pmap := t.
  Definition pset := pmap unit.
  Definition In_pset (p : positive) (s : pset) : Prop :=
    find p s = Some tt.

  Fixpoint pset_union (a b : pset) : pset :=
    match a , b with
      | Leaf , x => x
      | x , Leaf => x
      | Node la a ra , Node lb b rb =>
        Node (pset_union la lb) (match a , b with
                                   | None , None => None
                                   | _ , _ => Some tt
                                 end) (pset_union ra rb)
    end.

  Record fast_subst : Type :=
  { subst : pmap expr
  ; open : pmap pset
  }.

  Definition WellFormed_fast_subst (fs : fast_subst) : Prop :=
    (forall p e,
       find p fs.(subst) = Some e ->
       forall u s,
         mentionsU e (Pos.to_nat u) ->
         find u fs.(open) = Some s ->
         In_pset p s).

  Variable get_mentions_instantiate : (uvar -> option expr) -> expr -> pset * expr.
  Variable instantiate : (uvar -> option expr) -> expr -> expr.

  Definition to_key : nat -> positive := fun x => Pos.of_nat (S x).

  Definition fast_subst_lookup (u : uvar) (s : fast_subst) : option expr :=
    find (to_key u) s.(subst).

  Let RelDec_eq_uvar : RelDec (@eq uvar) := RelDec_eq.
  Local Existing Instance RelDec_eq_uvar.

  Definition fast_subst_set (u : uvar) (e : expr) (s : fast_subst)
  : option fast_subst :=
    let up := to_key u in
    match @get_mentions_instantiate (fun u => find (to_key u) s.(subst)) e with
      | (opens, e_inst) =>
        if find up opens then None
        else
          Some (fold (fun p _ acc =>
                        (** uvar p mentions u **)
                        match find p s.(subst) with
                          | None => (** dead code **) acc
                          | Some e =>
                            {| subst :=
                                 add p (instantiate (fun x => if x ?[ eq ] u then
                                                                Some e_inst
                                                              else None) e) acc.(subst)
                             ; open :=
                                 (** TODO: this should be done with modify **)
                                 add p match find p acc.(open) with
                                         | None => opens
                                         | Some opens' =>
                                           remove up (pset_union opens opens')
                                       end acc.(open)
                            |}
                        end)
                     (match find up s.(open) with
                        | None => empty _
                        | Some x => x
                      end) {| subst := add up e_inst s.(subst)
                            ; open := add up opens s.(open) |})
    end.

  Definition fast_subst_empty : fast_subst :=
    {| subst := empty _ ; open := empty _ |}.

  Fixpoint fast_subst_pull' (base : positive) (n : nat) (fs : fast_subst) {struct n}
  : option (fast_subst * list expr) :=
    match n with
      | 0 => Some (fs, nil)
      | S n =>
        match find base fs.(subst) with
          | None => None
          | Some x =>
            fast_subst_pull' (Pos.succ base) n {| subst := remove base fs.(subst)
                                                ; open := fs.(open) |}
        end
    end.

  Definition fast_subst_pull (base : uvar) := fast_subst_pull' (to_key base).

  Instance Subst_fast_subst : Subst fast_subst expr :=
    fast_subst_lookup.

  Instance SubstUpdate_fast_subst : SubstUpdate fast_subst expr :=
  { empty := fast_subst_empty
  ; pull := fast_subst_pull
  ; set := fast_subst_set
  }.

(**
    let zs :=  in
    let opens := fold (fun p _ acc =>
                         match find p s.(open) with
                           | None => acc
                           | Some acc' => pset_join acc acc'
                         end) (get_mentions e) pset_empty in
**)
End parametric.

(** For Expr **)
Section funced.
  Require Import MirrorCore.Ext.ExprCore.
  Require Import MirrorCore.Ext.ExprSubst.

  Variable func : Type.

  Definition instantiate : (uvar -> option (expr func)) -> expr func -> expr func :=
    fun z => ExprSubst.instantiate z 0.

  Fixpoint get_mentions (e : expr func) (acc : pset) : pset :=
    match e with
      | Var _
      | Inj _ => acc
      | App l r => get_mentions l (get_mentions r acc)
      | Abs _ e => get_mentions e acc
      | UVar u => PositiveMap.add (Pos.of_nat (S u)) tt acc
    end.

  Definition get_mentions_instantiate (i : uvar -> option (expr func)) (e : expr func)
  : pset * expr func :=
    let e' := instantiate i e in
    (get_mentions e' (PositiveMap.empty _), e').

(*
  Definition l := @fast_subst_lookup (expr func).
  Definition e := @fast_subst_empty (expr func).
  Definition s := @fast_subst_set (expr func) get_mentions_instantiate instantiate.

  Check s.

  Require Import ExtLib.Structures.Monad.
  Require Import ExtLib.Data.Monads.OptionMonad.

  Eval compute in bind (s 0 (Inj 0) e) (l 0).
*)

End funced.
