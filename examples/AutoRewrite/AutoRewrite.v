Require Import MirrorCore.EProver2.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Util.Iteration.

(** TODO: Move [applicable] to a common place **)
Require Import MirrorCore.Examples.Auto.AutoProver2.

Set Implicit Arguments.
Set Strict Implicit.

Section exprs.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : SymI.RSym (typD ts) func.
  Variable RSymOk_func : RSymOk RSym_func.

  (** TODO: This should be generalized **)
  Let Expr_expr := @Expr_expr ts func RSym_func.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (** rewriting lemmas **)
  Definition lemma_rw := lemma typ (expr func) (typ * expr func * expr func).
  Definition lemma_rwD :=
    @lemmaD _ _ _ Expr_expr _
            (fun tus tvs (c : typ * expr func * expr func) =>
               let '(t,lhs,rhs) := c in
               match exprD' tus tvs lhs t
                   , exprD' tus tvs rhs t
               with
                 | Some l , Some r =>
                   Some (fun us vs => l us vs = r us vs)
                 | _ , _ => None
               end).

  Record Hints : Type :=
  { rewrites : list lemma_rw (** TODO: This can be a map from head symbols **)
  }.

  Variable hints : Hints.

  (** [applicable] should look like the following
   ** - a procedure to solves side conditions, i.e. an [EProver]
   ** - i can think of the unification as a side condition...
   ** - a procedure to call on success
   **)

  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr func).
  Variable SubstOk_subst : SubstOk _ Subst_subst.
  Variable SU : SubstUpdate subst (expr func).
  Variable SubstUpdateOk : SubstUpdateOk SU _.

  Require Import ExtLib.Structures.Monad.
  Require Import ExtLib.Data.Option.
  Require Import MirrorCore.Ext.ExprSubst.

  Section apply_rewrite.
    Variable prove : tenv typ -> tenv typ -> expr func -> subst -> option subst.

    Definition apply_rewrite_at (tus tvs : tenv typ) (under : nat) (r : typ)
               (e : expr func) (s : subst)
    : option (expr func * subst) :=
      first_success (fun lem =>
                       let '(t,lhs,rhs) := lem.(concl) in
                       let pattern := vars_to_uvars lhs 0 (length tus) in
                       let fuel := 100 in
                       match
                         ExprUnifySyntactic3.exprUnify
                           RSym_func Subst_subst SU fuel
                           (tus ++ vars lem) tvs 0 s pattern e t
                       with
                         | Some s' =>
                           bind (all_success
                                   (prove (tus ++ lem.(vars)) tvs)
                                   lem.(premises)
                                   s')
                                (fun s' =>
                                   let insts :=
                                       instantiate (fun u => lookup u s') 0 (vars_to_uvars rhs 0 (length tus))
                                   in
                                   ret (insts, s'))
                         | None => None
                       end) hints.(rewrites).
  End apply_rewrite.

  Section typed_fold.
    Variable T : Type.
    Variable atom : tenv typ -> typ -> expr func -> T.
    Variable abs : tenv typ -> typ -> typ -> T -> T.
    Variable app : tenv typ -> typ -> typ -> T -> T -> T.

    Variable tus : tenv typ.
    Fixpoint typed_foldr (tvs : tenv typ) (e : expr func) (t : typ) : T :=
      match e with
        | App f x =>
          match typeof_expr tus tvs x with
            | None => atom tvs t e
            | Some d =>
              app tvs d t
                  (typed_foldr tvs f (tyArr d t))
                  (typed_foldr tvs x d)
          end
        | Abs d e =>
          match t with
            | tyArr _ r =>
              abs tvs d r (typed_foldr (t :: tvs) e r)
            | _ => atom tvs t (Abs d e)
          end
        | e => atom tvs t e
      end.
  End typed_fold.

  Variable prove : tenv typ -> tenv typ -> expr func -> subst -> option subst.

  Definition rewrite_bu (tus tvs : tenv typ) (e : expr func) (t : typ) (s : subst)
  : bool * expr func * subst :=
    @typed_foldr
      (nat -> subst -> bool * expr func * subst)%type
      (fun tvs t e under s =>
         match apply_rewrite_at prove tus tvs under t e s with
           | None => (false, e, s)
           | Some (e,s) => (true, e, s)
         end)
      (fun tvs d r rr under s =>
         (** TODO: what are the requirements for rewriting under functions **)
         let '(p,rr,sr) := rr (S under) s in
         match apply_rewrite_at prove tus tvs under (tyArr d r) rr sr with
           | None => (p, rr, s)
           | Some (e,s) => (true, e, s)
         end)
      (fun tvs d r rf rx under s =>
         let '(pf,rf,sf) := rf under s in
         let '(px,rx,sx) := rx under sf in
         match apply_rewrite_at prove tus tvs under r (App rf rx) sx with
           | None => (orb pf px, App rf rx, sx)
           | Some (e,s) => (true, e, s)
         end)
      tus tvs e t 0 s.
End exprs.
