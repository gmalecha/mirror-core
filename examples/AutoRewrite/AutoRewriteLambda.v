Require Import ExtLib.Data.Fun.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.SubstI3.
(*Require Import MirrorCore.Ext.Expr. *)
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprUnify.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Util.Iteration.

(*
(** TODO: Move [applicable] to a common place **)
Require Import McExamples.Auto.AutoProver2.
*)

Set Implicit Arguments.
Set Strict Implicit.

Section exprs.
  Variable func : Type.
  Variable RType_typ : RType.
  Variable Typ2_typ : Typ2 _ Fun.
  Variable RSym_func : RSym typD func.
  Variable RSymOk_func : RSymOk RSym_func.

  (** TODO: Can this be further generalized? *)
  Let Expr_expr := @Expr_expr func _ _ RSym_func.
  Local Existing Instance Expr_expr.
  Local Existing Instance ExprOk_expr.

  (** rewriting lemmas **)
  Record Eqn :=
  { type : typ
  ; lhs : expr typ func
  ; rhs : expr typ func
  }.

  Definition lemma_rw :=
    lemma typ (expr typ func) Eqn.

  Definition lemma_rwD :=
    @lemmaD _ _ _ Expr_expr _
            (fun tus tvs (c : Eqn) =>
               let '{| type := t ; lhs := lhs ; rhs := rhs |} := c in
               match exprD' nil tus tvs t lhs
                   , exprD' nil tus tvs t rhs
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
  Variable Subst_subst : Subst subst (expr typ func).
  Variable SubstOk_subst : SubstOk _ Subst_subst.
  Variable SU : SubstUpdate subst (expr typ func).
  Variable SubstUpdateOk : SubstUpdateOk SU _.

  Require Import ExtLib.Structures.Monad.
  Require Import ExtLib.Data.Option.
(*  Require Import MirrorCore.Ext.ExprSubst. *)

  Section apply_rewrite.
    Variable prove : tenv typ -> tenv typ -> expr typ func -> subst -> option subst.

    Definition apply_rewrite_at (tus tvs : tenv typ) (under : nat) (r : typ)
               (e : expr typ func) (s : subst)
    : option (expr typ func * subst) :=
      first_success (fun lem =>
                       let '{| type := t ; lhs := lhs ; rhs := rhs |} :=
                           lem.(concl)
                       in
                       let pattern := vars_to_uvars 0 (length tus) lhs in
                       let fuel := 100 in
                       match
                         ExprUnify.exprUnify
                           _ RSym_func Subst_subst SU fuel
                           nil (tus ++ vars lem) tvs 0 s pattern e t
                       with
                         | Some s' =>
                           match all_success
                                   (prove (tus ++ lem.(vars)) tvs)
                                   lem.(premises) s'
                           with
                             | Some s' =>
                               let insts :=
                                   instantiate (fun u => lookup u s') 0
                                               (vars_to_uvars 0 (length tus) rhs)
                               in
                               Some (insts, s')
                             | None => None
                           end
                         | None => None
                       end) hints.(rewrites).
  End apply_rewrite.

  (** TODO(gmalecha): Use the implementation inside Lambda **)
  Section typed_fold.
    Variable T : Type.
    Variable atom : tenv typ -> typ -> expr typ func -> T.
    Variable abs : tenv typ -> typ -> typ -> T -> T.
    Variable app : tenv typ -> typ -> typ -> T -> T -> T.

    Variable tus : tenv typ.
    Fixpoint typed_foldr (tvs : tenv typ) (e : expr typ func) (t : typ) : T :=
      match e with
        | App f x =>
          match typeof_expr nil tus tvs x with
            | None => atom tvs t e
            | Some d =>
              app tvs d t
                  (typed_foldr tvs f (typ2 d t))
                  (typed_foldr tvs x d)
          end
        | Abs d e =>
          typ2_match (fun _ => T) nil t
                     (fun _ r =>
                        abs tvs d r (typed_foldr (t :: tvs) e r))
                     (atom tvs t (Abs d e))
        | e => atom tvs t e
      end.
  End typed_fold.

  Variable prove : tenv typ -> tenv typ -> expr typ func -> subst -> option subst.

  Definition rewrite_bu (tus tvs : tenv typ) (e : expr typ func) (t : typ) (s : subst)
  : bool * expr typ func * subst :=
    @typed_foldr
      (nat -> subst -> bool * expr typ func * subst)%type
      (fun tvs t e under s =>
         match apply_rewrite_at prove tus tvs under t e s with
           | None => (false, e, s)
           | Some (e,s) => (true, e, s)
         end)
      (fun tvs d r rr under s =>
         (** TODO: what are the requirements for rewriting under functions **)
         let '(p,rr,sr) := rr (S under) s in
         match apply_rewrite_at prove tus tvs under (typ2 d r) rr sr with
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
