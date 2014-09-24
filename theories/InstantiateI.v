Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.

Fixpoint hlist_build {T U} (F : T -> Type) (f : forall x : T, U -> option (F x))
           (ls : list T) (ls' : list U)
: option (hlist F ls) :=
  match ls as ls , ls' return option (hlist F ls) with
    | nil , nil => Some Hnil
    | l :: ls , l' :: ls' =>
      match hlist_build F f ls ls' with
        | None => None
        | Some res =>
          match f l l' with
            | None => None
            | Some x =>
              Some (Hcons x res)
          end
      end
    | _ , _ => None
  end.

Section definitions.
  Variables typ expr : Type.
  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr _ expr}.
  Context {ExprOk_expr : ExprOk Expr_expr}.

  (** instantiate **)
  Variable instantiate : (nat -> option expr) -> expr -> expr.

  Definition sem_preserves_if (tus : tenv (ctyp typ)) (tvs : tenv typ)
             (P : exprT tus tvs Prop)
             (f : nat -> option expr) : Prop :=
    forall u e es t get vals,
      f u = Some e ->
      nth_error_get_hlist_nth _ tus u = Some (@existT _ _ t get) ->
      hlist_build (fun T => exprT tus tvs (typD T))
                  (fun t e => exprD' tus tvs e t) t.(cctx) es = Some vals ->
      exists eD,
        exprD' tus t.(cctx) e t.(vtyp) = Some eD /\
        forall us vs,
          P us vs ->
          let vs' := hlist_map (fun t (x : exprT tus tvs (typD t)) => x us vs) vals in
          get us vs' = eD us vs'.

(*
  (** TODO **)
  Definition instantiate_mentionsU : Prop :=
    forall f n e u,
      mentionsU u (instantiate f n e) = true <-> (** do i need iff? **)
      (   (f u = None /\ mentionsU u e = true)
       \/ exists u' e',
            f u' = Some e' /\
            mentionsU u' e = true/\
            mentionsU u e' = true).
*)

  Definition exprD'_instantiate : Prop :=
    forall tus tvs f e tvs' t eD P,
      sem_preserves_if tus tvs P f ->
      exprD' tus (tvs' ++ tvs) e t = Some eD ->
      exists eD',
        exprD' tus (tvs' ++ tvs) (instantiate f e) t = Some eD' /\
        forall us vs vs',
          P us vs ->
          eD us (hlist_app vs' vs) = eD' us (hlist_app vs' vs).
End definitions.

Arguments sem_preserves_if {typ expr RType Expr} _ _ _ _ : rename.
