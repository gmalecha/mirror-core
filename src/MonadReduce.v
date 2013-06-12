Require Import List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import MirrorCore.TypesExt.
Require Import MirrorCore.ExprExt.

Set Implicit Arguments.
Set Strict Implicit.

Section Demo.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable expr : Type.
  Context {RType_typ : RType typD}.
  Context {RTypeOk_typ : RTypeOk RType_typ}.
  Context {typ_arr : TypInstance2 typD Fun}.
  Context {typ_m : TypInstance1 typD m}.
  Let tvArr := @typ2 _ typD _ typ_arr.
  Let tvM := @typ1 _ typD _ typ_m.

  Variable bind_app : @SymAppN typ expr 2 ((fun x => tvM (vector_hd x)) :: (fun x => tvArr (vector_hd x) (tvM (vector_hd (vector_tl x)))):: nil) (fun _ => tvM).
  Variable ret_app : @SymAppN typ expr 1 (vector_hd :: nil) tvM.
  Variable app_i : forall d r, AppInstance typD expr (tvArr d r) d r.
  Variable lam : Lambda typ expr.

  Let Bind (t1 t2 : typ) (b1 b2 : expr) : expr := 
    sappn bind_app (Vcons t1 (Vcons t2 (Vnil _)))
                   (Vcons b1 (Vcons b2 (Vnil _))).
  Let Ret (t1 : typ) (b1 : expr) : expr := 
    sappn ret_app (Vcons t1 (Vnil _))
                  (Vcons b1 (Vnil _)).

  Definition monad_match (R : Type) (caseRet : typ -> expr -> R)
                                    (caseBind : typ -> typ -> expr -> expr -> R)
                                    (caseElse : unit -> R) (e : expr) : R :=
    match sappn_check bind_app e with
      | Some (vs,es) => caseBind (vector_hd vs) (vector_hd (vector_tl vs)) (vector_hd es) (vector_hd (vector_tl es))
      | None => match sappn_check ret_app e with
                  | Some (vs,es) => caseRet (vector_hd vs) (vector_hd es)
                  | None => caseElse tt
                end
    end.


  Import MonadNotation.
  Local Open Scope monad_scope.

  (** Recursion is a problem! **)
  Definition monad_run' : expr -> GFix expr.
  refine (
      mfix (fun recur e =>
              let do_lam e := 
                  match lambda_check lam e with
                    | None => ret (inl e)
                    | Some (t,e) => e' <- recur e ;;
                                    ret (inr (t,e'))
                  end
              in
      @monad_match (GFix expr)
        (fun _ _ => ret e)
        (fun t1 t2 b1 b2 =>
           b1' <- recur b1 ;;
           match sappn_check ret_app b1' with
             | None => 
               b2' <- do_lam b2 ;;
               match b2' with
                 | inl b2' => ret (Bind t1 t2 b1' b2)
                 | inr (t,b2') => ret (Bind t1 t2 b1' (lambda lam t b2'))
               end
             | Some (t, v) =>
               let t := vector_hd t in
               let v := vector_hd v in
               b2' <- do_lam b2 ;;
               match b2' with
                 | inl b2' => 
                   ret (@app1 _ typD expr _ _ _ (app_i t (tvM t2)) b2' v)
                 | inr (_, b2') =>
                   let b2' := subst0 lam b2' v in
                   recur b2'
               end
           end)
        (fun _ => ret e)
        e)).
  Defined.

  Definition monad_run (e : expr) : expr :=
    match runGFix (monad_run' e) 100 with
      | Term e => e
      | Diverge => e
    end.
    
End Demo.
