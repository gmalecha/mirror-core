Require Import List Bool.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Data.Monads.FuelMonad.
Require Import ExtLib.Relations.TransitiveClosure.
Require Import ExtLib.Recur.Relation.
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
  Context {Expr_expr : Expr typD expr}.
  Context {RType_typ : RType typD}.
  Context {RTypeOk_typ : RTypeOk RType_typ}.
  Context {typ_arr : TypInstance2 typD Fun}.
  Context {typ_m : TypInstance1 typD m}.
  Let tvArr := @typ2 _ typD _ typ_arr.
  Let tvM := @typ1 _ typD _ typ_m.

  Variable bind_app : @SymAppN typ _ expr _ 2 ((fun x => tvM (vector_hd x)) :: (fun x => tvArr (vector_hd x) (tvM (vector_hd (vector_tl x)))):: nil) (fun _ => tvM).
  Variable ret_app : @SymAppN typ _ expr _ 1 (vector_hd :: nil) tvM.
  Variable app_i : forall d r, @AppInstance _ typD expr _ (tvArr d r) d r.
  Variable lam : @Lambda typ _ expr _.

  Let Bind (t1 t2 : typ) (b1 b2 : expr) : expr := 
    sappn bind_app (Vcons t1 (Vcons t2 (Vnil _)))
                   (Vcons b1 (Vcons b2 (Vnil _))).
  Let Ret (t1 : typ) (b1 : expr) : expr := 
    sappn ret_app (Vcons t1 (Vnil _))
                  (Vcons b1 (Vnil _)).

  Definition monad_match (R : Type) (e : expr) 
             (caseRet : typ -> forall e' : expr, acc e' e -> R)
             (caseBind : typ -> typ -> forall e' e'' : expr, acc e' e -> acc e'' e -> R)
             (caseElse : unit -> R) : R.
  refine (
    match sappn_check bind_app e with
      | Some (existT vs_es pf) => 
        caseBind (vector_hd (fst vs_es)) (vector_hd (vector_tl (fst vs_es)))
                 (vector_hd (snd vs_es)) (vector_hd (vector_tl (snd vs_es)))
                 _ _
      | None => match sappn_check ret_app e with
                  | Some (existT vs_es _) => 
                    caseRet (vector_hd (fst vs_es)) (vector_hd (snd vs_es))
                            _
                  | None => caseElse tt
                end
    end); repeat (eassumption || apply ForallV_vector_hd || apply ForallV_vector_tl).
  Defined.

  Require Import MirrorCore.Approx.

  Definition monad_run' : expr -> nat -> expr * bool :=
    @approx _ 
            (fun recur e => 
               let do_lam e := 
                   match lambda_check lam e with
                     | None => inl e
                     | Some (existT (t,e) _) => 
                       match recur e with
                         | (e',true) => inr (t,e')
                         | (e',false) => inl e
                       end                       
                   end
               in
               @monad_match (expr * bool) e
                            (fun _ _ _ => (e, false))
                            (fun t1 t2 b1 b2 _ _ =>
                               let b1' := recur b1 in
                               match sappn_check ret_app (fst b1') with
                                 | None => 
                                   let b2' := do_lam b2 in
                                   match b2' with
                                     | inl b2' => (Bind t1 t2 (fst b1') b2, snd b1')
                                     | inr (t,b2') => (Bind t1 t2 (fst b1') (lambda lam t b2'), true)
                                   end
                                 | Some (existT (t, v) _) =>
                                   let t := vector_hd t in
                                   let v := vector_hd v in
                                   let b2' := do_lam b2 in
                                   match b2' with
                                     | inl b2' => 
                                       (@app1 _ typD expr _ _ _ _ (app_i t (tvM t2)) b2' v, true)
                                     | inr (_, b2') =>
                                       (subst0 lam b2' v, true)
                                   end
                               end)
                            (fun _ => (e, false))).

  Definition monad_run (e : expr) : expr :=
    fst (monad_run' e 100).
    
End Demo.

(**

  Let tacc := rightTrans (@acc _ _ _  Expr_expr).

  Fixpoint trans_rightTrans x y (pf : tacc y x) : forall z, tacc z y -> tacc z x :=
    match pf in rightTrans _ y x return forall z, tacc z y -> tacc z x with
      | RTFin _ _ pf => fun _ pf' => RTStep _ pf' pf
      | RTStep _ _ _ pf pf' => fun _ pf'' => RTStep _ (trans_rightTrans pf pf'') pf'
    end.    

  Definition monad_run' : expr -> expr.
  refine (
          @Fix _ _ (wf_rightTrans (@wf_acc _ _ _ Expr_expr)) 
               (fun _ : expr => expr)
               (fun e recur =>
                  let do_lam (e' : expr) (pf : tacc e' e) : expr + {x : typ * expr & tacc (snd x) e'} := 
                      _
                  in e)).
  refine (      
      match lambda_check lam e' with
        | None => inl e'
        | Some (existT t_e pf') =>
          let e'' := recur (snd t_e) (trans_rightTrans pf (RTFin _ _ _ pf')) in
          inr (fst t_e,e'')
      end).
  Require Import Setoid.
  etransitivity.
                  in
                  e)).
                  @monad_match expr
                               e
                               (fun _ _ _ => e)
                               (fun t1 t2 b1 b2 pf1 pf2 =>
                                  let b1' := recur b1 pf1 in
                                  match sappn_check ret_app b1' with
                                    | None => (* 
                                      let b2' := do_lam b2 _ in _
                                      match b2' with
                                        | inl b2' => Bind t1 t2 b1' b2
                                        | inr _ => (* (t,b2') => ret (Bind t1 t2 b1' (lambda lam t b2')) *) _
                                      end *) _
                                    | Some _ (*(t, v)*) => _
                                  (*
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
*)
                                  end)
                               (fun _ => e))).
  Defined.


 
    
(*
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
*)


**)