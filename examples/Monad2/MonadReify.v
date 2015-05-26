Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Reify.Reify.
Require Import McExamples.Monad2.MonadExpr.
Require Import McExamples.Monad2.MonadReduce.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).


(** Declare patterns **)
Reify Declare Patterns patterns_monad_typ := typ.
Reify Declare Patterns patterns_monad := (expr typ mext).

Reify Declare Table table_types : BinNums.positive.

Reify Declare Syntax reify_monad_typ :=
  { (@Patterns.CFirst _ (@Patterns.CPatterns _ patterns_monad_typ ::
                        (@Patterns.CTable typ _ table_types tyType) :: nil)) }.

Definition otherFunc (p : BinNums.positive) : expr typ mext :=
  Inj (inl p).
Definition mFunc (p : _) : expr typ mext :=
  Inj (inr p).

Reify Declare Typed Table table_terms : BinNums.positive => reify_monad_typ.

(** Declare syntax **)
Reify Declare Syntax reify_monad :=
  { (@Patterns.CFirst _ ((@Patterns.CPatterns (expr typ mext) patterns_monad) ::
                         (@Patterns.CApp (expr typ mext) (@ExprCore.App typ mext)) ::
                         (@Patterns.CAbs (expr typ mext) reify_monad_typ (@ExprCore.Abs typ mext)) ::
                         (@Patterns.CVar (expr typ mext) (@ExprCore.Var typ mext)) ::
                         (@Patterns.CTypedTable (expr typ mext) _ _ table_terms otherFunc) :: nil))
  }.

Reify Pattern patterns_monad_typ += (@RExact _ Prop) => tyProp.
Reify Pattern patterns_monad_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_monad_typ) => tyArr a b).
(** TODO: I don't have a way to do the particular monad **)

Reify Pattern patterns_monad +=
      ((!! (@ret)) @ RIgnore @ RIgnore @ (?0)) =>
      (fun (t : function reify_monad_typ) => mFunc (MonadSym.mReturn t)).
Reify Pattern patterns_monad +=
      ((!! (@ret)) @ RIgnore @ RIgnore @ (?0) @ ?1) =>
      (fun (t u : function reify_monad_typ) => mFunc (MonadSym.mBind t u)).

Ltac reify_left m :=
  let Monad_m := constr:(_ : Monad m) in
  match goal with
    | |- ?L = ?X =>
      let K ts fs us e :=
          let t := constr:(tyM (tyType 1)) in
          let result := constr:(reduce t e) in
          let result' := eval vm_compute in result in
          generalize (@reduceOk m Monad_m ts fs e us nil t result'
                            (@eq_refl _ _)) ;
          let H := fresh in
          intro H ;
          cbv beta iota zeta delta [ ts fs us exprD EnvI.split_env exprD' func_simul exprT_App eq_sym TypesI.typ2_cast Typ2_tyArr SymEnv.funcD FMapPositive.PositiveMap.find SymEnv.fdenote  SymI.typeof_sym RSym_mext SymSum.RSym_sum MonadSym.RSym_mfunc MonadSym.typeof_mfunc RType_typ SymI.symD MonadSym.mfuncD TypesI.typ2_match funcAs SymEnv.RSym_func SymEnv.func_typeof_sym exprT_GetVAs exprT_GetUAs SymEnv.ftype TypesI.type_cast Rcast type_cast TypesI.Relim TypesI.Rsym OptionMonad.Monad_option EnvI.nth_error_get_hlist_nth Functor.fmap positive_eq_odec f_equal Option.Functor_option TypesI.typ2 Relim getType typD Rcast_val HList.hlist_hd HList.hlist_tl ] in H ;
          simpl in H ;
          clear ts fs us
      in
      (let X := constr:((fun (t : table_types) (trm : table_terms t) => Type)) in
       reify_expr reify_monad K [ X ] [ L ])
  end.

Ltac reduce_monads m :=
  let Monad_m := constr:(_ : Monad m) in
  match goal with
    | |- ?L = ?R =>
      let K ts fs us el er :=
          let t := constr:(tyM (tyType 1)) in
          change (@MonadReduce.Conclusion_reduce_eq m Monad_m ts fs us nil t el er) ;
          let result := constr:((reduce t el, reduce t er)) in
          let result' := eval vm_compute in result in
          pose (result'V := result') ;
          cut (@MonadReduce.Premise_reduce_eq m Monad_m ts fs us nil t result'V) ;
          [ refine (@reduce_eq m Monad_m ts fs el er us nil t result'V
                               (@eq_refl _ result'V <: result = result'V))
          | cbv beta iota zeta delta [ ts fs us result'V exprD EnvI.split_env exprD' func_simul exprT_App eq_sym TypesI.typ2_cast Typ2_tyArr SymEnv.funcD FMapPositive.PositiveMap.find SymEnv.fdenote  SymI.typeof_sym RSym_mext SymSum.RSym_sum MonadSym.RSym_mfunc MonadSym.typeof_mfunc RType_typ SymI.symD MonadSym.mfuncD TypesI.typ2_match funcAs SymEnv.RSym_func SymEnv.func_typeof_sym exprT_GetVAs exprT_GetUAs SymEnv.ftype TypesI.type_cast Rcast type_cast TypesI.Relim TypesI.Rsym OptionMonad.Monad_option EnvI.nth_error_get_hlist_nth Functor.fmap positive_eq_odec f_equal Option.Functor_option TypesI.typ2 Relim getType typD Rcast_val HList.hlist_hd HList.hlist_tl MonadReduce.Premise_reduce_eq fst snd ] ;
          simpl ;
          clear ts fs us result'V ]
      in
      reify_expr reify_monad K
              [ (fun (t : table_types) (trm : table_terms t) => Type) ]
              [ L R ]
  end.
