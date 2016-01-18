Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import MirrorCore.ExprI.

Set Implicit Arguments.
Set Strict Implicit.

Section AppAbs.
  Variable typ : Type.
  Context {RType_typ : RType typ}.

  Variable expr : Type.
  Context {Expr_expr : Expr typ expr}.

  Context {Typ2_fun : Typ2 _ RFun}.

  Class Abstraction :=
  { Abs : typ -> expr -> expr
  ; Abs_match : expr -> forall T, (typ -> expr -> T) -> T -> T
  }.

  Class AbstractionOk (A : Abstraction) :=
  { exprD_Abs : forall (tus : tenv typ) (tvs : tenv typ) e t t',
      exprD tus tvs t' (Abs t e) =
      typ2_match (Typ2:=Typ2_fun)
                 (fun T => option (exprT tus tvs T)) t'
                 (fun d r =>
                    bind (m := option)
                         (type_cast d t)
                         (fun cast =>
                            bind (m := option)
                                 (exprD tus (t :: tvs) r e)
                                 (fun val =>
                                    ret (fun us vs x =>
                                           val us (Hcons (F:=typD) (Relim (fun x => x) (Rsym cast) x) vs)))))
                  None
  ; Abs_match_iota : forall t e,
      Abs_match (Abs t e) = fun T f _ => f t e
  ; Abs_match_case : forall e,
         (exists t' e',
          e = Abs t' e' /\
          Abs_match e = fun T f _ => f t' e')
      \/ ((~exists t' e', e = Abs t' e') /\
          Abs_match e = fun T _ d => d)
  }.

  Class Application :=
  { App : expr -> expr -> expr
  ; App_match : expr -> forall T, (expr -> expr -> T) -> T -> T
  }.

  Definition exprT_Abs {tus tvs t u}
  : exprT tus (t :: tvs) (typD u) ->
    exprT tus tvs (typD (typ2 t u)) :=
    match eq_sym (typ2_cast (F:=RFun) t u) in _ = T
          return exprT tus (t :: tvs) (typD u) -> exprT tus tvs T
    with
    | eq_refl => fun f => fun us vs x => f us (Hcons x vs)
    end.

  Definition exprT_App {tus : tenv typ} {tvs : tenv typ} {T U : typ}
  : exprT tus tvs (typD (typ2 T U)) ->
    exprT tus tvs (typD T) ->
    exprT tus tvs (typD U) :=
    match eq_sym (typ2_cast (F:=RFun) T U) in _ = t
          return exprT tus tvs t ->
                 exprT tus tvs (typD T) ->
                 exprT tus tvs (typD U)
    with
    | eq_refl => fun F X us vs => (F us vs) (X us vs)
    end.

  Class ApplicationOk (A : Application) :=
  { exprD_App : forall (tus : tenv typ) (tvs : tenv typ) f x d r F X,
      exprD tus tvs (typ2 d r) f = Some F ->
      exprD tus tvs d x = Some X ->
      exprD tus tvs r (App f x) = Some (exprT_App F X)
  ; match_App_iota : forall f e, App_match (App f e) = fun T r _ => r f e
  ; match_App_case : forall e,
         (exists t' e',
          e = App t' e' /\
          App_match e = fun T f _ => f t' e')
      \/ ((~exists t' e', e = App t' e') /\
          App_match e = fun T _ d => d)
  }.

End AppAbs.

Arguments exprT_App {typ _ _ _ _ _ _} _ _ _ _.
Arguments exprT_Abs {typ _ _ _ _ _ _} _ _ _.
Arguments ApplicationOk {typ _ expr _ _} _ : rename.
Arguments AbstractionOk {typ _ expr _ _} _ : rename.