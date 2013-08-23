Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

Module Type ExprDenote.

  (**
   ** The denotation function with binders must be total because we
   ** can't introduce the binder until we know that we are going to get
   ** the right type out, but, at the same time, we don't know we will
   ** succeed until after we've taken the denotation of the body,
   ** which we can't do until we have the binder.
   **
   **)
  Parameter exprD : forall (ts : types) (fs : functions ts),
    env (typD ts) -> env (typD ts) -> expr -> forall t : typ,
    option (typD ts nil t).

  Section with_envs.
    Variable ts : types.
    Variable fs : functions ts.
    Variable us : env (typD ts).

    Axiom typeof_exprD : forall vs e t,
      typeof_expr (typeof_funcs fs) (typeof_env us) (typeof_env vs) e = Some t ->
      exists val, exprD fs us vs e t = Some val.

    Axiom exprD_Var : forall ve v t,
      exprD fs us ve (Var v) t = lookupAs ve v t.

    Axiom exprD_UVar : forall ve u t,
      exprD fs us ve (UVar u) t = lookupAs us u t.

    Axiom exprD_Func : forall ve f ts t,
      exprD fs us ve (Func f ts) t =
      match nth_error fs f with
        | None => None
        | Some f =>
          match type_apply _ _ ts _ _ f.(fdenote) with
            | None => None
            | Some t' =>
              @typ_cast_val _ _ (instantiate_typ ts (ftype f)) t t'
          end
      end.

    Axiom exprD_Equal : forall ve t l r t',
      exprD fs us ve (Equal t l r) t' =
      match t' as t' return option (typD ts nil t') with
        | tvProp =>
          match exprD fs us ve l t , exprD fs us ve r t with
            | Some l , Some r => Some (l = r)
            | _ , _ => None
          end
        | _ => None
      end.

    Axiom exprD_Not : forall ve p t',
      exprD fs us ve (Not p) t' =
      match t' as t' return option (typD ts nil t') with
        | tvProp =>
          match exprD fs us ve p tvProp with
            | Some p => Some (~p)
            | _ => None
          end
        | _ => None
      end.

    Axiom exprD_Abs : forall ve t u e val,
      exprD fs us ve (Abs t e) (tvArr t u) = Some val ->
      forall x, exprD fs us (existT _ t x :: ve) e u = Some (val x).

    Axiom exprD_App : forall ve t e arg,
      exprD fs us ve (App e arg) t =
      match typeof_expr (typeof_funcs fs) (typeof_env us) (typeof_env ve) e with
        | Some (tvArr l r) =>
          match exprD fs us ve e (tvArr l r)
              , exprD fs us ve arg l
              , typ_cast_typ _ (fun x => x) _ r t
          with
            | Some f , Some x , Some cast =>
              Some (cast (f x))
            | _ , _ , _ => None
          end
        | _ => None
      end.
  End with_envs.

End ExprDenote.
