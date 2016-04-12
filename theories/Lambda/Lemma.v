Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.Expr.

Section reify_lemma.
  Variables typ func : Type.

  Variable is_forall : expr typ func -> option typ.
  Variable is_impl : expr typ func -> bool.

  Fixpoint get_alls (e : expr typ func)
  : list typ * expr typ func :=
    match e with
    | ExprCore.App f (ExprCore.Abs _ e) =>
      match is_forall f with
      | Some t =>
        let (alls,e) := get_alls e in
        (t :: alls, e)
      | None => (nil, e)
      end
    | _ => (nil, e)
    end.

  Fixpoint get_impls (e : expr typ func)
  : list (expr typ func) * expr typ func :=
    match e with
    | ExprCore.App (ExprCore.App f P) Q =>
      if is_impl f then
        let (impls,e) := get_impls Q in
        (P :: impls,e)
      else
        (nil, e)
    | _ => (nil, e)
    end.

  Definition convert_to_lemma (e : expr typ func)
  : lemma typ (expr typ func) (expr typ func) :=
    let (alls, e) := get_alls e in
    let (impls, e) := get_impls e in
    {| vars := rev alls
     ; premises := impls
     ; concl := e
     |}.
End reify_lemma.

Export MirrorCore.Lemma.