Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.

Set Implicit Arguments.
Set Strict Implicit.

Definition Lazy T := unit -> T.

Section app_full.
  Variable typ : Type.
  Variable sym : Type.

  Variable T : expr typ sym -> Type. (** The return type **)

  Variable do_var : forall v : var, Lazy (T (Var v)).
  Variable do_uvar : forall u : uvar, Lazy (T (UVar u)).
  Variable do_opaque : forall s : sym, Lazy (T (Inj s)).
  Variable do_app : forall f : expr typ sym, Lazy (T f) ->
                    forall args : list { e : expr typ sym & Lazy (T e) },
                    Lazy (T (apps f (map (@projT1 _ _) args))).
  Variable do_abs : forall (t : typ) (e : expr typ sym),
                      Lazy (T e) -> Lazy (T (Abs t e)).

  Fixpoint mfold_app (e : expr typ sym) {struct e} : Lazy (T e) :=
    match e as e return Lazy (T e) with
      | Var v => do_var v
      | UVar u => do_uvar u
      | Inj f => do_opaque f
      | Abs t' e =>
        do_abs t' (mfold_app e)
      | App f x =>
        gather_args f (@existT _ _ x (mfold_app x) :: nil)
    end
  with gather_args (e : expr typ sym)
                   (args : list { e : expr typ sym & Lazy (T e) })
                   {struct e} : Lazy (T (apps e (map (@projT1 _ _) args))) :=
    match e as e
          return Lazy (T (apps e (map (@projT1 _ _) args)))
    with
      | App f x =>
        gather_args f (@existT _ _ x (mfold_app x) :: args)
      | Var v =>
        @do_app (Var v) (do_var v) args
      | UVar v =>
        @do_app (UVar v) (do_uvar v) args
      | Inj i =>
        @do_app (Inj i) (do_opaque i) args
      | Abs t' e =>
        @do_app (Abs t' e) (do_abs t' (mfold_app e)) args
    end.

End app_full.

Section with_args.
  Variable typ : Type.
  Variable sym : Type.

  Variable T : expr typ sym -> Type. (** The return type **)

  Unset Elimination Schemes.

  Record AppFullArgs : Type :=
  { do_var : forall v : var, Lazy (T (Var v))
  ; do_uvar : forall u : uvar, Lazy (T (UVar u))
  ; do_opaque : forall s : sym, Lazy (T (Inj s))
  ; do_app : forall f : expr typ sym, Lazy (T f) ->
                                      forall args : list { e : expr typ sym & Lazy (T e) },
                                        Lazy (T (apps f (map (@projT1 _ _) args)))
  ; do_abs : forall (t : typ) (e : expr typ sym),
               Lazy (T e) -> Lazy (T (Abs t e))
  }.

  Set Elimination Schemes.

  Definition app_fold_args (args : AppFullArgs) : forall e, Lazy (T e) :=
    match args with
      | {| do_var := do_var
         ; do_uvar := do_uvar
         ; do_opaque := do_opaque
         ; do_app := do_app
         ; do_abs := do_abs |} =>
        @mfold_app typ sym T do_var do_uvar do_opaque do_app do_abs
    end.
End with_args.