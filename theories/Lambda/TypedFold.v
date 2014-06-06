Require MirrorCore.Lambda.TypedFoldLazy.

Set Implicit Arguments.
Set Strict Implicit.

Definition typed_mfold_lazy
           (typ : Type) (typD : list Type -> typ -> Type) (func : Type)
           (_ : SymI.RSym typD func)
           (_ : TypesI2.Typ2 typD PreFun.Fun)
           (ts : list Type)
           (T : Type)
       (do_var : ExprCore.var -> typ -> TypedFoldLazy.Lazy T)
       (do_uvar : ExprCore.uvar -> typ -> TypedFoldLazy.Lazy T)
       (do_inj : func -> typ -> TypedFoldLazy.Lazy T)
       (do_app : list typ -> list typ -> typ -> typ ->
                 TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T)
       (do_abs : list typ -> list typ -> typ -> typ ->
                 TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T)
       (tus tvs : list typ) (t : typ) (e : ExprCore.expr typ func)
: option T :=
  @TypedFoldLazy.typed_mfold_cpsL typ typD func _ _ ts T
                                  do_var do_uvar do_inj do_app do_abs
                                  (option T) tus tvs t e
                                  (fun x => x tt)
                                  None.

Definition typed_mfold_infer_lazy
           (typ : Type) (typD : list Type -> typ -> Type) (func : Type)
           (_ : SymI.RSym typD func)
           (_ : TypesI2.Typ2 typD PreFun.Fun)
           (ts : list Type)
           (T : Type)
       (do_var : ExprCore.var -> typ -> TypedFoldLazy.Lazy T)
       (do_uvar : ExprCore.uvar -> typ -> TypedFoldLazy.Lazy T)
       (do_inj : func -> typ -> TypedFoldLazy.Lazy T)
       (do_app : list typ -> list typ -> typ -> typ ->
                 TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T)
       (do_abs : list typ -> list typ -> typ -> typ ->
                 TypedFoldLazy.Lazy T -> TypedFoldLazy.Lazy T)
       (tus tvs : list typ) (e : ExprCore.expr typ func)
: option (typ * T) :=
  @TypedFoldLazy.typed_mfold_infer_cpsL typ typD func _ _ ts T
                                  do_var do_uvar do_inj do_app do_abs
                                  (option (typ * T)) tus tvs e
                                  (fun t x => match x tt with
                                                | None => None
                                                | Some val => Some (t,val)
                                              end)
                                  None.