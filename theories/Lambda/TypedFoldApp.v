Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed_fold.
  Variable typ : Set.
  Variable func : Set.

  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ RFun.
  Variable RSym_func : RSym func.

  Section folderL.
    Definition Lazy (T : Type) := unit -> option T.

    Variable T : Type.

    Variable do_var : var -> typ -> Lazy T.
    Variable do_uvar : var -> typ -> Lazy T.
    Variable do_inj : func -> typ -> Lazy T.
    Variable do_app : list typ -> list typ ->
                      typ -> expr typ func -> Lazy T -> list (typ * expr typ func * Lazy T) -> Lazy T.
    Variable do_abs : list typ -> list typ -> typ -> typ -> expr typ func -> Lazy T -> Lazy T.

    Fixpoint unroll_types R (ft : typ) (ls : list (typ -> Lazy T))
             (success : typ -> list (typ * Lazy T) -> R)
             (failure : R) {struct ls}
    : R.
    refine
      match ls with
        | nil => success ft nil
        | l :: ls =>
          typ2_match (F := RFun)
                     (fun _ => R)
                     ft
                     (fun d r =>
                        unroll_types R r ls
                                     (fun rt ls =>
                                        success rt ((d, l d) :: ls))
                                     failure)
                     failure
      end.
    Defined.

    Fixpoint gather_app R (tus tvs : list typ) (e : expr typ func)
             (success : typ -> expr typ func -> Lazy T -> list (typ * expr typ func * Lazy T) -> R)
             (failure : R) {struct e}
    : R :=
      match e return R with
        | App f x =>
          gather_app tus tvs f
(*
                     ((fun t => typed_mfold_cpsL tus tvs t x
                                                 (fun x => x)
                                                 (fun _ => None)) :: ls)
*)
             (fun ft f val args =>
                typ2_match (F := RFun) (fun _ => R) ft
                           (fun d r =>
                              success r f val
                                      ((d,x,fun z =>
                                              typed_mfold_cpsL (R := option _)
                                                               tus tvs d x
                                                               (fun x => x z)
                                                               None)
                                         :: args))
                           failure)
             failure
        | Var v =>
          match nth_error tvs v with
            | None => failure
            | Some ft =>
              let val := fun z => do_var v ft z in
              success ft (Var v) val nil
          end
        | UVar u =>
          match nth_error tus u with
            | None => failure
            | Some ft =>
              let val := fun z => do_uvar u ft z in
              success ft (UVar u) val nil
          end
        | Inj f =>
          match typeof_sym f with
            | None => failure
            | Some ft =>
              let val := fun z => do_inj f ft z in
              success ft (Inj f) val nil
          end
        | Abs d e =>
          typed_mfold_infer_cpsL tus (d :: tvs) e
                                 (fun rt val => failure)
                                 failure (*
                                    unroll_types (typ2 d rt) ls
                                                 (fun rt z => success rt val z)
                                                 failure)
                                 failure *)
      end

    with typed_mfold_cpsL R (tus tvs : list typ) (t : typ) (e : expr typ func)
             (success : Lazy T -> R) (failure : R) {struct e}
    : R :=
      match e with
        | Var v => success (fun z => do_var v t z)
        | UVar u => success (fun z => do_uvar u t z)
        | Inj f => success (fun z => do_inj f t z)
        | Abs t' e =>
          typ2_match (F := RFun)
                     (fun _ => R)
                     t
                     (fun d r =>
                        success (fun z => do_abs tus tvs d r e
                                                 (fun z =>
                                                    typed_mfold_cpsL tus (d :: tvs) r e
                                                                     (fun rr => rr z)
                                                                     None) z))
                     failure
        | App f x =>
          gather_app tus tvs f
                     (fun ft f val vals =>
                        typ2_match (F := RFun) (fun _ => R) ft
                           (fun d r =>
                              let vals :=
                                  vals ++ (d,x,fun z =>
                                                 typed_mfold_cpsL (R := option _)
                                                                  tus tvs d x
                                                                  (fun x => x z)
                                                                  None) :: nil in
                              success (fun z => do_app tus tvs r f val vals z))
                           failure)
                     failure
      end

    with typed_mfold_infer_cpsL
             R (tus tvs : list typ) (e : expr typ func)
             (success : typ -> Lazy T -> R) (failure : R) {struct e}
    : R :=
      match e with
        | Var v =>
          match nth_error tvs v with
            | None => failure
            | Some t => success t (fun z => do_var v t z)
          end
        | UVar u =>
          match nth_error tus u with
            | None => failure
            | Some t => success t (fun z => do_uvar u t z)
          end
        | Inj f =>
          match typeof_sym f with
            | None => failure
            | Some t => success t (fun z => do_inj f t z)
          end
        | Abs d e =>
          typed_mfold_infer_cpsL tus (d :: tvs) e
                                 (fun r v =>
                                    success (typ2 d r) (fun z => do_abs tus tvs d r e v z))
                                 failure
        | App f x =>
          gather_app tus tvs f
                     (fun ft f val vals =>
                        typ2_match (F := RFun) (fun _ => R) ft
                           (fun d r =>
                              let vals :=
                                  vals ++ (d,x,fun z =>
                                                 typed_mfold_cpsL (R := option _)
                                                                  tus tvs d x
                                                                  (fun x => x z)
                                                                  None) :: nil in
                              success ft (fun z => do_app tus tvs r f val vals z))
                           failure)
                     failure
      end.
  End folderL.

  Record AppFullFoldArgs (T : Type) : Type :=
  { do_var : var -> typ -> Lazy T
  ; do_uvar : uvar -> typ -> Lazy T
  ; do_inj : func -> typ -> Lazy T
  ; do_app : list typ -> list typ ->
             typ -> expr typ func -> Lazy T -> list (typ * expr typ func * Lazy T) -> Lazy T
  ; do_abs : list typ -> list typ -> typ -> typ -> expr typ func -> Lazy T -> Lazy T
  }.

  Definition lazy_typed_mfold {T : Type} (args : AppFullFoldArgs T)
  : list typ -> list typ -> typ -> expr typ func -> option (Lazy T) :=
    fun tus tvs t e =>
      @typed_mfold_cpsL T
                        args.(do_var)
                        args.(do_uvar)
                        args.(do_inj)
                        args.(do_app)
                        args.(do_abs) (option (Lazy T)) tus tvs t e
                                      (@Some _) None.

End typed_fold.
