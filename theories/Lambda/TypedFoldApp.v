Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed_fold.
  Variable func : Type.

  Variable RType_typ : RType.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable RSym_func : RSym typD func.

  Section folderL.
    Definition Lazy (T : Type) := unit -> option T.

    Variable ts : list Type.

    Variable T : Type.

    Variable do_var : var -> typ -> Lazy T.
    Variable do_uvar : var -> typ -> Lazy T.
    Variable do_inj : func -> typ -> Lazy T.
    Variable do_app : list typ -> list typ ->
                      typ -> Lazy T -> list (typ * Lazy T) -> Lazy T.
    Variable do_abs : list typ -> list typ -> typ -> typ -> Lazy T -> Lazy T.

    Fixpoint unroll_types R (ft : typ) (ls : list (typ -> Lazy T))
             (success : typ -> list (typ * Lazy T) -> R)
             (failure : R) {struct ls}
    : R.
    refine
      match ls with
        | nil => success ft nil
        | l :: ls =>
          typ2_match (F := Fun)
                     (fun _ => R)
                     ts ft
                     (fun d r =>
                        unroll_types R r ls
                                     (fun rt ls =>
                                        success rt ((d, l d) :: ls))
                                     failure)
                     failure
      end.
    Defined.

    Fixpoint gather_app R (tus tvs : list typ) (e : expr typ func)
             (success : typ -> Lazy T -> list (typ * Lazy T) -> R)
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
             (fun ft val args =>
                typ2_match (F := Fun) (fun _ => R) ts ft
                           (fun d r =>
                              success r val
                                      ((d,fun z =>
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
              success ft val nil
          end
        | UVar u =>
          match nth_error tus u with
            | None => failure
            | Some ft =>
              let val := fun z => do_uvar u ft z in
              success ft val nil
          end
        | Inj f =>
          match typeof_sym f with
            | None => failure
            | Some ft =>
              let val := fun z => do_inj f ft z in
              success ft val nil
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
          typ2_match (F := Fun)
                     (fun _ => R)
                     ts t
                     (fun d r =>
                        success (fun z => do_abs tus tvs d r
                                                 (fun z =>
                                                    typed_mfold_cpsL tus (d :: tvs) r e
                                                                     (fun rr => rr z)
                                                                     None) z))
                     failure
        | App f x =>
          gather_app tus tvs f
                     (fun ft val vals =>
                        typ2_match (F := Fun) (fun _ => R) ts ft
                           (fun d r =>
                              let vals :=
                                  ((d,fun z =>
                                        typed_mfold_cpsL (R := option _)
                                                         tus tvs d x
                                                         (fun x => x z)
                                                         None)
                                     :: vals) in
                              success (fun z => do_app tus tvs r val vals z))
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
                                    success (typ2 d r) (fun z => do_abs tus tvs d r v z))
                                 failure
        | App f x =>
          gather_app tus tvs f
                     (fun ft val vals =>
                        typ2_match (F := Fun) (fun _ => R) ts ft
                           (fun d r =>
                              let vals :=
                                  ((d,fun z =>
                                        typed_mfold_cpsL (R := option _)
                                                         tus tvs d x
                                                         (fun x => x z)
                                                         None)
                                     :: vals) in
                              success ft (fun z => do_app tus tvs r val vals z))
                           failure)
                     failure
      end.
  End folderL.

End typed_fold.