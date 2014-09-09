Require Import ExtLib.Data.Fun.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed_fold.
  Variable typ : Type.
  Variable func : Type.

  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable RSym_func : RSym func.

  Section folderL.
    Definition Lazy (T : Type) := unit -> option T.

    Variable T : Type.

    Variable do_var : var -> typ -> Lazy T.
    Variable do_uvar : var -> typ -> Lazy T.
    Variable do_opaque : expr typ func -> typ -> Lazy T.
    Variable do_app : list typ -> list typ -> typ -> typ -> Lazy T -> Lazy T -> Lazy T.
    Variable do_abs : list typ -> list typ -> typ -> typ -> Lazy T -> Lazy T.

    Fixpoint typed_mfold_cpsL R (tus tvs : list typ) (t : typ) (e : expr typ func)
             (success : Lazy T -> R) (failure : R) {struct e}
    : R :=
      match e with
        | Var v => success (fun z => do_var v t z)
        | UVar u => success (fun z => do_uvar u t z)
        | Inj f => success (fun z => do_opaque e t z)
        | Abs t' e =>
          typ2_match (F := Fun)
                     (fun _ => R)
                     t
                     (fun d r =>
                        success (fun z => do_abs tus tvs d r
                                                 (fun z =>
                                                    typed_mfold_cpsL tus (d :: tvs) r e
                                                                     (fun rr => rr z)
                                                                     None) z))
                     failure
        | App f x =>
          typed_mfold_infer_cpsL tus tvs x (fun d xv =>
               success (fun z => do_app tus tvs d t xv
                                        (fun z =>
                                           typed_mfold_cpsL tus tvs (typ2 d t) f
                                                            (fun fv => fv z)
                                                            None) z))
                                 failure
      end
    with typed_mfold_infer_cpsL R (tus tvs : list typ) (e : expr typ func)
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
            | Some t => success t (fun z => do_opaque e t z)
          end
        | Abs d e =>
          typed_mfold_infer_cpsL tus (d :: tvs) e
                                 (fun r v =>
                                    success (typ2 d r) (fun z => do_abs tus tvs d r v z))
                                 failure
        | App f x =>
          typed_mfold_infer_cpsL tus tvs f (fun dr fv =>
           typ2_match (F := Fun)
                      (fun _ => R)
                      dr
                      (fun d r =>
                         success r (fun z =>
                                      do_abs tus tvs d r
                                             (fun z =>
                                                typed_mfold_cpsL tus (d :: tvs) r x
                                                                 (fun rr => rr z)
                                                                 None) z))

                                 failure)
                      failure
      end.
  End folderL.
End typed_fold.