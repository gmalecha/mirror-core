Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.ExprCore.

Set Implicit Arguments.
Set Strict Implicit.

Section typed_fold.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable func : Type.
  Variable RType_typ : RType typD.
  Variable RSym_func : RSym typD func.
  Variable Typ2_Fun : Typ2 typD Fun.

  Section folder.
    Variable ts : list Type.

    Variable T : Type.

    Variable do_var : var -> typ -> T.
    Variable do_uvar : var -> typ -> T.
    Variable do_inj : func -> typ -> T.
    Variable do_app : list typ -> list typ -> typ -> typ -> T -> T -> T.
    Variable do_abs : list typ -> list typ -> typ -> typ -> T -> T.

    (** The type doesn't guarantee well-typedness, so we need to return an error
     **)
    Fixpoint typed_mfold (tus tvs : list typ) (t : typ) (e : expr typ func)
    : option T :=
      match e with
        | Var v => Some (do_var v t)
        | UVar u => Some (do_uvar u t)
        | Inj f => Some (do_inj f t)
        | Abs t' e =>
          typ2_match (F := Fun)
                     (fun _ => option T)
                     ts t
                     (fun d r =>
                        match typed_mfold tus (d :: tvs) r e with
                          | Some rr =>
                            Some (do_abs tus tvs d r rr)
                          | None => None
                        end)
                     None
        | App f x =>
          match typed_mfold_infer tus tvs x with
            | None => None
            | Some (d,xv) =>
              match typed_mfold tus tvs (typ2 d t) f with
                | None => None
                | Some fv => Some (do_app tus tvs d t fv xv)
              end
          end
      end
    with typed_mfold_infer (tus tvs : list typ) (e : expr typ func)
                           {struct e}
    : option (typ * T) :=
      match e with
        | Var v =>
          match nth_error tvs v with
            | None => None
            | Some t => Some (t, do_var v t)
          end
        | UVar u =>
          match nth_error tus u with
            | None => None
            | Some t => Some (t, do_uvar u t)
          end
        | Inj f =>
          match typeof_sym f with
            | None => None
            | Some t => Some (t,do_inj f t)
          end
        | Abs d e =>
          match typed_mfold_infer tus (d :: tvs) e with
            | None => None
            | Some (r,v) =>
              Some (typ2 d r, do_abs tus tvs d r v)
          end
        | App f x =>
          match typed_mfold_infer tus tvs f with
            | Some (dr,fv) =>
              typ2_match (F := Fun)
                         (fun _ => option (typ * T))
                         ts dr
                         (fun d r =>
                            match typed_mfold tus (d :: tvs) r x with
                              | Some rr => Some (r, do_abs tus tvs d r rr)
                              | None => None
                            end)
                         None
            | None => None
          end
      end.

    (** CPS version **)
    Fixpoint typed_mfold_cps R (tus tvs : list typ) (t : typ) (e : expr typ func)
             (success : T -> R) (failure : R) {struct e}
    : R :=
      match e with
        | Var v => success (do_var v t)
        | UVar u => success (do_uvar u t)
        | Inj f => success (do_inj f t)
        | Abs t' e =>
          typ2_match (F := Fun)
                     (fun _ => R)
                     ts t
                     (fun d r =>
                        typed_mfold_cps tus (d :: tvs) r e
                                        (fun rr => success (do_abs tus tvs d r rr))
                                        failure)
                     failure
        | App f x =>
          typed_mfold_infer_cps tus tvs x (fun d xv =>
                                             typed_mfold_cps tus tvs (typ2 d t) f
                                                             (fun fv => success (do_app tus tvs d t fv xv))
                                                             failure)
                                failure
      end
    with typed_mfold_infer_cps R (tus tvs : list typ) (e : expr typ func)
         (success : typ -> T -> R) (failure : R) {struct e}
    : R :=
      match e with
        | Var v =>
          match nth_error tvs v with
            | None => failure
            | Some t => success t (do_var v t)
          end
        | UVar u =>
          match nth_error tus u with
            | None => failure
            | Some t => success t (do_uvar u t)
          end
        | Inj f =>
          match typeof_sym f with
            | None => failure
            | Some t => success t (do_inj f t)
          end
        | Abs d e =>
          typed_mfold_infer_cps tus (d :: tvs) e
                                (fun r v =>
                                   success (typ2 d r) (do_abs tus tvs d r v))
                                failure
        | App f x =>
          typed_mfold_infer_cps tus tvs f (fun dr fv =>
               typ2_match (F := Fun)
                          (fun _ => R)
                          ts dr
                          (fun d r =>
                             typed_mfold_cps tus (d :: tvs) r x
                                             (fun rr => success r (do_abs tus tvs d r rr))
                                             failure)
                          failure)
               failure
      end.
  End folder.
End typed_fold.