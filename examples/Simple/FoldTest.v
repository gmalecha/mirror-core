Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import MirrorCore.Lambda.TypedFoldApp.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.AppN.
Require Import McExamples.Simple.Simple.

Definition AFFA : AppFullFoldArgs typ func (expr typ func).
refine
{| do_var := fun v _ _ => Some (Var v)
 ; do_uvar := fun u _ _ => Some (UVar u)
 ; do_inj := fun f _ _ => Some (Inj f)
 ; do_app := fun _ _ _ _ f (xs : list (typ * expr typ func * Lazy (expr typ func))) force =>
               match f force
                   , mapT (fun (abc : (typ * expr typ func * Lazy (expr typ func))) =>
                             let '(_,_,c) := abc in
                             c force) xs
               with
                 | Some f , Some xs => Some (apps f xs)
                 | _ , _ => None
               end
 ; do_abs := fun _ _ _ _ _ x => x
 |}.
Defined.

Eval compute in lazy_typed_mfold _ _ AFFA nil nil tyNat (App (App (Inj Plus) (Inj (N 10))) (Inj (N 1))).