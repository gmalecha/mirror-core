Require Import MirrorCore.ExprI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO(gmalecha): There needs to be a nicer interface to this.
 ** At the moment, it appears that if I pack things up then it all breaks down.
 **)
Section knot.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable expr : Type.
  Variable Expr_expr : Expr typD expr.

  Record EProver (Facts : Type) : Type :=
  { Summarize : tenv typ -> tenv typ -> list expr -> Facts
  ; Learn : Facts -> tenv typ -> tenv typ -> list expr -> Facts
  ; Prove : forall (subst : Type) {S : Subst subst expr},
              Facts -> tenv typ -> tenv typ -> subst -> expr -> option subst
  }.

  Variable fl fr : Type.
  (** NOTE: This type is essential!
   ** Perhaps this should be the type of EProver
   ** The other thing that I probably want is to cps-ify this, that enables
   ** me to learn a little and then pass on to learn more...
   **)
  Definition EProveT (F : Type) : Type :=
    forall (subst : Type) {S : Subst subst expr},
      F -> tenv typ -> tenv typ -> subst -> expr -> option subst.
  Variable summarizeL : tenv typ -> tenv typ -> list expr -> fl.
  Variable summarizeR : tenv typ -> tenv typ -> list expr -> fr.
  Variable learnL : fl -> tenv typ -> tenv typ -> list expr -> fl.
  Variable learnR : fr -> tenv typ -> tenv typ -> list expr -> fr.
  Variable proveL : forall aux, EProveT aux -> EProveT fl.
  Variable proveR : forall aux, EProveT aux -> EProveT fr.

  Record KnotFacts : Type := mkKnotFacts
  { knot_left : fl
  ; knot_right : fr
  }.

  Fixpoint knotProve (n : nat) : EProveT KnotFacts :=
    match n with
      | 0 => fun _ _ _ _ _ _ _ => None
      | S n =>
        let res := knotProve n in
        fun _ _ kf =>
          @proveL KnotFacts (fun _ _ kf =>
                               @proveR KnotFacts res _ _ kf.(knot_right))
                  _ _ kf.(knot_left)
    end.

  Definition knotProver (n : nat) : EProver KnotFacts :=
  {| Summarize := fun tus tvs es =>
                    {| knot_left := summarizeL tus tvs es
                     ; knot_right := summarizeR tus tvs es
                     |}
   ; Learn := fun F tus tvs es =>
                {| knot_left := learnL F.(knot_left) tus tvs es
                 ; knot_right := learnR F.(knot_right) tus tvs es
                 |}
   ; Prove := knotProve n
   |}.
End knot.