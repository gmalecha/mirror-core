Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprDAs.
Require Import MirrorCore.InstantiateI.
Require Import MirrorCore.RTac.Core.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.RTac.Reduce.

Require Import MirrorCore.Util.Forwardy.
Require Import MirrorCore.Util.Nat.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.

  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {ExprOk_expr : ExprOk _}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {ExprUVar_expr : ExprUVar expr}.
  Context {ExprUVarOk_expr : ExprUVarOk ExprUVar_expr}.

  Section lookup_compress.
    (** [es] must be pre-translated **)

    Fixpoint lookup_compress (es : list (option expr)) (base u : uvar)
    : option expr :=
      match es with
        | nil => Some (UVar (base + u)) (* DEAD *)
        | e :: es' =>
          match e , u with
            | None , 0 => Some (UVar base)
            | None , S u => lookup_compress es' (S base) u
            | Some e' , 0 => Some e'
            | Some _ , S u => lookup_compress es' base u
          end
      end.
  End lookup_compress.

  Definition do_instantiate {c : Ctx typ expr} (cs : ctx_subst c)
             (base : nat) (es : list (option expr)) (u : uvar)
  : option expr :=
    match lt_rem u base with
      | None => (* u < base *)
        ctx_lookup u cs
      | Some u' => lookup_compress es base u'
    end.

  Section minify.
    Variable base : nat.
    Variables (c : Ctx typ expr)
              (cs : ctx_subst c).
    Fixpoint minify_goal (es : list (option expr))
             (nus : nat)  (g : Goal typ expr)
    : Goal typ expr :=
      match g with
        | GAll t g' =>
          GAll t (minify_goal es nus g')
        | GExs ts m g' =>
          let len_ts := length ts in
          let mlist := amap_aslist m nus len_ts in
          let mlist_inst :=
              List.map (Functor.fmap
                          (instantiate (do_instantiate cs base (es ++ mlist))
                                       0)) mlist in
          let tes := combine ts mlist_inst in
          let tes' := filter (fun x => match snd x with
                                         | None => true
                                         | Some _ => false
                                       end) tes in
          let (ts',_) := split tes' in
          GExs_nil_check ts' (amap_empty _)
                         (minify_goal (es ++ mlist_inst) (len_ts + nus) g')
        | GHyp e g' =>
          GHyp (instantiate (do_instantiate cs base es) 0 e)
               (minify_goal es nus g')
        | GConj_ g1 g2 =>
          GConj (minify_goal es nus g1)
                (minify_goal es nus g2)
        | GGoal e =>
          GGoal (instantiate (do_instantiate cs base es) 0 e)
        | GSolved => GSolved
      end.
  End minify.

  Definition MINIFY : rtacK typ expr :=
    fun tus tvs nus nvs c cs g =>
      More cs (@minify_goal nus c cs nil nus g).

  Theorem MINIFY_sound : rtacK_sound MINIFY.
  Admitted.

End parameterized.
