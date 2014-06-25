Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.SubstI3.

Set Implicit Arguments.
Set Strict Implicit.

Section cascade_subst.
  Variable expr : Type.
  (** These are really more like a functor **)
  Variable Usubst : Type.
  Variable Subst_Usubst : Subst Usubst expr.
  Variable SubstUpdate_Usubst : SubstUpdate Usubst expr.

  Variable Lsubst : Type.
  Variable Subst_Lsubst : Subst Lsubst expr.
  Variable SubstUpdate_Lsubst : SubstUpdate Lsubst expr.

  Variable lift : nat -> expr -> expr.
  Variable lower : nat -> expr -> option expr.

  Record CascadeSubst : Type :=
  { belowVars  : nat
  ; insertVars : nat
  ; lowerSubst : Lsubst
  ; upperSubst : Usubst
  }.

  Instance Subst_CascadeSubst : Subst CascadeSubst expr :=
  { lookup := fun u s =>
                if u ?[ lt ] s.(belowVars) then
                  match lookup u s.(lowerSubst) with
                    | None => None
                    | Some e =>
                      Some (lift s.(insertVars) e)
                  end
                else
                  lookup u s.(upperSubst)
  ; domain := fun s =>
                List.app (domain s.(lowerSubst)) (domain s.(upperSubst))
  }.

  Variable mentions_any : (nat -> bool) -> expr -> bool.
  Variable instantiate : (nat -> nat -> option expr) -> nat -> expr -> expr.

  Instance SubstUpdate_CascadeSubst : SubstUpdate CascadeSubst expr :=
  { (** NOTE: [empty] doesn't make a lot of sense since a lot of the custom
     ** substitutions need more information.
     **)
    empty := {| belowVars := 0
              ; insertVars := 0
              ; lowerSubst := @empty _ _ _
              ; upperSubst := @empty _ _ _
              |}
  ; set   := fun u e sub =>
               if u ?[ lt ] sub.(belowVars) then
                 let e' :=
                     instantiate (fun u n =>
                                    match lookup u sub.(upperSubst) with
                                      | None => None
                                      | Some e => Some (lift n e)
                                    end)
                                 0 e
                 in
                 if mentions_any
                      (fun u => u ?[ ge ] sub.(belowVars))
                      e'
                 then
                   None
                 else
                   match lower sub.(insertVars) e' with
                     | None => None
                     | Some e =>
                       match set u e sub.(lowerSubst) with
                         | None => None
                         | Some sub' =>
                           Some {| belowVars := sub.(belowVars)
                                 ; insertVars := sub.(insertVars)
                                 ; lowerSubst := sub'
                                 ; upperSubst :=
                                     (** I need to instantiate this **)
                                     sub.(upperSubst)
                                |}
                       end
                   end
               else
                 match set u e sub.(upperSubst) with
                   | None => None
                   | Some sub' =>
                     Some {| belowVars := sub.(belowVars)
                           ; insertVars := sub.(insertVars)
                           ; lowerSubst := sub.(lowerSubst)
                           ; upperSubst := sub'
                           |}
                 end
  ; pull  := fun from count sub =>
               if from ?[ ge ] sub.(belowVars) then
                 match pull from count sub.(upperSubst) with
                   | None => None
                   | Some sub' =>
                     Some {| belowVars := sub.(belowVars)
                           ; insertVars := sub.(insertVars)
                           ; lowerSubst := sub.(lowerSubst)
                           ; upperSubst := sub' |}
                 end
               else
                 None
  }.

  Definition over (l : Lsubst) (s : Usubst) (u : nat) (n : nat) : CascadeSubst :=
  {| belowVars := u
   ; insertVars := n
   ; lowerSubst := l
   ; upperSubst := s
   |}.
End cascade_subst.

(*
Require MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import McExamples.Simple.Simple.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Option.

Let update_above :=
  (FMapSubst3.SUBST.SubstUpdate_subst
                                   (@mentionsU typ func)
                                   (@instantiate typ func)).
Let Subst_subst : Subst (CascadeSubst _ _) (expr typ func) :=
  @Subst_CascadeSubst _ _ (FMapSubst3.SUBST.Subst_subst _) _ (FMapSubst3.SUBST.Subst_subst _) (@lift _ _ 0).

Section inst_2.
  Variables typ func : Type.
  Variable lookup : uvar -> nat -> option (expr typ func).

  Fixpoint instantiate (u : nat) (e : expr typ func)
  : expr typ func :=
    match e with
      | Var _ => e
      | Inj _ => e
      | App l r => App (instantiate u l) (instantiate u r)
      | Abs t e =>
        Abs t (instantiate (S u) e)
      | UVar uv =>
        match lookup uv u with
          | None => UVar uv
          | Some e => e
        end
    end.

  Variable check : uvar -> bool.
  Fixpoint mentions_any (e : expr typ func) : bool :=
    match e with
      | Var _ => false
      | Inj _ => false
      | App l r => if mentions_any l then true else mentions_any r
      | Abs t e => mentions_any e
      | UVar uv => check uv
    end.
End inst_2.

Let SubstUpdate_subst : SubstUpdate (CascadeSubst _ _) (expr typ func) :=
  @SubstUpdate_CascadeSubst _ _
                            (FMapSubst3.SUBST.Subst_subst _)
                            update_above
                            _
                            update_above
                            (@lift _ _ 0)
                            (@lower _ _ 0)
                            (@mentions_any _ _)
                            (@instantiate typ func).

Let empty_above : FMapSubst3.SUBST.raw (expr typ func) :=
  @empty _ _ (update_above).
Let set := @set _ _ SubstUpdate_subst.
Let lookup := @lookup _ _ Subst_subst.


Definition foo := over empty_above empty_above 1 1.
Eval compute in set 0 (Var 0) foo.
Eval compute in set 1 (Var 0) foo.
Eval compute in bind (bind (set 0 (Var 1) foo) (set 1 (Var 0))) (lookup 0).
Eval compute in bind (set 0 (UVar 1) foo) (set 1 (Var 1)).
*)