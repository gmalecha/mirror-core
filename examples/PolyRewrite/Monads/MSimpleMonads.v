(** This is a very simple monadic language that
 ** can be useful for testing.
 **)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
<<<<<<< HEAD:examples/PolyRewrite/MSimpleMonads.v
Require Import MirrorCore.Types.ModularTypes.
Require Import MirrorCore.Types.TSymOneOf.
=======
Require Import MirrorCore.CTypes.CoreTypes.
Require Import MirrorCore.CTypes.CTypeUnify.
Require Import MirrorCore.CTypes.TSymOneOf.

>>>>>>> master:examples/PolyRewrite/Monads/MSimpleMonads.v

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ' : nat -> Type :=
| tyNat : typ' 0
| tyBool : typ' 0
| tyMonad : typ' 1.

Definition typ'_dec n (a : typ' n) : forall b : typ' n, {a = b} + {a <> b}.
refine
  match a as a in typ' n return forall b : typ' n, {a = b} + {a <> b} with
  | tyNat => fun b =>
              match b as b in typ' k return (match k return typ' k -> Type with
                                             | 0 => fun t => {tyNat = t} + {tyNat <> t}
                                             | _ => fun _ => unit end b) with
               | tyNat => left eq_refl
               | tyBool => right _
               | tyMonad => tt
               end
  | tyBool => fun b =>
               match b as b in typ' 0 return {_ = b} + {_ <> b} with
               | tyBool => left eq_refl
               | tyNat => right _
               end
  | tyMonad => fun b =>
               match b as b in typ' 1 return {tyMonad = b} + {tyMonad <> b} with
               | tyMonad => left eq_refl
               end
  end; try (intro H; inversion H).
Defined.

Require Import ExtLib.Structures.Monad.
Require Import McExamples.PolyRewrite.Monads.Monad.
Module TheMonad (M : Monad) (F : Frob M).
  Import M.
  Import F.

    Instance TSym_typ' : TSym typ' :=
    { symbolD n s :=
        match s with
        | tyNat => nat
        | tyBool => bool
        | tyMonad => M
        end
    ; symbol_dec := typ'_dec }.

    Definition typ := ctyp typ'.

    Global Instance RType_typ : RType typ := RType_ctyp _ _.
    Global Instance RTypeOk_typ : @RTypeOk _ RType_typ := RTypeOk_ctyp _ _.

    Inductive func :=
    | Lt | Plus | N : nat -> func | Eq : typ -> func
    | Ex : typ -> func | All : typ -> func
    | And | Or | Impl | Bind : typ -> typ -> func | Ret : typ -> func | Frob : func.


    (* slower version if we don't know how many vars we need *)
    Definition func_unify_slow (a b : func) (s : FMapPositive.pmap typ) : option (FMapPositive.pmap typ) :=
      match a , b with
      | Lt , Lt
      | Plus , Plus
      | Frob, Frob
      | N _ , N _
      | And , And
      | Or , Or
      | Impl , Impl => Some s
      | Ret t , Ret t'
      | Eq t , Eq t'
      | Ex t , Ex t'
      | All t , All t' => ctype_unify_slow _ t t' s
      | Bind a b , Bind a' b'  =>
        match ctype_unify_slow _ a a' s with
        | Some s' => ctype_unify_slow _ b b' s
        | None => None
        end
      | _ , _ => None
      end.

    (* n is how many variables we are trying to discover *)    
    Definition func_unify (n : nat) (a b : func) (s : FMapPositive.pmap typ) : option (FMapPositive.pmap typ) :=
      match n with
      | S _ =>
        match a , b with
        | Lt , Lt
        | Plus , Plus
        | Frob, Frob
        | N _ , N _
        | And , And
        | Or , Or
        | Impl , Impl => Some s
        | Ret t , Ret t'
        | Eq t , Eq t'
        | Ex t , Ex t'
        | All t , All t' =>
          match ctype_unify _ n t t' s with
          | Some (s', _) => Some s'
          | _ => None
          end
        | Bind a b , Bind a' b'  =>
          match ctype_unify _ n a a' s with
          | Some (s', S k) =>
            match ctype_unify _ (S k) b b' s' with
            | Some (s'', _) => Some s''
            | _ => None
            end
          | Some (s', 0) => Some s'
          | None => None
          end
        | _ , _ => None
        end
      | 0 => Some s
      end.

    Local Notation "! x" := (@tyBase0 _ x) (at level 0).
    Definition typeof_func (f : func) : option typ :=
      Some match f with
           | Lt => tyArr !tyNat (tyArr !tyNat !tyBool)
           | Plus => tyArr !tyNat (tyArr !tyNat !tyNat)
           | N _ => !tyNat
           | Eq t => tyArr t (tyArr t tyProp)
           | And | Or | Impl => tyArr tyProp (tyArr tyProp tyProp)
           | Ex t | All t => tyArr (tyArr t tyProp) tyProp
           | Bind alpha beta => tyArr (tyBase1 tyMonad alpha) (tyArr (tyArr alpha (tyBase1 tyMonad beta)) (tyBase1 tyMonad beta))
           | Ret alpha => tyArr alpha (tyBase1 tyMonad alpha)
           | Frob => tyArr (tyBase0 tyNat) (tyBase1 tyMonad (tyBase0 tyNat))
           end.

    Definition funcD (f : func)
      : match typeof_func f with
        | None => unit
        | Some t => typD t
        end :=
      match f as f return match typeof_func f with
                          | None => unit
                          | Some t => typD t
                          end
      with
      | Lt => NPeano.Nat.ltb
      | Plus => plus
      | N n => n
      | Eq t => @eq _
      | And => and
      | Or => or
      | Impl => fun (P Q : Prop) => P -> Q
      | All t => fun P => forall x : typD t, P x
      | Ex t => fun P => exists x : typD t, P x
      | Bind a b => bind
      | Ret a => ret
      | Frob => frob
      end.

    Let RelDec_eq_typ : RelDec (@eq typ) := RelDec_Rty _.
    Local Existing Instance RelDec_eq_typ.

    Instance RelDec_eq_func : RelDec (@eq func) :=
      { rel_dec := fun (a b : func) =>
                     match a , b with
                     | Plus , Plus => true
                     | Lt , Lt => true
                     | N a , N b => a ?[ eq ] b
                     | Eq a , Eq b => a ?[ eq ] b
                     | And , And
                     | Impl , Impl
                     | Or , Or => true
                     | All a , All b
                     | Ex a , Ex b => a ?[ eq ] b
                     | Bind a b, Bind a' b' => andb (a ?[eq] a') (b ?[eq] b')
                     | Ret a, Ret a' => a ?[eq] a'
                     | Frob, Frob => true
                     | _ , _ => false
                     end
      }.

    Instance RelDecCorrect_eq_func : RelDec_Correct RelDec_eq_func.
    Proof.
      constructor.
      destruct x; destruct y; simpl;
      try solve [ tauto
                | split; congruence
                | rewrite rel_dec_correct; split; congruence
                ].
      split.
      { intros. apply andb_prop in H. destruct H.
        rewrite rel_dec_correct in H. rewrite rel_dec_correct in H0.
        subst; auto. }
      { intros. inversion H. subst.
        do 2 (rewrite rel_dec_eq_true; [|eauto with typeclass_instances|reflexivity]).
        reflexivity. }
    Qed.

    Instance RSym_func : RSym func :=
      { typeof_sym := typeof_func
        ; symD := funcD
        ; sym_eqb := fun a b => Some (a ?[ eq ] b)
      }.

    Instance RSymOk_func : RSymOk RSym_func.
    { constructor.
      intros. simpl. consider (a ?[ eq ] b); auto. }
    Qed.

End TheMonad.