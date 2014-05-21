Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Set Printing Universes.

Fixpoint nat_eq (a b : nat) {struct a} : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | 0 , 0 => Some eq_refl
    | S a , S b => match nat_eq a b with
                     | Some pf =>
                       Some match pf in _ = t return S a = S t with
                              | eq_refl => eq_refl
                            end
                     | None => None
                   end
    | _ , _ => None
  end.


Module Type Context.
  Parameter iT : Type.
  Parameter Denote : iT -> Type.

  (** Contexts are like [->]s **)
  Parameter Ctx : list iT -> Type -> Type.

  Parameter eval_Ctx : forall T, Ctx nil T -> T.

  Parameter Applicative_Ctx : forall ks, Applicative (Ctx ks).
  Parameter Functor_Ctx : forall ks, Functor (Ctx ks).

  (** TODO: There should be a naturality property about this,
   ** i.e. how it interacts with [ap], [pure], and [fmap]
   **)
  Parameter Ctx_weaken
  : forall ks ks' T, Ctx ks T -> Ctx (ks ++ ks') T.

  (** Quantify **)
  Parameter Quant_Ctx
  : forall (T : Type) {k : iT} {ks : list iT},
      ((Denote k -> T) -> T) ->
      Ctx (cons k ks) T -> Ctx ks T.

  Parameter Use_Ctx
  : forall {ks k} (m : member k ks), Ctx ks (Denote k).

  (** TODO: I need dependent contexts for expressions **)

End Context.

Module Type ContextP.
  Parameter iT : Type.
  Parameter Denote : iT -> Type.
End ContextP.

Module Type ContextBuilder (P : ContextP)
:= Context with Definition iT := P.iT
           with Definition Denote := P.Denote.

Module ContextHList (P : ContextP)
<: Context with Definition iT := P.iT
          with Definition Denote := P.Denote.
  Require ExtLib.Data.HList.

  Definition iT : Type := P.iT.
  Definition Denote : iT -> Type := P.Denote.

  Definition Ctx (ls : list iT) (T : Type) : Type :=
    HList.hlist Denote ls -> T.

  Definition eval_Ctx T (c : Ctx nil T) : T :=
    c HList.Hnil.

  Definition Applicative_Ctx {ks} : Applicative (Ctx ks) :=
  {| pure := fun _ val _ => val
   ; ap := fun _ _ f x vs => f vs (x vs)
   |}.

  Definition Functor_Ctx {ks} : Functor (Ctx ks) :=
  {| fmap := fun _ _ f x => fun vs => f (x vs) |}.

  Definition Ctx_weaken ks ks' T (ctx : Ctx ks T) : Ctx (ks ++ ks') T :=
    fun vs_vs' => let (vs,_) := HList.hlist_split ks ks' vs_vs' in ctx vs.

  Definition Quant_Ctx (T : Type) {k : iT} {ks : list iT}
             (Q : (Denote k -> T) -> T)
             (ctx : Ctx (cons k ks) T)
  : Ctx ks T :=
    fun vs => Q (fun v => ctx (HList.Hcons v vs)).

  Fixpoint Use_Ctx {ks k} (m : member k ks) : Ctx ks (Denote k) :=
    hlist_get m.
End ContextHList.
