Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Set Printing Universes.

Module Context.
  Parameter iT : Type.
  Parameter Denote : iT -> Type.

  Definition Env : list iT -> Type :=
    hlist Denote.

  (** Dependent contexts are like [Pi]s **)
  Definition DCtx (ts : list iT) (F : forall ts, Env ts -> Type) : Type :=
    forall x : Env ts, F ts x.

  Definition eval_Ctx ts F (ctx : DCtx ts F) (x : Env ts) : F ts x :=
    ctx x.

  (** TODO: All of these look a little bit funny **)
  Definition dpure {ts} {F : forall ts, Env ts -> Type} (val : forall x : Env ts, F ts x) : @DCtx ts F := val.

  Definition dap {ts} {F G : forall ts, Env ts -> Type}
             (f : @DCtx ts (fun ts x => F ts x -> G ts x))
             (x : @DCtx ts F)
  : @DCtx ts G :=
    fun e => f e (x e).

  Definition dfmap {ts} {F G : forall ts, Env ts -> Type}
             (f : forall x : Env ts, F ts x -> G ts x)
             (x : @DCtx ts F)
  : @DCtx ts G :=
    fun e => f e (x e).

  Definition Env_join {ts ts'} : Env ts -> Env ts' -> Env (ts ++ ts') :=
    @hlist_app _ _ _ _.

(*  Parameter Env_weaken : forall ts ts', Env (ts ++ ts') -> Env ts. *)
  Definition DCtx_weaken {ts ts' F} (ctx : @DCtx ts F)
    (F_weaken : forall es es', F ts es -> F (List.app ts ts') (Env_join es es'))
  : @DCtx (ts ++ ts') F.
    red. red in ctx.
    intros. specialize (ctx (fst (hlist_split ts ts' x))).
    rewrite <- hlist_app_hlist_split.
    eapply F_weaken. eapply ctx.
  Defined.

  (** Quantify **)
  (** TODO: Something about this is strange! **)
  Definition Quant_Ctx {ks : list iT} F {k : iT}
             (Q : forall ks e, (Denote k -> F ks e) -> F ks e)
             (v : @DCtx (cons k ks) F)
  : @DCtx ks F.
    refine (fun es => _).
    eapply Q.
    refine (fun x => _).
    red in v.
    specialize (v (Hcons x es)).
  Admitted.

  Definition Use_DCtx {ks k} (m : member k ks) : @DCtx ks (fun _ _ => Denote k).
  Admitted.

End Context.
