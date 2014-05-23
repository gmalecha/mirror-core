Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.HList.

Set Implicit Arguments.
Set Strict Implicit.

Module Type Context.
  Parameter iT : Type.

  Section denoted.
    Variable Denote : iT -> Type.

    Parameter Env : (iT -> Type) -> list iT -> Type.
    Parameter Env_nil : Env Denote nil.
    Parameter Env_weaken : forall ts ts', Env Denote (ts ++ ts') -> Env Denote ts.
    Parameter Env_tl : forall t ts, Env Denote (t :: ts) -> Env Denote ts.


    (** Dependent contexts are like [Pi]s **)
    Parameter DCtx : forall ts : list iT, (Env Denote ts -> Type) -> Type.

    Parameter eval_Ctx : forall ts F, DCtx F -> forall x : Env Denote ts, F x.

    Parameter dpure : forall ts F, (forall x : Env Denote ts, F x) -> @DCtx ts F.
    Parameter dap   : forall ts F G,
                        @DCtx ts (fun x => F x -> G x) ->
                        @DCtx ts F ->
                        @DCtx ts G.
    Parameter dfmap : forall ts F G,
                        (forall x : Env Denote ts, F x -> G x) ->
                        @DCtx ts F ->
                        @DCtx ts G.

    Parameter DCtx_weaken
    : forall ts ts' F,
        @DCtx ts F ->
        @DCtx (ts ++ ts') (fun x => F (Env_weaken ts ts' x)).

    (** Quantify **)
    Parameter Quant_DCtx
    : forall {ks : list iT} {T : Env Denote ks -> Type} {k : iT},
        (forall e, (Denote k -> T e) -> T e) ->
        @DCtx (cons k ks) (fun g => T (Env_tl g)) -> @DCtx ks T.

    Parameter Use_DCtx'
    : forall {ks k} (m : member k ks), @DCtx ks (fun _ => Denote k).

    Parameter Env_get : forall k ks, member k ks -> Env Denote ks -> Denote k.

    Parameter Use_DCtx
    : forall {ks k} (m : member k ks)
             (F : Denote k -> Type) (ret : forall v, F v),
        @DCtx ks (fun e => F (Env_get m e)).

    (** Contexts **)
    Definition Ctx ts T : Type :=
      @DCtx ts (fun _ => T).

    Definition Applicative_Ctx {ks} : Applicative (Ctx ks) :=
      {| pure := fun _ X => dpure _ (fun _ : Env Denote ks => X)
         ; ap := fun (A B : Type) (f : DCtx (fun _ : Env Denote ks => A -> B))
                     (x : DCtx (fun _ : Env Denote ks => A)) => dap _ f x
      |}.

    Definition Functor_Ctx {ks} : Functor (Ctx ks) :=
      {| fmap := fun (A B : Type) (X : A -> B) (X0 : Ctx ks A) =>
                   dfmap _ (fun _ : Env Denote ks => X) X0 |}.

    Definition Ctx_weaken ks ks' T (ctx : Ctx ks T) : Ctx (ks ++ ks') T :=
      @DCtx_weaken ks ks' (fun _ => T) ctx.

    Definition Quant_Ctx (T : Type) {k : iT} {ks : list iT}
               (Q : (Denote k -> T) -> T)
               (ctx : Ctx (cons k ks) T)
    : Ctx ks T :=
      Quant_DCtx (fun _ : Env Denote ks => Q) ctx.

    Definition Use_Ctx {ks k} (m : member k ks) : Ctx ks (Denote k) :=
      Use_DCtx' m.

  End denoted.

End Context.

Module Type ContextP.
  Parameter iT : Type.
End ContextP.

Module ContextHList (P : ContextP)
<: Context with Definition iT := P.iT.

  Definition iT : Type := P.iT.

  Section denoted.
    Variable Denote : iT -> Type.

    Definition Env : list iT -> Type := hlist Denote.

    Definition Env_nil : Env nil := Hnil.
    Definition Env_tl {t ts} : Env (t :: ts) -> Env ts :=
      @hlist_tl _ _ _ _.


    (** Dependent contexts are like [Pi]s **)
    Definition DCtx (ts : list iT) (F : Env ts -> Type) : Type :=
      forall env, F env.

    Definition eval_Ctx {ts F} (ctx : DCtx F) (e : Env ts) : F e :=
      ctx e.

    Definition dpure {ts F} (val : forall x : Env ts, F x) : @DCtx ts F :=
      val.

    Definition dap {ts F G }
               (f : @DCtx ts (fun x => F x -> G x))
               (x : @DCtx ts F)
    : @DCtx ts G :=
      fun e => f e (x e).

    Definition dfmap {ts F G}
               (f : forall x : Env ts, F x -> G x)
               (ctx : @DCtx ts F)
    : @DCtx ts G :=
      fun e => f e (ctx e).

    (** This operation is not valid for iterated environments! **)
    Definition Env_weaken {ts ts'} (ctx : Env (ts ++ ts')) : Env ts :=
      fst (hlist_split ts ts' ctx). (** This requires a weakening **)

    Definition DCtx_weaken {ts ts' F}
               (ctx : @DCtx ts F)
    : @DCtx (ts ++ ts') (fun x => F (Env_weaken x)) :=
      fun e => ctx _.

    (** Quantify **)
    Definition Quant_DCtx
               {ks : list iT} {T : Env ks -> Type} {k : iT}
               (Q : forall e, (Denote k -> T e) -> T e)
               (v : @DCtx (cons k ks) (fun g => T (Env_tl g)))
    :  @DCtx ks T :=
      fun env => Q env (fun (x : _) => v (Hcons x env)).

    Definition Env_get {k ks} (m : member k ks) : Env ks -> Denote k :=
      @hlist_get _ _ _ _ m.

    Definition Use_DCtx' {ks k} (m : member k ks)
    : @DCtx ks (fun _ => Denote k) :=
      fun e => hlist_get m e.

    Definition Use_DCtx {ks k} (m : member k ks)
               (F : Denote k -> Type) (ret : forall v, F v)
    : @DCtx ks (fun e => F (hlist_get m e)) :=
      fun e => ret (Env_get m e).

    (** Contexts **)
    Definition Ctx ts T : Type :=
      @DCtx ts (fun _ => T).

    Definition Applicative_Ctx {ks} : Applicative (Ctx ks) :=
      {| pure := fun _ X => dpure (fun _ : Env ks => X)
         ; ap := fun (A B : Type) (f : DCtx (fun _ : Env ks => A -> B))
                     (x : DCtx (fun _ : Env ks => A)) => dap f x
      |}.

    Definition Functor_Ctx {ks} : Functor (Ctx ks) :=
      {| fmap := fun (A B : Type) (X : A -> B) (X0 : Ctx ks A) =>
                   dfmap (fun _ : Env ks => X) X0 |}.

    Definition Ctx_weaken ks ks' T (ctx : Ctx ks T) : Ctx (ks ++ ks') T :=
      @DCtx_weaken ks ks' (fun _ => T) ctx.

    Definition Quant_Ctx (T : Type) {k : iT} {ks : list iT}
               (Q : (Denote k -> T) -> T)
               (ctx : Ctx (cons k ks) T)
    : Ctx ks T :=
      Quant_DCtx (fun _ : Env ks => Q) ctx.

    Definition Use_Ctx {ks k} (m : member k ks) : Ctx ks (Denote k) :=
      Use_DCtx' m.
  End denoted.

End ContextHList.
