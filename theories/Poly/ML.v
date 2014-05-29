Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import MirrorCore.Poly.TypeI.
Require Import MirrorCore.Poly.Ctx.

Set Implicit Arguments.
Set Strict Implicit.

(** ML-style polymorphism **)
Definition UU := Type.
Definition U1 : UU := Type.
Definition U0 : U1 := Type.

Inductive kind1 := kTy1.

Definition kind1D (_ : kind1) : UU :=
  U1.

Inductive kind0 :=
| kTy0 : kind0
| kArr0 : kind0 -> kind0 -> kind0.

Fixpoint kind0D (k : kind0) (b : kind1) : kind1D b :=
  match k with
    | kTy0 => U0
    | kArr0 k1 k2 => kind0D k1 b -> kind0D k2 b
  end.
Definition kind0D' (k : kind0) : U1 := kind0D k kTy1.

Fixpoint kind0_eq (k1 k2 : kind0) : option (k1 = k2) :=
  match k1 as k1 , k2 as k2 return option (k1 = k2) with
    | kTy0 , kTy0 => Some eq_refl
    | kArr0 l1 l2 , kArr0 r1 r2 =>
      match kind0_eq l1 r1 , kind0_eq l2 r2 with
        | Some pf1 , Some pf2 =>
          Some match pf1 in _ = l , pf2 in _ = r
                     return (kArr0 l1 l2 = kArr0 l r) with
                 | eq_refl , eq_refl => eq_refl
               end
        | _ , _ => None
      end
    | _ , _ => None
  end.

Fixpoint kind1_eq (k1 k2 : kind1) : option (k1 = k2) :=
  Some match k1 as k1 , k2 as k2 return k1 = k2 with
         | kTy1 , kTy1 => eq_refl
       end.

(*
Record TypeCtor : Type :=
{ Kind : kind0
; Value : kind0D Kind kTy1
}.
*)

Module Type MLExt.
  Parameter ext : Type.
  Parameter kindof_ext : ext -> option kind0.
  Parameter extD : forall e : ext, match kindof_ext e with
                                     | None => unit
                                     | Some k => kind0D k kTy1
                                   end.
  Parameter ext_eq : forall a b : ext, option (a = b).
End MLExt.

Module ML (Ext : MLExt) (* (MkCtx : ContextBuilder) *).
  Module CtxP_skind <: ContextP.
    Definition iT := kind0.
  End CtxP_skind.

  Module Ctx := ContextHList CtxP_skind.

  Existing Instance Ctx.Applicative_Ctx.
  Existing Instance Ctx.Functor_Ctx.

  Inductive typ0 :=
  | tApp : typ0 -> typ0 -> typ0
  | tArr : typ0 -> typ0 -> typ0
  | tVar : nat -> typ0
  | tExt : Ext.ext -> typ0.

  Inductive typ1 :=
  | tPi : kind0 -> typ1 -> typ1
  | tLift : typ0 -> typ1
(*  | tArr1 : typ1 -> typ1 -> typ1 -- needed for non-type schemes *)
  .

  Fixpoint kindof_typ0 (ss : list kind0) (t : typ0) : option kind0 :=
    match t with
      | tExt e => Ext.kindof_ext e
      | tApp l r => match kindof_typ0 ss r
                        , kindof_typ0 ss l
                     with
                       | Some r , Some (kArr0 ld lr) =>
                         if kind0_eq ld r then Some lr else None
                       | _ , _ => None
                     end
      | tArr t1 t2 => match kindof_typ0 ss t1
                          , kindof_typ0 ss t2
                      with
                        | Some kTy0 , Some kTy0 => Some kTy0
                        | _ , _ => None
                      end
      | tVar n => nth_error ss n
    end.

  Fixpoint kindof_typ1 (ss : list kind0) (t : typ1) : option kind1 :=
    match t with
      | tLift t => match kindof_typ0 ss t with
                     | Some kTy0 => Some kTy1
                     | _ => None
                   end
      | tPi k t => match kindof_typ1 (k :: ss) t with
                   | Some s' => Some kTy1
                   | None => None
                 end
    end.

  Fixpoint lift_typ0 (skip _by : nat) (t : typ0) {struct t} : typ0 :=
    match t with
      | tExt e => tExt e
      | tApp t1 t2 => tApp (lift_typ0 skip _by t1) (lift_typ0 skip _by t2)
      | tVar n => tVar (if n ?[ lt ] skip then n else (n + _by))
      | tArr t1 t2 => tArr (lift_typ0 skip _by t1) (lift_typ0 skip _by t2)
    end.

  Fixpoint lift_typ1 (skip _by : nat) (t : typ1) {struct t} : typ1 :=
    match t with
      | tPi k t => tPi k (lift_typ1 (S skip) _by t)
      | tLift t => tLift (lift_typ0 skip _by t)
    end.

  Fixpoint typ0_sub (s : typ0) (skip : nat) (s' : typ0) : typ0 :=
    match s with
      | tExt e => tExt e
      | tApp t1 t2 => tApp (typ0_sub t1 skip s') (typ0_sub t2 skip s')
      | tVar n =>
        if n ?[ eq ] skip then s'
        else if n ?[ lt ] skip then tVar n
             else tVar (pred n)
      | tArr t1 t2 => tArr (typ0_sub t1 skip s') (typ0_sub t2 skip s')
    end.

  Fixpoint typ1_sub (s : typ1) (skip : nat) (s' : typ0) : typ1 :=
    match s with
      | tPi k t => tPi k (typ1_sub t (S skip) (lift_typ0 0 1 s'))
      | tLift t => tLift (typ0_sub t skip s')
    end.

  Fixpoint typ0_eq (a b : typ0) {struct a} : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | tApp a1 a2 , tApp b1 b2 =>
        match typ0_eq a1 b1 , typ0_eq a2 b2 with
          | Some pf1 , Some pf2 =>
            Some match pf1 in _ = t1 , pf2 in _ = t2
                       return tApp a1 a2 = tApp t1 t2
                 with
                   | eq_refl , eq_refl => eq_refl
                 end
          | _ , _ => None
        end
      | tArr a1 a2 , tArr b1 b2 =>
        match typ0_eq a1 b1 , typ0_eq a2 b2 with
          | Some pf1 , Some pf2 =>
            Some match pf1 in _ = t1 , pf2 in _ = t2
                       return tArr a1 a2 = tArr t1 t2
                 with
                   | eq_refl , eq_refl => eq_refl
                 end
          | _ , _ => None
        end
      | tVar a , tVar b =>
        match nat_eq a b with
          | Some pf => Some (f_equal tVar pf)
          | None => None
        end
      | tExt a , tExt b =>
        match Ext.ext_eq a b with
          | Some pf => Some (f_equal tExt pf)
          | None => None
        end
      | _ , _ => None
    end.

  Fixpoint typ1_eq (a b : typ1) {struct a} : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | tPi ka a , tPi kb b =>
        match kind0_eq ka kb , typ1_eq a b with
          | Some pfk , Some pf =>
            Some match pfk in _ = k , pf in _ = t return tPi ka a = tPi k t with
                   | eq_refl , eq_refl => eq_refl
                 end
          | _ , _ => None
        end
      | tLift a , tLift b =>
        match typ0_eq a b with
          | Some pf => Some (f_equal tLift pf)
          | _ => None
        end
      | _ , _ => None
    end.


  (** Forall **)
  Definition Quant_Ctx
  : forall (T : UU) {k : kind0} {ks : list kind0},
      ((kind0D' k -> T) -> T) ->
      Ctx.Ctx kind0D' (k :: ks) T -> Ctx.Ctx kind0D' ks T :=
    @Ctx.Quant_Ctx kind0D'.

  (** Arrow **)
  Definition Arr0_Ctx {ks : list kind0}
             (L R : Ctx.Ctx kind0D' ks (kind0D' kTy0))
  : Ctx.Ctx kind0D' ks (kind0D' kTy0) :=
    ap (ap (pure (fun l r => l -> r)) L) R.

  (** Application **)
  Definition App_Ctx {ks : list kind0} {k k' : kind0}
             (F : Ctx.Ctx kind0D' ks (kind0D' (kArr0 k' k)))
             (X : Ctx.Ctx kind0D' ks (kind0D' k'))
  : Ctx.Ctx kind0D' ks (kind0D' k) :=
    ap (ap (pure (fun f x => f x)) F) X.

  (** Injection **)
  Definition Inj_Ctx {ks : list kind0} (k : kind0) (val : kind0D' k)
  : Ctx.Ctx kind0D' ks (kind0D' k) := pure val.

  Fixpoint typD0 (ks : list kind0) (t : typ0) (k : kind0)
  : option (Ctx.Ctx kind0D' ks (kind0D' k)) :=
    match t with
      | tArr t t' =>
        match k as k return option (Ctx.Ctx kind0D' ks (kind0D' k))
        with
          | kTy0 =>
            match typD0 ks t kTy0 , typD0 ks t' kTy0 with
              | Some K , Some T => Some (Arr0_Ctx K T)
              | _ , _ => None
            end
          | _ => None
        end
      | tApp t t' =>
        match kindof_typ0 ks t' with
          | Some k' =>
            match typD0 ks t' k' , typD0 ks t (kArr0 k' k) with
              | Some T , Some F => Some (App_Ctx F T)
              | _ , _ => None
            end
          | _ => None
        end
      | tVar v =>
        match nth_member ks v with
          | Some (existT k' m) =>
            match kind0_eq k' k with
              | Some pf => Some match pf in _ = kk
                                      return Ctx.Ctx kind0D' ks (kind0D' kk)
                                with
                                  | eq_refl => Ctx.Use_Ctx m
                                end
              | None => None
            end
          | _ => None
        end
      | tExt u =>
        match Ext.kindof_ext u as koe
              return match koe with
                       | None => unit
                       | Some k => kind0D' k
                     end -> _
        with
          | Some k' =>
            match kind0_eq k' k with
              | Some pf => fun f =>
                Some (match pf in _ = k
                            return kind0D' k' -> Ctx.Ctx kind0D' ks (kind0D' k) with
                        | eq_refl => fun v => Inj_Ctx _ v
                      end f)
              | None => fun _ => None
            end
          | None => fun _ => None
        end (Ext.extD u)
    end.

  Fixpoint typD1 (ks : list kind0) (t : typ1) (k : kind1)
  : option (Ctx.Ctx kind0D' ks (kind1D k)) :=
    match t with
      | tPi k' t =>
        match k as k return option (Ctx.Ctx kind0D' ks (kind1D k))
        with
          | kTy1 =>
            match typD1 (cons k' ks) t kTy1 with
              | Some T =>
                Some (Quant_Ctx (k := k')
                                (fun P => forall x : kind0D k' kTy1, P x) T)
              | _ => None
            end
        end
      | tLift t =>
        match k as k return option (Ctx.Ctx kind0D' ks (kind1D k)) with
          | kTy1 =>
            fmap (fmap (fun x : U0 => x : U1)) (typD0 ks t kTy0)
        end
    end.

  Fixpoint typD1_weaken ks ks' t {struct t}
  : match typD1 ks t kTy1 , typD1 (ks ++ ks') t kTy1 return Type with
      | Some T , Some T' =>
        @Ctx.DCtx kind0D' ks (fun env =>
                                @Ctx.eval_Ctx kind0D' ks (fun _ => kind1D kTy1) T env ->
                                @Ctx.DCtx kind0D' ks' (fun env' =>
                                                         @Ctx.eval_Ctx kind0D' (ks ++ ks') (fun _ => kind1D kTy1) T'
                                                                       (hlist_app env env')))

      | Some _ , None => Empty_set
      | None , _ => unit
    end.
    (** TODO: There has got to be a cleaner statement for this **)
(*
    destruct t; simpl.
    { specialize (typD_weaken (kTy :: ks) ks' t k).
      simpl in *.
      destruct k; try solve [ refine (fun x => x) ].
      destruct (typD (kTy :: ks) t kTy). 2: destruct 1.
      match goal with
        | H : context [ match ?X with _ => _ end ]
          |- context [ match ?Y with _ => _ end ] =>
          change Y with X ; destruct X
      end.
      refine (fun x => x).
      intro. apply typD_weaken. apply c. }
    { generalize (typD_weaken ks ks' t1 (kArr kTy k)).
      generalize (typD_weaken ks ks' t2 kTy).
      clear.
      destruct (typD ks t2 kTy). 2: destruct 3.
      destruct (typD ks t1 (kArr kTy k)). 2: destruct 3.
      destruct (typD (ks ++ ks') t2 kTy).
      { destruct (typD (ks ++ ks') t1 (kArr kTy k)); auto. }
      { auto. } }
    { destruct k; auto.
      generalize (typD_weaken ks ks' t1 kTy).
      generalize (typD_weaken ks ks' t2 kTy).
      clear.
      destruct (typD ks t1 kTy);
      destruct (typD ks t2 kTy);
      destruct (typD (ks ++ ks') t1 kTy);
      destruct (typD (ks ++ ks') t2 kTy); auto. }
    { destruct (skindD_to_kindD k); auto.
      clear. admit. }
    { clear. admit. }
*)
  Admitted.

End ML.
