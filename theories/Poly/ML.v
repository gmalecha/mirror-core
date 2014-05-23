Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Poly.TypeI.
Require Import MirrorCore.Poly.Ctx.

Set Implicit Arguments.
Set Strict Implicit.

(** ML-style polymorphism **)
Definition UU := Type.
Definition Ustar : UU := Type.
Definition Usmall : Ustar := Type.

Inductive kind :=
| kTy : kind
| kArr : kind -> kind -> kind.

Fixpoint kindD (k : kind) : UU :=
  match k with
    | kTy => Ustar
    | kArr k1 k2 => kindD k1 -> kindD k2
  end.

Fixpoint kind_eq (k1 k2 : kind) : option (k1 = k2) :=
  match k1 as k1 , k2 as k2 return option (k1 = k2) with
    | kTy , kTy => Some eq_refl
    | kArr l1 l2 , kArr r1 r2 =>
      match kind_eq l1 r1 , kind_eq l2 r2 with
        | Some pf1 , Some pf2 =>
          Some match pf1 in _ = l , pf2 in _ = r
                     return (kArr l1 l2 = kArr l r) with
                 | eq_refl , eq_refl => eq_refl
               end
        | _ , _ => None
      end
    | _ , _ => None
  end.

Record TypeCtor : Type :=
{ Kind : kind
; Value : kindD Kind
}.

Module Type MLExt.
  Parameter ext : Type.
  Parameter kindof_ext : ext -> option kind.
  Parameter extD : forall e : ext, match kindof_ext e with
                                     | None => unit
                                     | Some k => kindD k
                                   end.
  Parameter ext_eq : forall a b : ext, option (a = b).
End MLExt.

Module ML (Ext : MLExt) (* (MkCtx : ContextBuilder) *).
  Definition skind := kind.

  Fixpoint skindD (k : skind) : Ustar :=
    match k with
      | kTy => Usmall
      | kArr k1 k2 => skindD k1 -> skindD k2
    end.

  Module CtxP_skind <: ContextP.
    Definition iT := skind.
  End CtxP_skind.

  Module Ctx := ContextHList CtxP_skind.

  Existing Instance Ctx.Applicative_Ctx.
  Existing Instance Ctx.Functor_Ctx.

  Definition skindD_to_kindD (k : kind) : option (skindD k -> kindD k) :=
    match k as k return option (skindD k -> kindD k) with
      | kTy => Some (fun x : Usmall => x : Ustar)
      | _ => None
    end.

  Inductive typ :=
  | tPi  : typ -> typ
  | tApp : typ -> typ -> typ
  | tArr : typ -> typ -> typ
  | tVar : nat -> typ
  | tExt : Ext.ext -> typ.

  Fixpoint kindof_typ (ss : list kind) (t : typ) : option kind :=
    match t with
      | tExt e => Ext.kindof_ext e
      | tApp l r => match kindof_typ ss r
                           , kindof_typ ss l
                     with
                       | Some r , Some (kArr ld lr) =>
                         if kind_eq ld r then Some lr else None
                       | _ , _ => None
                     end
      | tPi t => match kindof_typ (kTy :: ss) t with
                   | Some s' => Some (kArr kTy s')
                   | None => None
                 end
      | tArr t1 t2 => match kindof_typ ss t1
                          , kindof_typ ss t2
                      with
                        | Some kTy , Some kTy => Some kTy
                        | _ , _ => None
                      end
      | tVar n => nth_error ss n
    end.

  Fixpoint lift_typ (skip _by : nat) (t : typ) {struct t} : typ :=
    match t with
      | tExt e => tExt e
      | tApp t1 t2 => tApp (lift_typ skip _by t1) (lift_typ skip _by t2)
      | tPi t => tPi (lift_typ (S skip) _by t)
      | tVar n => tVar (if n ?[ lt ] skip then n else (n + _by))
      | tArr t1 t2 => tArr (lift_typ skip _by t1) (lift_typ skip _by t2)
    end.

  Fixpoint typ_sub (s : typ) (skip : nat) (s' : typ) : typ :=
    match s with
      | tExt e => tExt e
      | tApp t1 t2 => tApp (typ_sub t1 skip s') (typ_sub t2 skip s')
      | tPi t => tPi (typ_sub t (S skip) (lift_typ 0 1 s'))
      | tVar n =>
        if n ?[ eq ] skip then s'
        else if n ?[ lt ] skip then tVar n
             else tVar (pred n)
      | tArr t1 t2 => tArr (typ_sub t1 skip s') (typ_sub t2 skip s')
    end.

  Fixpoint typ_eq (a b : typ) {struct a} : option (a = b) :=
    match a as a , b as b return option (a = b) with
      | tPi a , tPi b =>
        match typ_eq a b with
          | Some pf => Some match pf in _ = t return tPi a = tPi t with
                              | eq_refl => eq_refl
                            end
          | _ => None
        end
      | tApp a1 a2 , tApp b1 b2 =>
        match typ_eq a1 b1 , typ_eq a2 b2 with
          | Some pf1 , Some pf2 =>
            Some match pf1 in _ = t1 , pf2 in _ = t2
                       return tApp a1 a2 = tApp t1 t2
                 with
                   | eq_refl , eq_refl => eq_refl
                 end
          | _ , _ => None
        end
      | tArr a1 a2 , tArr b1 b2 =>
        match typ_eq a1 b1 , typ_eq a2 b2 with
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
          | Some pf => Some match pf in _ = t return tVar a = tVar t with
                              | eq_refl => eq_refl
                            end
          | None => None
        end
      | tExt a , tExt b =>
        match Ext.ext_eq a b with
          | Some pf => Some match pf in _ = t return tExt a = tExt t with
                              | eq_refl => eq_refl
                            end
          | None => None
        end
      | _ , _ => None
    end.


  (** Forall **)
  Definition Quant_Ctx
  : forall (T : UU) {k : skind} {ks : list skind},
      ((skindD k -> T) -> T) ->
      Ctx.Ctx skindD (k :: ks) T -> Ctx.Ctx skindD ks T :=
    @Ctx.Quant_Ctx skindD.

  (** Arrow **)
  Definition Arr_Ctx {ks : list skind} (L R : Ctx.Ctx skindD ks (kindD kTy))
  : Ctx.Ctx skindD ks (kindD kTy) :=
    ap (ap (pure (fun l r => l -> r)) L) R.

  (** Application **)
  Definition App_Ctx {ks : list skind} {k k' : kind}
             (F : Ctx.Ctx skindD ks (kindD (kArr k' k)))
             (X : Ctx.Ctx skindD ks (kindD k'))
  : Ctx.Ctx skindD ks (kindD k) :=
    ap (ap (pure (fun f x => f x)) F) X.

  (** Injection **)
  Definition Inj_Ctx {ks : list skind} (k : kind) (val : kindD k)
  : Ctx.Ctx skindD ks (kindD k) := pure val.

  Fixpoint nth_mem_kind (ks : list skind) (k : skind) (n : nat) : option (member k ks) :=
    match ks as ks return option (member k ks) with
      | nil => None
      | cons k' ks =>
        match n with
          | 0 => match kind_eq k' k with
                   | Some pf => Some match pf in _ = kk return member kk (cons k' ks) with
                                       | eq_refl => MZ _ _
                                     end
                   | None => None
                 end
          | S n => match nth_mem_kind ks k n with
                     | Some m => Some (@MN _ _ _ _ m)
                     | None => None
                   end
        end
    end.

  Fixpoint typD (ks : list skind) (t : typ) (k : kind)
  : option (Ctx.Ctx skindD ks (kindD k)) :=
    match t with
      | tPi t =>
        match k as k return option (Ctx.Ctx skindD ks (kindD k))
        with
          | kTy =>
            match typD (cons kTy ks) t kTy with
              | Some T => Some (Quant_Ctx (k := kTy) (fun P => forall x : Usmall, P x) T)
              | _ => None
            end
          | _ => None
        end
      | tArr t t' =>
        match k as k return option (Ctx.Ctx skindD ks (kindD k))
        with
          | kTy =>
            match typD ks t kTy , typD ks t' kTy with
              | Some K , Some T => Some (Arr_Ctx K T)
              | _ , _ => None
            end
          | _ => None
        end
      | tApp t t' =>
        let k' := kTy in
        (** NOTE: This is fine since [tPi] only ranges over [*] **)
        match typD ks t' k' , typD ks t (kArr k' k) with
          | Some T , Some F => Some (App_Ctx F T)
          | _ , _ => None
        end
      | tVar v =>
        match skindD_to_kindD k , nth_mem_kind ks k v with
          | Some f , Some m => Some (@fmap _ _ _ _ f (Ctx.Use_Ctx m))
          | _ , _ => None
        end
      | tExt u =>
        match Ext.kindof_ext u as koe
              return match koe with
                       | None => unit
                       | Some k => kindD k
                     end -> _
        with
          | Some k' =>
            match kind_eq k' k with
              | Some pf => fun f =>
                Some (match pf in _ = k
                            return kindD k' -> Ctx.Ctx skindD ks (kindD k) with
                        | eq_refl => fun v => Inj_Ctx _ v
                      end f)
              | None => fun _ => None
            end
          | None => fun _ => None
        end (Ext.extD u)
    end.

  Fixpoint typD_weaken ks ks' t {struct t}
  : match typD ks t kTy , typD (ks ++ ks') t kTy return Type with
      | Some T , Some T' =>
        @Ctx.DCtx skindD ks (fun env =>
           @Ctx.eval_Ctx skindD ks (fun _ => kindD kTy) T env ->
           @Ctx.DCtx skindD ks' (fun env' =>
                            @Ctx.eval_Ctx skindD (ks ++ ks') (fun _ => kindD kTy) T'
                                          (hlist_app env env')))

      | Some _ , None => Empty_set
      | None , _ => unit
    end.
  Proof.
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
