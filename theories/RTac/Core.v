Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Data.Pair.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.ExprDAs.

Require Import MirrorCore.Util.Quant.
Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Move to Data.HList **)
Theorem rev_app_distr_trans
: forall (A : Type) (x y : list A), rev (x ++ y) = rev y ++ rev x.
Proof. clear.
       induction x; simpl; intros.
       - symmetry. apply app_nil_r_trans.
       - rewrite IHx. apply app_ass_trans.
Defined.

(** TODO: This is cubic! **)
Theorem rev_involutive_trans (A : Type)
: forall (l : list A), rev (rev l) = l.
Proof. clear.
       induction l; simpl; auto.
       rewrite rev_app_distr_trans. rewrite IHl. reflexivity.
Defined.

Definition hlist_unrev {T} {F : T -> Type} {ls} (h : hlist F (rev ls))
: hlist F ls :=
  match rev_involutive_trans ls in _ = t return hlist F t with
    | eq_refl => hlist_rev h
  end.

Ltac equivs :=
  repeat match goal with
           | H : equiv_hlist _ _ _ |- _ => apply equiv_eq_eq in H
         end; subst.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  Context {RType_typ : RType typ}.
  Context {Expr_expr : Expr RType_typ expr}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {Subst_subst : Subst subst expr}.
  Context {SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst}.
  Context {SubstUpdate_subst : SubstUpdate subst expr}.
  Context {SubstUpdateOk_subst : @SubstUpdateOk _ _ _ _ Expr_expr Subst_subst _ _}.

  Inductive Goal :=
  | GAll    : typ -> Goal -> Goal
  (** The first element in the list has the lowest index
   ** in the final goal.
   **)
  | GExs    : list (typ * option expr) -> Goal -> Goal
  | GHyp    : expr -> Goal -> Goal
  | GConj_  : Goal -> Goal -> Goal
  | GGoal   : expr -> Goal
  | GSolved : Goal.

  Definition GAlls (ts : list typ) (g : Goal) : Goal :=
    fold_right (fun x y => GAll x y) g ts.

  Definition GEx (t : typ) (e : option expr) (g : Goal) : Goal :=
    match g with
      | GExs tes g' => GExs ((t,e) :: tes) g'
      | _ => GExs ((t, e) :: nil) g
    end.

  Definition GConj l r : Goal :=
    match l with
      | GSolved => r
      | _ => match r with
               | GSolved => l
               | _ => GConj_ l r
             end
    end.

  Fixpoint GConj_list (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | g :: nil => g
      | g :: gs => GConj_ g (GConj_list gs)
    end.

  Fixpoint GConj_list_filter (ls : list Goal) : Goal :=
    match ls with
      | nil => GSolved
      | GSolved :: gs => GConj_list gs
      | g :: gs => GConj g (GConj_list gs)
    end.

  Inductive Ctx :=
  | CTop
  | CAll : Ctx -> typ -> Ctx
  | CExs : Ctx -> list typ -> Ctx
  | CHyp : Ctx -> expr -> Ctx.

  Fixpoint CEx (c : Ctx) (t : typ) : Ctx :=
    CExs c (t :: nil).

  Fixpoint CAlls (c : Ctx) (ls : list typ) : Ctx :=
    match ls with
      | nil => c
      | l :: ls => CAlls (CAll c l) ls
    end.

  (** Auxiliary Functions **)
  Fixpoint countVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CAll ctx' t => S (countVars ctx')
      | CExs ctx' _
      | CHyp ctx' _ => countVars ctx'
    end.

  Fixpoint countUVars (ctx : Ctx) : nat :=
    match ctx with
      | CTop => 0
      | CExs ctx' ts => length ts + countUVars ctx'
      | CAll ctx' _
      | CHyp ctx' _ => countUVars ctx'
    end.

  Fixpoint getUVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' _ => getUVars ctx'
      | CExs ctx' ts => getUVars ctx' ++ ts
      | CHyp ctx' _ => getUVars ctx'
    end.

  Fixpoint getVars (ctx : Ctx) : tenv typ :=
    match ctx with
      | CTop => nil
      | CAll ctx' t => getVars ctx' ++ t :: nil
      | CExs ctx' _ => getVars ctx'
      | CHyp ctx' _ => getVars ctx'
    end.

  Lemma countVars_getVars : forall ctx, countVars ctx = length (getVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Lemma countUVars_getUVars : forall ctx, countUVars ctx = length (getUVars ctx).
    induction ctx; simpl; auto.
    rewrite app_length. simpl. omega.
  Qed.

  Fixpoint getEnvs' (ctx : Ctx) (tus tvs : tenv typ)
  : tenv typ * tenv typ :=
    match ctx with
      | CTop => (tus,tvs)
      | CAll ctx' t => getEnvs' ctx' tus (t :: tvs)
      | CExs ctx' ts => getEnvs' ctx' (ts ++ tus) tvs (** TODO: Check **)
      | CHyp ctx' _ => getEnvs' ctx' tus tvs
    end.

  Definition getEnvs (ctx : Ctx) : tenv typ * tenv typ :=
    let (x,y) := getEnvs' ctx nil nil in
    (x, y).

  Fixpoint Ctx_append (c1 c2 : Ctx) : Ctx :=
    match c2 with
      | CTop => c1
      | CAll ctx' t => CAll (Ctx_append c1 ctx') t
      | CExs ctx' ts => CExs (Ctx_append c1 ctx') ts
      | CHyp ctx' h => CHyp (Ctx_append c1 ctx') h
    end.

  Theorem getUVars_append
  : forall c1 c2,
      getUVars (Ctx_append c1 c2) = getUVars c1 ++ getUVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.

  Theorem getVars_append
  : forall c1 c2,
      getVars (Ctx_append c1 c2) = getVars c1 ++ getVars c2.
  Proof.
    clear. induction c2; simpl; eauto.
    symmetry; eapply app_nil_r_trans.
    rewrite IHc2. apply app_ass_trans.
  Defined.
  (** End: Auxiliary Functions **)


  Inductive ctx_subst : Ctx -> Type :=
  | TopSubst : subst -> ctx_subst CTop
  | AllSubst : forall {t c}, ctx_subst c -> ctx_subst (CAll c t)
  | HypSubst : forall {t c}, ctx_subst c -> ctx_subst (CHyp c t)
  | ExsSubst : forall {ts c}, ctx_subst c -> subst -> ctx_subst (CExs c ts).

  Inductive WellFormed_ctx_subst : forall c, ctx_subst c -> Prop :=
  | WF_TopSubst : forall s, WellFormed_subst s -> WellFormed_ctx_subst (TopSubst s)
  | WF_AllSubst : forall t c s, WellFormed_ctx_subst s -> WellFormed_ctx_subst (@AllSubst t c s)
  | WF_HypSubst : forall t c s, WellFormed_ctx_subst s -> WellFormed_ctx_subst (@HypSubst t c s)
  | WF_ExsSubst : forall t c s s', WellFormed_subst s' ->
                                   WellFormed_ctx_subst s -> WellFormed_ctx_subst (@ExsSubst t c s s').

  Fixpoint ctx_lookup {c} (u : nat) (cs : ctx_subst c) : option expr :=
    match cs with
      | TopSubst s => lookup u s
      | AllSubst _ _ c => ctx_lookup u c
      | HypSubst _ _ c => ctx_lookup u c
      | ExsSubst _ _ c s =>
        match lookup u s with
          | None => ctx_lookup u c
          | Some e => Some e
        end
    end.

  Fixpoint ctx_domain {c} (cs : ctx_subst c) : list nat :=
    match cs with
      | TopSubst s => domain s
      | AllSubst _ _ c => ctx_domain c
      | HypSubst _ _ c => ctx_domain c
      | ExsSubst _ _ c s =>
        ctx_domain c ++ domain s
    end.

  Fixpoint ctx_substD {c} tus tvs (cs : ctx_subst c) 
  : option (exprT tus tvs Prop).
  Admitted.

  Section ctx_set'.
    Variables (u : nat) (e : expr) (min : nat) (nus : nat).

    Fixpoint ctx_set' {c T} (cs : ctx_subst c) {struct cs}
    : (ctx_subst c -> option T) -> option T.
      refine
        match cs in ctx_subst c return (ctx_subst c -> option T) -> option T with
          | TopSubst s => fun k =>
            match set u e s with
              | None => None
              | Some s' => k (TopSubst s')
            end
          | AllSubst _ _ c => fun k =>
            ctx_set' _ _ c (fun c => k (AllSubst c))
          | HypSubst _ _ c => fun k =>
            ctx_set' _ _ c (fun c => k (HypSubst c))
          | ExsSubst _ ctx c s => fun k =>
            if u ?[ ge ] (countUVars ctx + nus) then
              match set u e s with
                | None => None
                | Some s' => k (ExsSubst c s')
              end
            else
              (** NOTE: This is incorrect! **)
              @ctx_set' _ _ c (fun c => k (@ExsSubst _ ctx c s))
        end.
    Defined.
  End ctx_set'.

  Definition ctx_set {c} (u : nat) (e : expr) (cs : ctx_subst c)
  : option (ctx_subst c) :=
    (** TODO: This is wrong! **)
    ctx_set' u e 0 cs (@Some _).

  Fixpoint ctx_empty {c} : ctx_subst c :=
    match c with
      | CTop => TopSubst (@empty _ _ _)
      | CHyp c h => HypSubst ctx_empty
      | CAll c h => AllSubst ctx_empty
      | CExs c h => ExsSubst ctx_empty (@empty _ _ _)
    end.

  Global Instance Subst_ctx_subst ctx : Subst (ctx_subst ctx) expr :=
  { lookup := ctx_lookup
  ; domain := ctx_domain
  }.

  Global Instance SubstOk_cxt_subst ctx
  : @SubstOk (ctx_subst ctx) typ expr _ _ _ :=
  { WellFormed_subst := @WellFormed_ctx_subst ctx
  ; substD := @ctx_substD _
  }.
  admit.
  admit.
  admit.
  admit.
  Defined.

  Global Instance SubstUpdate_ctx_subst ctx : SubstUpdate (ctx_subst ctx) expr :=
  { set := ctx_set
  ; empty := ctx_empty
  }.

  (** StateT subst Option Goal **)
  Inductive Result c :=
  | Fail
  | More_  : ctx_subst c -> Goal -> Result c
  | Solved : ctx_subst c -> Result c.

  Definition More {c} (s : ctx_subst c) (g : Goal) : Result c :=
    match g with
      | GSolved => Solved s
      | _ => More_ s g
    end.

  Definition fromResult {c} (r : Result c) : option (ctx_subst c * Goal) :=
    match r with
      | Fail => None
      | More_ s g => Some (s, g)
      | Solved s => Some (s, GSolved)
    end.

  Definition DEAD {c} : Result c.
    exact (Fail c).
  Qed.

  (** Treat this as opaque! **)
  Definition rtac : Type :=
    tenv typ -> tenv typ -> nat -> nat ->
    forall c : Ctx, ctx_subst c -> expr -> Result c.

  Definition propD := @exprD'_typ0 _ _ _ _ Prop _.

  Fixpoint hlist_mapT {T : Type} {F : T -> Type}
           {ls : list T} (h : HList.hlist (fun x => option (F x)) ls)
  : option (hlist F ls) :=
    match h in hlist _ ls return option (hlist F ls) with
      | Hnil => Some (Hnil)
      | Hcons _ _ x y =>
        match x , hlist_mapT y with
          | Some x , Some y => Some (Hcons x y)
          | _ , _ => None
        end
    end.

  Section with_T.
    Context {T : Type}.
    Variables (b : T) (c : list T).

    Fixpoint nth_after' a  : nth_error (a ++ b :: c) (length a) = Some b :=
      match a as a return nth_error (a ++ b :: c) (length a) = Some b with
        | nil => eq_refl
        | x :: xs => nth_after' xs
      end.
  End with_T.
  Definition nth_after T a b c := @nth_after' T b c a.

  Definition hlist_get_cons_after_app {T : Type} {F : T -> Type} {t} {a b : list T}
             (h : hlist F (a ++ t :: b)) : F t :=
    (match nth_after a t b in _ = T return match T with
                                             | None => unit
                                             | Some x => F x
                                           end
     with
       | eq_refl => hlist_nth h (length a)
     end).

  Fixpoint goal_substD (tus tvs : list typ)
           (ts : list typ) (es : list (option expr))
  : option (exprT (tus ++ ts) tvs Prop) :=
    match ts as ts , es return option (exprT (tus ++ ts) tvs Prop) with
      | nil , nil => Some (fun _ _ => True)
      | t :: ts , None :: es =>
        match app_ass_trans tus (t :: nil) ts in _ = t
              return option (exprT _ tvs Prop) ->
                     option (exprT t tvs Prop)
        with
          | eq_refl => fun x => x
        end (goal_substD (tus ++ t :: nil) tvs ts es)
      | t :: ts , (Some e) :: es =>
        match exprD' (tus ++ t :: ts) tvs e t
            , goal_substD (tus ++ t :: nil) tvs ts es
        with
          | Some eD , Some sD =>
            Some (match eq_sym (app_ass_trans tus (t :: nil) ts) in _ = t
                        return exprT t tvs Prop -> exprT _ tvs Prop
                  with
                    | eq_refl => fun sD =>
                      fun us vs => sD us vs /\
                                   hlist_get_cons_after_app us = eD us vs
                  end sD)
          | _ , _ => None
        end
      | nil , _ :: _ => None
      | _ :: _ , nil => None
    end.

  (** NOTE:
   ** Appending the newly introduced terms makes tactics non-local.
   ** Requiring globalness seems bad.
   ** - The alternative, however, is to expose a lot more operations
   **   on substitute
   **)
  Fixpoint goalD (tus tvs : list typ) (goal : Goal) {struct goal}
  : option (exprT tus tvs Prop) :=
    match goal with
      | GAll tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => _foralls typD (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tes goal' =>
        let tus_ext := map fst tes in
        match goalD (tus ++ tus_ext) tvs goal'
            , goal_substD tus tvs tus_ext (map snd tes) with
          | None , _ => None
          | Some _ , None => None
          | Some D , Some sD =>
            Some (fun us vs => _exists typD tus_ext
                                        (fun us' => sD (HList.hlist_app us us') vs
                                                    /\ D (HList.hlist_app us us') vs))
        end
      | GHyp hyp' goal' =>
        match mapT (T:=list) (F:=option) (propD tus tvs) (hyp' :: nil) with
          | None => None
          | Some hs =>
            match goalD tus tvs goal' with
              | None => None
              | Some D =>
                Some (fun us vs => _impls (map (fun x => x us vs) hs) (D us vs))
            end
        end
      | GConj_ l r =>
        match goalD tus tvs l
            , goalD tus tvs r
        with
          | Some lD , Some rD => Some (fun us vs => lD us vs /\ rD us vs)
          | _ , _ => None
        end
      | GSolved => Some (fun _ _ => True)
      | GGoal goal' => propD tus tvs goal'
    end.

  Lemma goalD_conv
  : forall tus tvs tus' tvs' (pfu : tus' = tus) (pfv : tvs' = tvs),
      goalD tus tvs =
      match pfu in _ = t
            return Goal -> option (HList.hlist _ t -> _) with
        | eq_refl =>
          match pfv in _ = t
                return Goal -> option (_ -> HList.hlist _ t -> _) with
            | eq_refl => goalD tus' tvs'
          end
      end.
  Proof.
    clear. destruct pfu; destruct pfv. reflexivity.
  Qed.

  Fixpoint pctxD (tus tvs : tenv typ) (ctx : Ctx) (s : ctx_subst ctx) {struct s}
  : option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
            -> exprT tus tvs Prop) :=
    match s in ctx_subst ctx
          return option (   exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop
                         -> exprT tus tvs Prop)
    with
      | TopSubst s =>
        match substD tus tvs s with
          | None => None
          | Some sD =>
            Some (fun (k : exprT _ _ Prop) us vs =>
                    sD us vs ->
                    k (hlist_app us Hnil) (hlist_app vs Hnil))
        end
      | AllSubst t ctx' s' =>
        match pctxD tus tvs s' with
          | Some cD =>
            Some (fun k : exprT _ _ Prop =>
                    cD (fun us vs =>
                          forall x : typD t,
                            k us
                              match
                                app_ass_trans tvs (getVars ctx') (t :: nil) in (_ = t0)
                                return (hlist typD t0)
                              with
                                | eq_refl => hlist_app vs (Hcons x Hnil)
                              end))
          | None => None
        end
      | ExsSubst ts ctx' s' sub =>
        match substD ((tus ++ getUVars ctx') ++ ts) (tvs ++ getVars ctx') sub
            , pctxD tus tvs s'
        with
          | Some sD , Some cD =>
            Some (fun k : exprT (tus ++ getUVars ctx' ++ ts) (tvs ++ getVars ctx') Prop =>
                    cD (fun us vs =>
                          _foralls typD ts (fun us' =>
                                             sD (hlist_app us us') vs ->
                                             k match
                                                 app_ass_trans tus _ ts in (_ = t0)
                                                 return (hlist typD t0)
                                               with
                                                 | eq_refl => hlist_app us us'
                                               end
                                               vs)))
          | _ , _ => None
        end
      | HypSubst h ctx' s' =>
        match propD (tus ++ getUVars ctx') (tvs ++ getVars ctx') h with
          | None => None
          | Some pD => match pctxD tus tvs s' with
                         | None => None
                         | Some cD =>
                           Some (fun k : exprT _ _ Prop =>
                                   cD (fun us vs => pD us vs -> k us vs))
                       end
        end
    end.

  Definition RCtx {tus tvs tus' tvs'} :=
    (RexprT tus tvs Basics.impl ==> RexprT tus' tvs' Basics.impl)%signature.

  Local Existing Instance Transitive_Roption.
  Local Existing Instance Symmetric_Roption.
  Local Existing Instance Reflexive_Roption.
  Local Existing Instance Transitive_RexprT.
  Local Existing Instance Symmetric_RexprT.
  Local Existing Instance Reflexive_RexprT.

  Definition EqGoal tus tvs : relation Goal :=
    fun g1 g2 =>
        Roption (RexprT tus tvs iff)
                (goalD tus tvs g1)
                (goalD tus tvs g2).

  Global Instance Reflexive_EqGoal tus tvs : Reflexive (EqGoal tus tvs).
  Proof. red. red. reflexivity. Qed.
  Global Instance Transitive_EqGoal tus tvs : Transitive (EqGoal tus tvs).
  Proof.
    red. unfold EqGoal. intros.
    etransitivity; eauto.
  Qed.
  Global Instance Symmetric_EqGoal tus tvs : Symmetric (EqGoal tus tvs).
  Proof.
    red; unfold EqGoal. intros.
    symmetry. eauto.
  Qed.

  Definition EqResult tus tvs c : relation (Result c) :=
    fun r1 r2 =>
      Roption (Eqpair (@eq _) (EqGoal tus tvs))
              (fromResult r1) (fromResult r2).

  Global Instance Reflexive_EqResult tus tvs c
  : Reflexive (@EqResult tus tvs c).
  Proof.
    red. red. intros. reflexivity.
  Qed.
  Global Instance Symmetric_EqResult tus tvs c
  : Symmetric (@EqResult tus tvs c).
  Proof.
    red. unfold EqResult; inversion 1; constructor.
    symmetry; eauto.
  Qed.
  Global Instance Transitive_EqResult tus tvs c
  : Transitive (@EqResult tus tvs c).
  Proof.
    red; unfold EqResult; inversion 1; inversion 1; constructor.
    subst.
    etransitivity; eauto.
  Qed.

  Theorem Proper_pctxD_iff
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) iff ==>
                              (RexprT tus tvs iff)))%signature
             (@pctxD tus tvs c1 s).
  Proof.
    induction s; simpl; intros.
    { destruct (substD tus tvs s); try constructor.
      do 6 red; intros.
      apply equiv_eq_eq in H0; subst.
      apply equiv_eq_eq in H1; subst.
      eapply impl_iff; try reflexivity.
      intro. eapply H; reflexivity. }
    { red; simpl.
      destruct (pctxD tus tvs s); try constructor.
      inv_all.
      do 6 red. intros.
      eapply IHs; eauto.
      do 5 red; intros.
      eapply forall_iff. intros.
      eapply H; eauto.
      equivs. reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try constructor
             end.
      red; intros.
      inv_all. eapply IHs.
      do 5 red; intros.
      apply equiv_eq_eq in H0.
      apply equiv_eq_eq in H1. subst.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try solve [ constructor ]
             end.
      constructor.
      inv_all; do 6 red; intros.
      equivs.
      eapply IHs; try reflexivity.
      do 5 red; intros; equivs.
      eapply _forall_iff. intros.
      eapply impl_iff. reflexivity.
      intro. eapply H; reflexivity. }
  Qed.

  Theorem Proper_pctxD_impl
  : forall tus tvs c1 s,
      Proper (Roption (RexprT (tus ++ getUVars c1) (tvs ++ getVars c1) Basics.impl ==>
                              (RexprT tus tvs Basics.impl)))%signature
             (@pctxD tus tvs c1 s).
  Proof.
    induction s; simpl; intros.
    { destruct (substD tus tvs s); try constructor.
      do 7 red; intros.
      equivs.
      eapply H; eauto; reflexivity. }
    { red; simpl.
      destruct (pctxD tus tvs s); try constructor.
      inv_all.
      do 7 red. intros.
      eapply IHs; eauto.
      do 6 red; intros.
      equivs.
      eapply H; eauto; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try constructor
             end.
      red; intros.
      inv_all. eapply IHs.
      do 6 red; intros.
      equivs.
      eapply H; eauto; reflexivity. }
    { repeat match goal with
               | |- context [ match ?X with _ => _ end ] => destruct X ; try solve [ constructor ]
             end.
      constructor.
      inv_all.
      do 7 red; intros.
      eapply IHs; eauto.
      do 6 red; intros.
      equivs.
      eapply _forall_sem; intro.
      eapply _forall_sem with (x := x0) in H5.
      intros. eapply H; eauto; reflexivity. }
  Qed.

  Lemma More_More_ tus tvs c s :
    (EqGoal tus tvs ==> @EqResult tus tvs c)%signature
                                            (@More c s) (@More_ c s).
  Proof.
    red. red.
    simpl. intros; subst.
    destruct x; simpl; repeat constructor; assumption.
  Qed.

  Inductive GConj_rel : Goal -> Goal -> Goal -> Prop :=
  | GConjL : forall x, GConj_rel GSolved x x
  | GConjR : forall x, GConj_rel x GSolved x
  | GConjLR : forall x y, GConj_rel x y (GConj_ x y).

  Lemma GConj_rel_sound
  : forall tus tvs g1 g2 g,
      GConj_rel g1 g2 g ->
      (EqGoal tus tvs)%signature (GConj_ g1 g2) g.
  Proof.
    clear. inversion 1; subst; red; simpl.
    - destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite and_comm. rewrite and_True_iff.
      apply equiv_eq_eq in H0; apply equiv_eq_eq in H1; subst; reflexivity.
    - destruct (goalD tus tvs g); constructor.
      do 5 red; intros.
      rewrite and_True_iff.
      apply equiv_eq_eq in H0; apply equiv_eq_eq in H1; subst; reflexivity.
    - reflexivity.
  Qed.

  Lemma GConj_GConj_rel : forall g1 g2, GConj_rel g1 g2 (GConj g1 g2).
  Proof.
    intros; destruct g1; destruct g2; simpl; try constructor.
  Qed.

  Lemma GConj_GConj_ tus tvs :
    (EqGoal tus tvs ==> EqGoal tus tvs ==> EqGoal tus tvs)%signature
                                                          GConj GConj_.
  Proof.
    unfold EqGoal, respectful; simpl.
    intros.
    etransitivity.
    - symmetry. eapply GConj_rel_sound. eapply (GConj_GConj_rel x x0).
    - simpl. inversion H; try reflexivity.
      inversion H0; try reflexivity.
      constructor.
      do 5 red.
      intros. eapply and_iff. eapply H3; eauto.
      intro; eapply H6; eauto.
  Qed.

  Theorem Applicative_pctxD
  : forall tus tvs ctx s C,
      @pctxD tus tvs ctx s = Some C ->
      (forall us vs (P Q : exprT _ _ Prop),
         C (fun a b => P a b -> Q a b) us vs ->
         C P us vs ->
         C Q us vs) /\
      (forall us vs (Q : exprT _ _ Prop), (forall a b, Q a b) -> C Q us vs).
  Proof.
    clear. induction s; simpl; intros.
    { forward; inv_all; subst.
      forward_reason; split; eauto. }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H0; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto. }
      { intros us vs Q v.
        eapply Hpure. intros; eauto. } }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal; intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H1; [ | reflexivity | reflexivity | eapply f ].
        clear.
        do 6 red; intros; equivs.
        tauto. }
      { intros. eapply Hpure.
        intros. eauto. } }
    { forward; inv_all; subst.
      destruct (IHs _ eq_refl) as [ Hap Hpure ]; clear IHs.
      generalize (Proper_pctxD_impl tus tvs s).
      Cases.rewrite_all_goal.
      intros; inv_all.
      split.
      { intros us vs P Q f.
        eapply Hap.
        eapply H1; [ | reflexivity | reflexivity | eapply f ].
        simpl. clear.
        do 6 red. intros; equivs; eauto.
        eapply _forall_sem. intros.
        rewrite _forall_sem in H2.
        rewrite _forall_sem in H1.
        eauto. }
      { intros us vs Q v.
        eapply Hpure. intros.
        eapply _forall_sem; intros.
        eauto. } }
  Qed.

  Lemma Ap_pctxD
  : forall tus tvs (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop ->
                exprT tus tvs Prop),
      pctxD tus tvs s = Some C ->
      forall (us : hlist typD tus) (vs : hlist typD tvs)
             (P Q : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop),
        C (fun us vs => P us vs -> Q us vs) us vs -> C P us vs -> C Q us vs.
  Proof.
    intros. revert H1. revert H0. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H.
  Qed.

  Lemma Pure_pctxD
  : forall tus tvs (ctx : Ctx) (s : ctx_subst ctx)
           (C : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop ->
                exprT tus tvs Prop),
      pctxD tus tvs s = Some C ->
      forall (P : exprT (tus ++ getUVars ctx) (tvs ++ getVars ctx) Prop),
        (forall us vs, P us vs) -> forall us vs, C P us vs.
  Proof.
    intros. eapply Applicative_pctxD in H; eauto.
    destruct H. eapply H1; eauto.
  Qed.

  Definition CtxMorphism {tus tvs tus' tvs'}
             (c1 c2 : exprT tus tvs Prop -> exprT tus' tvs' Prop) : Prop :=
    forall (P : exprT _ _ Prop) us vs, c1 P us vs -> c2 P us vs.

  Inductive SubstMorphism (tus tvs : tenv typ)
  : forall c : Ctx, ctx_subst c -> ctx_subst c -> Prop :=
  | SMall : forall c t s1 s2,
              @SubstMorphism tus tvs c s1 s2 ->
              @SubstMorphism tus tvs (CAll c t) (AllSubst s1) (AllSubst s2)
  | SMexs : forall c ts s1 s2 cs1 cs2,
              (match @pctxD tus tvs c cs1
                   , substD ((tus ++ getUVars c) ++ ts) (tvs ++ getVars c) s1
                   , @pctxD tus tvs c cs2
                   , substD ((tus ++ getUVars c) ++ ts) (tvs ++ getVars c) s2
               with
                 | None , _ , _ , _
                 | Some _ , None , _ , _ => True
                 | Some _ , Some _ , None , _
                 | Some _ , Some _ , Some _ , None => False
                 | Some c1D , Some s1D , Some c2D , Some s2D =>
                   forall us vs, c2D (fun us vs =>
                                       forall us',
                                         s2D (hlist_app us us') vs ->
                                         s1D (hlist_app us us') vs) us vs
               end) ->
              @SubstMorphism tus tvs c cs1 cs2 ->
              @SubstMorphism tus tvs (CExs c ts) (ExsSubst cs1 s1) (ExsSubst cs2 s2)
  | SMhyp : forall c h s1 s2,
              @SubstMorphism tus tvs c s1 s2 ->
              @SubstMorphism tus tvs (CHyp c h) (HypSubst s1) (HypSubst s2)
  | SMtop : forall s1 s2,
              match substD tus tvs s1
                  , substD tus tvs s2
              with
                | None , _ => True
                | Some _ , None => False
                | Some a , Some b => forall us vs, b us vs -> a us vs
              end ->
              @SubstMorphism tus tvs CTop (TopSubst s1) (TopSubst s2).

  Definition rtac_spec tus tvs ctx s g r : Prop :=
    match r with
      | Fail => True
      | Solved s' =>
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match @pctxD tus tvs ctx s
            , goalD _ _ g
            , @pctxD tus tvs ctx s'
        with
          | None , _ , _
          | Some _ , None , _ => True
          | Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' =>
            @SubstMorphism tus tvs ctx s s' /\
            forall us vs,
              cD' gD us vs
        end
      | More_ s' g' =>
        WellFormed_ctx_subst s ->
        WellFormed_ctx_subst s' /\
        match @pctxD tus tvs ctx s
            , goalD _ _ g
            , @pctxD tus tvs ctx s'
            , goalD _ _ g'
        with
          | None , _ , _ , _
          | Some _ , None , _ , _ => True
          | Some _ , Some _ , None , _
          | Some _ , Some _ , Some _ , None => False
          | Some cD , Some gD , Some cD' , Some gD' =>
            @SubstMorphism tus tvs ctx s s' /\
            forall us vs, cD' (fun us vs => gD' us vs -> gD us vs) us vs
        end
    end.

  Definition rtac_sound (tus tvs : tenv typ) (tac : rtac) : Prop :=
    forall ctx s g result,
      (let tus := tus ++ getUVars ctx in
       let tvs := tvs ++ getVars ctx in
       tac tus tvs (length tus) (length tvs) ctx s g = result) ->
      @rtac_spec tus tvs ctx s (GGoal g) result.

  Lemma Fmap_pctxD_impl
  : forall tus tvs c s C,
      @pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ Basics.impl ==> RexprT tus tvs Basics.impl)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_impl tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.

  Lemma Fmap_pctxD_iff
  : forall tus tvs c s C,
      @pctxD tus tvs c s = Some C ->
      Proper (RexprT _ _ iff ==> RexprT tus tvs iff)%signature C.
  Proof.
    clear. intros.
    generalize (@Proper_pctxD_iff tus tvs c s).
    rewrite H. intros; inv_all. auto.
  Qed.


  Theorem Proper_rtac_spec tus tvs ctx s
  : Proper (EqGoal (tus ++ getUVars ctx) (tvs ++ getVars ctx) ==>
            @EqResult (tus ++ getUVars ctx) (tvs ++ getVars ctx) ctx ==> iff)
           (@rtac_spec tus tvs ctx s).
  Proof.
    red. red. red. unfold rtac_spec.
    inversion 2.
    { destruct x0; destruct y0; simpl in *; try congruence.
      reflexivity. }
    { destruct x0; destruct y0; simpl in *;
      try solve [ reflexivity | congruence ]; inv_all; subst; inv_all;
      try (eapply impl_iff; try reflexivity; intros;
           eapply and_iff; try reflexivity; intros;
           try inversion H; try reflexivity;
           try inversion H5; try reflexivity;
           repeat match goal with
                    | |- context [ match ?X with _ => _ end ] =>
                      consider X; intros; try reflexivity; [ ]
                  end;
           eapply and_iff; try reflexivity; intros;
           do 2 (eapply forall_iff; intro);
           eapply Fmap_pctxD_iff; eauto; try reflexivity;
           do 5 red; intros).
      { apply impl_iff; [ eapply H10; eauto | intro ].
        apply H7; eauto. }
      { do 5 red in H10.
        rewrite H10; try reflexivity.
        rewrite impl_True_iff.
        eapply H7; eauto. }
      { do 5 red in H10.
        rewrite <- H10; try reflexivity.
        rewrite impl_True_iff.
        eapply H7; eauto. } }
  Qed.

  Lemma pctxD_SubstMorphism
  : forall tus tvs ctx s s',
      @SubstMorphism tus tvs ctx s s' ->
      forall C C',
      @pctxD tus tvs ctx s = Some C ->
      @pctxD tus tvs ctx s' = Some C' ->
      forall us vs (P : exprT _ _ Prop),
        C P us vs -> C' P us vs.
  Proof.
    induction 1; intros; simpl in *; forward; inv_all; subst; eauto.
    { eapply IHSubstMorphism; eauto. }
    { simpl in *.
      eapply (IHSubstMorphism _ _ eq_refl eq_refl) in H3.
      destruct (Applicative_pctxD _ H2) as [ Hap Hpure ].
      revert H3. eapply Hap.
      generalize (H7 us vs).
      eapply Hap.
      eapply Hpure.
      clear. intros.
      rewrite _forall_sem.
      rewrite _forall_sem in H0.
      intros; eauto. }
    { eapply IHSubstMorphism; eauto. }
  Qed.

  Definition fromTop (cs : ctx_subst CTop) : subst :=
    match cs in ctx_subst c
          return match c with
                   | CTop => subst
                   | _ => unit
                 end
    with
      | TopSubst c => c
      | _ => tt
    end.

  Definition fromAll {c t} (cs : ctx_subst (CAll c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CAll c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | AllSubst _ _ c => c
      | _ => tt
    end.

  Definition fromHyp {c t} (cs : ctx_subst (CHyp c t)) : ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CHyp c _ => ctx_subst c
                   | _ => unit
                 end
    with
      | HypSubst _ _ c => c
      | _ => tt
    end.

  Definition fromExs {c t} (cs : ctx_subst (CExs c t)) : subst * ctx_subst c :=
    match cs in ctx_subst c
          return match c with
                   | CExs c _ => subst * ctx_subst c
                   | _ => unit
                 end
    with
      | ExsSubst _ _ c s => (s,c)
      | _ => tt
    end.

  Global Instance Injective_SubstMorphism_AllSubst tus tvs t ctx s s'
  : Injective (@SubstMorphism tus tvs (CAll ctx t) (AllSubst s) s') :=
  { result := exists s'', s' = AllSubst s'' /\ @SubstMorphism tus tvs ctx s s'' }.
  intros.
  exists (fromAll s').
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | AllSubst t s c => fun s' =>
                                            s' = AllSubst (fromAll s') /\
                                            SubstMorphism tus tvs c (fromAll s')
                    | _ => fun _ => True
                  end Y
     with
       | SMall _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_HypSubst tus tvs t ctx s s'
  : Injective (@SubstMorphism tus tvs (CHyp ctx t) (HypSubst s) s') :=
  { result := exists s'', s' = HypSubst s'' /\ @SubstMorphism tus tvs ctx s s'' }.
  intros.
  exists (fromHyp s').
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | HypSubst t s c => fun s' =>
                                            s' = HypSubst (fromHyp s') /\
                                            SubstMorphism tus tvs c (fromHyp s')
                    | _ => fun _ => True
                  end Y
     with
       | SMhyp _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_TopSubst tus tvs s s'
  : Injective (@SubstMorphism tus tvs (CTop) (TopSubst s) s') :=
  { result := exists s'', s' = TopSubst s'' /\ match substD tus tvs s
                                                   , substD tus tvs s''
                                               with
                                                 | None , _ => True
                                                 | Some _ , None => False
                                                 | Some a , Some b => forall us vs, b us vs -> a us vs
                                               end }.
  Proof.
    intros.
    exists (fromTop s').
    refine
      (match H in @SubstMorphism _ _ C X Y
             return match X in ctx_subst C' return ctx_subst C' -> Prop with
                      | TopSubst s => fun s' =>
                                        s' = TopSubst (fromTop s') /\
                                        match substD tus tvs s
                                            , substD tus tvs (fromTop s')
                                        with
                                          | None , _ => True
                                          | Some _ , None => False
                                          | Some a , Some b => forall us vs, b us vs -> a us vs
                                        end
                      | _ => fun _ => True
                    end Y
       with
         | SMtop _ _ _ => _
         | _ => I
       end).
    simpl; eauto.
  Defined.

  Global Instance Injective_SubstMorphism_ExsSubst tus tvs ctx tes s s' sub
  : Injective (@SubstMorphism tus tvs (CExs ctx tes) (ExsSubst sub s) s') :=
  { result := exists s'' sub',
                s' = ExsSubst sub' s''
                /\ (match @pctxD tus tvs ctx sub
                        , substD ((tus ++ getUVars ctx) ++ tes) (tvs ++ getVars ctx) s
                        , @pctxD tus tvs ctx sub'
                        , substD ((tus ++ getUVars ctx) ++ tes) (tvs ++ getVars ctx) s''
                    with
                      | None , _ , _ , _
                      | Some _ , None , _ , _ => True
                      | Some _ , Some _ , None , _
                      | Some _ , Some _ , Some _ , None => False
                      | Some c1D , Some s1D , Some c2D , Some s2D =>
                        forall us vs, c2D (fun us vs =>
                                             forall us',
                                               s2D (hlist_app us us') vs ->
                                               s1D (hlist_app us us') vs) us vs
                    end)
                /\ SubstMorphism tus tvs sub sub'}.
  intros. exists (fst (fromExs s')). exists (snd (fromExs s')).
  refine
    (match H in @SubstMorphism _ _ C X Y
           return match X in ctx_subst C' return ctx_subst C' -> Prop with
                    | ExsSubst t s su c =>
                      fun s' =>
                        s' = ExsSubst (snd (fromExs s')) (fst (fromExs s')) /\
                        match pctxD tus tvs su with
                          | Some _ =>
                            match
                              substD ((tus ++ getUVars s) ++ t) (tvs ++ getVars s) c
                            with
                              | Some s1D =>
                                match pctxD tus tvs (snd (fromExs s')) with
                                  | Some c2D =>
                                    match
                                      substD ((tus ++ getUVars s) ++ t)
                                             (tvs ++ getVars s) (fst (fromExs s'))
                                    with
                                      | Some s2D =>
                                        forall us vs,
                                          c2D
                                            (fun us0 vs0 =>
                                               forall us' : hlist typD t,
                                                 s2D (hlist_app us0 us') vs0 ->
                                                 s1D (hlist_app us0 us') vs0) us vs
                                      | None => False
                                    end
                                  | None => False
                                end
                              | None => True
                            end
                          | None => True
                        end /\
                        SubstMorphism tus tvs su (snd (fromExs s'))
                    | _ => fun _ => True
                  end Y
     with
       | SMexs _ _ _ _ _ _ _ _ => _
       | _ => I
     end).
  simpl; eauto.
  Defined.

  Global Instance Reflexive_SubstMorphism tus tvs ctx
  : Reflexive (@SubstMorphism tus tvs ctx).
  Proof.
    red. induction x;
         simpl; intros; try constructor;
         forward; eauto.
    eapply Applicative_pctxD; eauto.
  Qed.

  Global Instance Transitive_SubstMorphism tus tvs ctx
  : Transitive (@SubstMorphism tus tvs ctx).
  Proof.
    clear. red. intros x y z H; revert z.
    induction H.
    { intros; inv_all; subst.
      constructor; eauto. }
    { intros; inv_all; subst.
      forward. simpl in *.
      constructor.
      { forward. inv_all; subst.
        Cases.rewrite_all_goal.
        repeat match goal with
                 | H : ?X = _ , H' : ?X = _ |- _ =>
                   rewrite H in H'
               end; inv_all; subst.
        specialize (H8 us vs).
        specialize (H6 us vs).
        revert H8.
        eapply (Applicative_pctxD _ H5).
        eapply (pctxD_SubstMorphism H4 H1 H5 us vs).
        revert H6.
        eapply (Fmap_pctxD_impl _ H1); try reflexivity.
        clear.
        do 6 red. intros. equivs. firstorder. }
      { eapply IHSubstMorphism. eassumption. } }
    { intros; inv_all; subst. constructor; eauto. }
    { intros; inv_all; subst.
      constructor.
      forward. eauto. }
  Qed.

  Theorem rtac_spec_More_
  : forall tus tvs ctx (s : ctx_subst ctx) g,
      rtac_spec tus tvs s (GGoal g) (More_ s (GGoal g)).
  Proof.
    unfold rtac_spec.
    intros; subst.
    split; auto.
    simpl. forward.
    split; try reflexivity.
    intros. eapply Applicative_pctxD; eauto.
  Qed.

  Theorem rtac_spec_Fail
  : forall tus tvs ctx (s : ctx_subst ctx) g,
      rtac_spec tus tvs s g (Fail _).
  Proof.
    intros. exact I.
  Qed.

  Lemma rtac_spec_trans
  : forall tus tvs ctx (c c' : ctx_subst ctx) g g' r,
      rtac_spec tus tvs c g (More_ c' g') ->
      rtac_spec tus tvs c' g' r ->
      rtac_spec tus tvs c g r.
  Proof.
    destruct r; simpl; intros; auto; forward; forward_reason;
    split; eauto.
    - split; [ etransitivity; eauto | ].
      intros us vs. generalize (H11 us vs); clear H11.
      destruct (Applicative_pctxD _ H4) as [ Hap Hpure ].
      eapply Hap.
      eapply (pctxD_SubstMorphism H10 H0 H4).
      generalize (H9 us vs); clear H9.
      clear Hap Hpure.
      eapply Fmap_pctxD_impl;
        [ eassumption | | reflexivity | reflexivity ].
      clear. do 6 red.
      intros; equivs. tauto.
    - split; [ etransitivity; eauto | ].
      intros us vs. generalize (H10 us vs); clear H10.
      destruct (Applicative_pctxD _ H4) as [ Hap Hpure ].
      eapply Hap.
      eapply (pctxD_SubstMorphism H9 H0 H4).
      generalize (H8 us vs); clear H8.
      clear Hap Hpure.
      eapply Fmap_pctxD_impl;
        [ eassumption | | reflexivity | reflexivity ].
      clear. do 6 red.
      intros; equivs. tauto.
  Qed.

End parameterized.

Arguments rtac_sound {typ expr subst _ _ _ _ _} tus tvs tac : rename.

Arguments GEx {typ expr} _ _ _ : rename.
Arguments GAll {typ expr} _ _ : rename.
Arguments GHyp {typ expr} _ _ : rename.
Arguments GConj {typ expr} _ _ : rename.
Arguments GConj_ {typ expr} _ _ : rename.
Arguments GConj_list {typ expr} _ : rename.
Arguments GGoal {typ expr} _ : rename.
Arguments GSolved {typ expr} : rename.
Arguments CTop {typ expr} : rename.
Arguments CEx {typ expr} _ _ : rename.
Arguments CAll {typ expr} _ _ : rename.
Arguments CHyp {typ expr} _ _ : rename.

Arguments Fail {typ expr subst _} : rename.
Arguments More {typ expr subst _} _ _ : rename.
Arguments More_ {typ expr subst _} _ _ : rename.
Arguments Solved {typ expr subst _} _ : rename.

Export MirrorCore.ExprI.
Export MirrorCore.SubstI.
Export MirrorCore.ExprDAs.
