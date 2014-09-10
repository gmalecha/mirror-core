Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: Can I do alternation if I can do strengthening of both
 ** unification variables and regular variables?
 ** 1) This means that substD needs strengthening
 ** 2) It also means that hypotheses need to be eliminatable
 **
 **    goal :=
 **      Alls : list typ -> goal -> goal
 **    | Exs : list typ -> goal -> goal
 **    | Hyps : list expr -> goal -> goal
 **    | Goal : expr -> goal.
 **
 **)
Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.

  (** This is a way to put everything inside there,
   ** an alternative representation is to use a simpler type, i.e.
   **     [list (All | Ex | Hyp)]
   ** to interpret the flattened environments
   **)
  (** NOTE: It seems for performance this should be inverted, otherwise
   ** every operation is going to be very expensive.
   **)
  Inductive Goal :=
  | GAlls : typ -> Goal -> Goal
  | GExs  : typ -> Goal -> Goal
  | GHyps : expr -> Goal -> Goal
  | GGoal : subst -> option expr -> Goal.

  (** GoalD **)

  Definition Result := option Goal.

  Definition rtac : Type :=
    Goal -> Result.

  Variable RType_typ : RType typ.
  Variable Expr_expr : Expr RType_typ expr.
  Variable Typ0_Prop : Typ0 _ Prop.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.

  Definition propD (tus tvs : list typ) (goal : expr) : ResType tus tvs Prop :=
    match exprD' tus tvs goal (@typ0 _ _ _ _) return ResType tus tvs Prop with
      | None => None
      | Some val =>
        Some match typ0_cast nil in _ = T return HList.hlist _ tus -> HList.hlist _ tvs -> T with
               | eq_refl => val
             end
    end.

  Fixpoint _foralls (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => forall x : typD nil l,
                              _foralls (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _exists (ls : list typ)
  : (HList.hlist (typD nil) ls -> Prop) -> Prop :=
    match ls as ls return (HList.hlist (typD nil) ls -> Prop) -> Prop with
      | nil => fun P => P HList.Hnil
      | l :: ls => fun P => exists x : typD nil l,
                              _exists (fun z => P (HList.Hcons x z))
    end.

  Fixpoint _impls (ls : list Prop) (P : Prop) :=
    match ls with
      | nil => P
      | l :: ls => l -> _impls ls P
    end.

  (** NOTE:
   ** Appending the newly introduced terms makes tactics non-local.
   ** Requiring globalness seems really bad.
   **)
  Fixpoint goalD (tus tvs : list typ) (goal : Goal)
  : ResType tus tvs Prop :=
    match goal with
      | GAlls tv goal' =>
        match goalD tus (tvs ++ tv :: nil) goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_foralls (tv :: nil) (fun vs' => D us (HList.hlist_app vs vs')))
        end
      | GExs tu goal' =>
        match goalD (tus ++ tu :: nil) tvs goal' with
          | None => None
          | Some D =>
            Some (fun us vs => @_exists (tu :: nil)
                      (fun us' => D (HList.hlist_app us us') vs))
        end
      | GHyps hyp' goal' =>
        match mapT (T:=list) (F:=option) (propD tus tvs) (hyp' :: nil) with
          | None => None
          | Some hs =>
            match goalD tus tvs goal' with
              | None => None
              | Some D =>
                Some (fun us vs => _impls (map (fun x => x us vs) hs) (D us vs))
            end
        end
      | GGoal sub' None =>
        match substD tus tvs sub' with
          | Some sD => Some (fun us vs => sD us vs)
          | _ => None
        end
      | GGoal sub' (Some goal') =>
        match substD tus tvs sub'
            , propD tus tvs goal'
        with
          | Some sD , Some gD =>
            Some (fun (us : HList.hlist (typD nil) tus)
                      (vs : HList.hlist (typD nil) tvs)  => sD us vs /\ gD us vs)
          | _ , _ => None
        end
    end.

  Definition rtac_sound tus tvs (tac : rtac) : Prop :=
    forall g g',
      tac g = Some g' ->
      match goalD tus tvs g
          , goalD tus tvs g'
      with
        | None , _ => True
        | Some _ , None => False
        | Some g , Some g' =>
          forall us vs,
            g' us vs ->
            g us vs
      end.

  Section at_bottom.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    Variable gt : list typ -> list typ -> subst -> option expr -> m Goal.

    Let under (gt : Goal -> Goal) (x : m Goal) : m Goal :=
      bind x (fun x => ret (gt x)).

    Fixpoint at_bottom tus tvs (g : Goal) : m Goal :=
      match g with
        | GAlls x g' => under (GAlls x) (at_bottom tus (tvs ++ x :: nil) g')
        | GExs  x g' => under (GExs  x) (at_bottom (tus ++ x :: nil) tvs g')
        | GHyps x g' => under (GHyps x) (at_bottom tus tvs g')
        | GGoal s e => gt tus tvs s e
      end.
  End at_bottom.

  Definition THEN (c1 c2 : rtac) : rtac :=
    fun gl =>
      match c1 gl with
        | Some gl' => c2 gl'
        | None => None
      end.

  Theorem THEN_sound
  : forall tus tvs tac1 tac2,
      rtac_sound tus tvs tac1 ->
      rtac_sound tus tvs tac2 ->
      rtac_sound tus tvs (THEN tac1 tac2).
  Proof.
    unfold THEN.
    intros.
    red. intros.
    Require Import MirrorCore.Util.Forwardy.
    forwardy.
    eapply H in H1.
    eapply H0 in H2.
    forward. intuition.
  Qed.

  Definition TRY (tac : rtac) : rtac :=
    fun gl => match tac gl with
                | None => Some gl
                | Some gl' => Some gl'
              end.

  Theorem TRY_sound
  : forall tus tvs tac, rtac_sound tus tvs tac -> rtac_sound tus tvs (TRY tac).
  Proof.
    unfold TRY, rtac_sound.
    intros.
    specialize (H g g').
    destruct (tac g); inv_all; subst.
    { eapply H. reflexivity. }
    { forward. }
  Qed.

  Definition INTRO (open : expr -> option ((typ + expr) * expr)) : rtac :=
    fun g => at_bottom (m := option)
                       (fun tus tvs s g =>
                          match g with
                            | None => None
                            | Some g =>
                              match open g with
                                | None => None
                                | Some (inl t, g') =>
                                  Some (GAlls t (GGoal s (Some g')))
                                | Some (inr t, g') =>
                                  Some (GHyps t (GGoal s (Some g')))
                              end
                          end)
               nil nil g.

  Definition open_sound (open : expr -> option ((typ + expr) * expr)) : Prop :=
    forall tus tvs e eD h e',
      open e = Some (h,e') ->
      propD tus tvs e = Some eD ->
      match h with
        | inl t =>
          exists eD',
          propD tus (t :: tvs) e' = Some eD' /\
          forall us vs,
            (eD us vs) -> (forall x : typD nil t, eD' us (HList.Hcons x vs))
        | inr h =>
          False
      end.

  Lemma at_bottom_sound_option
  : forall goal tus tvs f goal',
      (** I need a characterization of [f] **)
      (forall tus' tvs' s e e',
         f (tus ++ tus') (tvs ++ tvs') s e = Some e' ->
         match goalD (tus ++ tus') (tvs ++ tvs') (GGoal s e)
               , goalD (tus ++ tus') (tvs ++ tvs') e'
         with
           | None , _ => True
           | Some _ , None => False
           | Some g , Some g' =>
             forall us vs,
               g' us vs -> g us vs
         end) ->
      at_bottom f tus tvs goal = Some goal' ->
      match goalD tus tvs goal
            , goalD tus tvs goal'
      with
        | None , _ => True
        | Some _ , None => False
        | Some g , Some g' =>
          forall us vs,
            g' us vs -> g us vs
      end.
  Proof.
    induction goal; simpl; intros.
    { forwardy. inv_all; subst.
      eapply IHgoal in H0.
      simpl. forward. auto.
      intros.
      specialize (H tus' (t :: tvs') s e).
      rewrite app_ass in H1. simpl in *.
      eapply H in H1; clear H IHgoal.
      forward.
      destruct e.
      admit. admit. }
    { admit.
    (* forwardy; inv_all; subst.
        eapply IHgoal in H.
        simpl; forward; eauto.
        destruct H2. exists x.
        eapply H1. eassumption. *) }
    { admit.
    (* forwardy; inv_all; subst.
        eapply IHgoal in H.
        simpl. forward; eauto.
        inv_all; subst. simpl in *.
        eauto. *) }
    { specialize (H nil nil s o goal').
      simpl in H.
      repeat rewrite HList.app_nil_r_trans in H.
      eapply H in H0; clear H.
      auto. }
  Qed.

  Theorem INTRO_sound
  : forall open, open_sound open ->
                 rtac_sound nil nil (INTRO open).
  Proof.
    unfold rtac_sound, INTRO.
    intros.
    eapply at_bottom_sound_option in H0; eauto.
    + clear - H.
      simpl. intros.
      forward. inv_all; subst.
      eapply H in H2.
      eapply H2 in H5; clear H2.
      destruct s0.
      - inv_all; subst.
        simpl.
        (** TODO : This doesn't quite work!
         ** The order of quantifiers is backwards
         **)
  Abort.
    


  Eval compute in fun open t1 t2 e3 s goal =>
    INTRO open (GAlls t1 (GExs t2 (GHyps e3 (GGoal s (Some goal))))).

  Instance Monad_id : Monad (fun T : Type => T) :=
  { ret := fun T x => x
  ; bind := fun T U c c1 => c1 c
  }.

  Definition GOAL_map (f : list typ -> list typ -> subst -> expr -> expr)
  : rtac :=
    fun g =>
      Some (at_bottom (m := fun T => T)
                      (fun tus tvs s e =>
                         match e with
                           | None => GGoal s None
                           | Some e => GGoal s (Some (f tus tvs s e))
                         end)
                      nil nil g).

  Instance Monad_writer_nat : Monad (fun T : Type => (T * nat)%type) :=
  { ret := fun T x => (x,0)
  ; bind := fun T U c c1 =>
              let (x,n) := c in
              let (y,n') := c1 x in
              (y,n+n')
  }.

  (** On [Proved], I need to check, that means that I probably need to do
   ** deltas so that I know where I need to pull to...
   **)
  Definition with_new_uvar (t : typ) (k : nat -> rtac)
  : rtac :=
    fun g =>
      let (g',n) :=
          at_bottom (m := fun T => (T * nat))%type
                    (fun tus _ s g => (GExs t (GGoal s g), length tus)) nil nil g
      in
      k n g'.
(*
  Axiom ty : typ.
  Axiom s : subst.

  Eval compute in fun (f : nat -> rtac) => with_new_uvar ty f (GGoal s None).

  Definition with_new_var (t : typ) (k : nat -> rtac)
  : rtac :=
    fun g =>
      let (g',uv) :=
          at_bottom (fun _ tvs g => (GAlls t g, length tvs)) nil nil g
      in
      k uv g'.
*)
End parameterized.