(** The implementation of rewriting hint databases
 **)
Require Import ExtLib.Structures.Functor.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.CoreK.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.RewriteRelations.
Require Import MirrorCore.Types.ModularTypesT.
Require Import MirrorCore.Types.MTypeUnifyT.
Require Import MirrorCore.PolymorphicF.
Require Import MirrorCore.Lambda.PolyInstT.

Require Import MirrorCore.Util.Forwardy.

Set Implicit Arguments.
Set Strict Implicit.

Set Suggest Proof Using.

Module HintDbs (Import RT : TypeLang) (RTU : TypeLangUnify with Module RT := RT).
  Module PI := PolyInst RT RTU.

  Section with_symbols.
    Variable tsym : kind -> Set.
    Variable TSym_tsym : TSym kindD tsym.
    Let typ := type tsym Kstar.
    Context {func : Set}.
    Let RType_typD : RType typ := RT.RType_type _ _.
    Context {Typ2_Fun : Typ2 RType_typD RFun}.
    Context {RSym_func : RSym func}.

    (** Reasoning principles **)
    Context {RTypeOk_typD : RTypeOk}.
    Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
    Context {RSymOk_func : RSymOk RSym_func}.
    Context {Typ0_Prop : Typ0 _ Prop}.

    Local Existing Instance Expr_expr.
    Local Existing Instance ExprOk_expr.

    (* TODO(gmalecha): Wrap all of this up in a type class?
     * Why should it be different than Expr?
     *)
    Variable Rbase : Set.
    Variable Rbase_eq : Rbase -> Rbase -> bool.
    Hypothesis Rbase_eq_ok : forall a b, Rbase_eq a b = true -> a = b.

    Local Notation "'R'" := (R typ Rbase).

    Variable RbaseD : Rbase -> forall t : typ, option (typD t -> typD t -> Prop).

    Hypothesis RbaseD_single_type
    : forall r t1 t2 rD1 rD2,
        RbaseD r t1 = Some rD1 ->
        RbaseD r t2 = Some rD2 ->
        t1 = t2.

    Inductive HintRewrite : Type :=
    | PRw_tc : forall {n : list kind},
        polymorphic (type tsym) n (rw_lemma typ func Rbase) ->
        polymorphic (type tsym) n bool ->
        CoreK.rtacK typ (expr typ func) ->
        HintRewrite.

    (* TODO - change to RewriteDb for consistency? *)
    Definition RewriteHintDb : Type := list HintRewrite.

    (* TODO(mario): this is duplicated in Respectful.v. We should find a long-term home for it *)
    (* TODO(mario): convert this so it uses rw_concl instead of rw_lemma? *)
    (* no-op typeclass, used to construct polymorphic types without constraints *)
    Definition tc_any (n : list kind) : polymorphic (type tsym) n bool :=
      make_polymorphic (fun _ => true).

    Definition with_typeclasses {T : Type} (TD : T -> Prop) {n}
               (tc : polymorphic (type tsym) n bool)
               (pc : polymorphic (type tsym) n T)
      : polymorphic (type tsym) n Prop :=
      make_polymorphic (fun args =>
                          if inst tc args
                          then TD (inst pc args)
                          else True).

    (* TODO(mario): end duplicated code *)

    Definition rw_lemmaP (rw : rw_lemma typ func Rbase) : Prop :=
      lemmaD (rw_conclD RbaseD) nil nil rw.

    Definition RewriteHintOk (hr : HintRewrite) : Prop :=
      match hr with
      | PRw_tc plem tc tac =>
        polymorphicD (fun x => x) (with_typeclasses rw_lemmaP tc plem) /\
        rtacK_sound tac
      end.

    Theorem PRw_tc_sound
            {n : list kind}
            (plem : polymorphic (type tsym) n (rw_lemma typ func Rbase)) tc tac
      : polymorphicD (fun x => x) (with_typeclasses rw_lemmaP tc plem) ->
        rtacK_sound tac ->
        RewriteHintOk (PRw_tc plem tc tac).
    Proof using.
      clear. simpl. tauto.
    Qed.

    (** Convenience constructors for building lemmas that do not use
     ** polymorphism.
     **)
    Definition Rw (rw : rw_lemma typ func Rbase) :=
      @PRw_tc nil rw true.

    Theorem Rw_sound
            (rw : rw_lemma typ func Rbase)
            (tac : CoreK.rtacK typ (expr typ func))
    : rw_lemmaP rw ->
      CoreK.rtacK_sound tac ->
      RewriteHintOk (Rw rw tac).
    Proof using.
      clear.
      intros.
      eapply PRw_tc_sound; eauto.
    Qed.

    (** polymorphic proper hint without typeclass constraints *)
    Definition PRw {n : list kind}
               (pc : polymorphic (type tsym) n (rw_lemma typ func Rbase)) :=
      PRw_tc (n:=n) pc (tc_any n).

    Theorem PRw_sound
            {n : list kind}
            (plem : polymorphic (type tsym) n (rw_lemma typ func Rbase))
            (tac : CoreK.rtacK typ (expr typ func))
    : polymorphicD rw_lemmaP plem ->
        CoreK.rtacK_sound tac ->
        RewriteHintOk (PRw plem tac).
    Proof using.
      intros.
      eapply PRw_tc_sound; eauto.
      eapply polymorphicD_make_polymorphic. intros.
      unfold tc_any.
      rewrite inst_make_polymorphic.
      unfold rw_lemmaP, lemmaD.
      apply inst_sound.
      simpl. assumption.
    Qed.

    Require Import Coq.NArith.BinNat.

    Local Definition get_lemma (su : PI.sym_unifier) {n : list kind}
          (plem : polymorphic (type tsym) n (rw_lemma typ func Rbase))
          (tc : polymorphic (type tsym) n bool)
          (e : expr typ func)
    : option (rw_lemma typ func Rbase) :=
      match
        PI.get_inst su (fun x => x.(concl).(lhs)) plem e
      with
      | None => None
      | Some args =>
        if inst tc args
        then Some (inst plem args)
        else None
      end.

    Fixpoint CompileHints (su : PI.sym_unifier) (hints : RewriteHintDb)
             (e : expr typ func)
             (r : R)
    : list (rw_lemma typ func Rbase * rtacK typ (expr typ func)) :=
      match hints with
      | nil => nil
      | PRw_tc plem tc tac :: hints =>
        match get_lemma su plem tc e with
        | None => CompileHints su hints e r
        | Some lem => (lem, tac) :: CompileHints su hints e r
        end
      end.

    Definition hints_sound
               (hints : expr typ func -> R ->
                        list (rw_lemma typ func Rbase * CoreK.rtacK typ (expr typ func)))
    : Prop :=
      (forall r e,
          Forall (fun lt =>
                    (forall tus tvs t eD,
                        lambda_exprD tus tvs t e = Some eD ->
                        Lemma.lemmaD (rw_conclD RbaseD) nil nil (fst lt)) /\
                    CoreK.rtacK_sound (snd lt)) (hints e r)).


    Definition RewriteHintDbOk (db : RewriteHintDb) : Prop :=
      Forall RewriteHintOk db.

    Theorem CompileHints_sound
    : forall su db, RewriteHintDbOk db ->
            hints_sound (CompileHints su db).
    Proof using.
      induction db; intros; simpl.
      { unfold hints_sound. intros. constructor. }
      { inversion H; subst; clear H.
        specialize (IHdb H3). clear H3.
        unfold hints_sound. intros.
        destruct a.
        destruct (get_lemma su p p0) eqn:Hgl; [|eapply IHdb].
        constructor; [|eauto].
        unfold RewriteHintOk in *. destruct H2.
        split; [|eauto].
        intros.
        unfold get_lemma in *.
        Import MirrorCore.Util.Forwardy.
        forwardy.
        eapply inst_sound with (v:=y) in H.
        unfold with_typeclasses in H.
        rewrite inst_make_polymorphic in H.
        destruct (inst p0 y); [|congruence].
        inversion H3; clear H3; subst.
        simpl in *. clear H2.
        red in H. tauto. }
    Qed.
  End with_symbols.
End HintDbs.
