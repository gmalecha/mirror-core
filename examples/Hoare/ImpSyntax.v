Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.MTypes.ModularTypes.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
Require Import MirrorCore.Views.ViewSum.
Require Import McExamples.Hoare.Imp.
Require Import McExamples.Hoare.ILogicFunc.

Module ImpSyntax (I : ImpLang).
  (* Types *)
  Inductive tsym : nat -> Type :=
  | tyLocals   : tsym 0
  | tyCmd      : tsym 0
  | tySProp    : tsym 0
  | tyHProp    : tsym 0
  | tyProp     : tsym 0
  | tyVariable : tsym 0
  | tyExpr     : tsym 0
  | tyValue    : tsym 0.

  Definition tsymD (n : nat) (t : tsym n) : type_for_arity n :=
    match t with
    | tyLocals => I.locals
    | tyCmd => I.icmd
    | tySProp => I.SProp
    | tyHProp => I.HProp
    | tyProp => Prop
    | tyVariable => I.var
    | tyExpr => I.iexpr
    | tyValue => I.value
    end.

  Definition tsym_tag {n} (t : tsym n) : nat :=
    match t with
    | tyLocals => 0
    | tyCmd => 1
    | tySProp => 2
    | tyHProp => 3
    | tyVariable => 4
    | tyExpr => 5
    | tyValue => 6
    | tyProp => 7
    end.

  Definition tsym_neq : forall n (a b : tsym n),
      tsym_tag a <> tsym_tag b ->
      a <> b.
  Proof.
    intros. intro.
    apply H. destruct H0.
    reflexivity.
  Defined.

  Definition tsym_dec {n} (a : tsym n) : forall b, {a = b} + {a <> b}.
  refine
    match a as a in tsym n return forall b : tsym n, {a = b} + {a <> b} with
    | tyLocals => fun b =>
                    match b with
                    | tyLocals => left eq_refl
                    | _ => right _
                    end
    | tyCmd => fun b =>
                    match b with
                    | tyCmd => left eq_refl
                    | _ => right _
                    end
    | tySProp => fun b =>
                    match b with
                    | tySProp => left eq_refl
                    | _ => right _
                    end
    | tyHProp => fun b =>
                    match b with
                    | tyHProp => left eq_refl
                    | _ => right _
                    end
    | tyProp => fun b =>
                    match b with
                    | tyProp => left eq_refl
                    | _ => right _
                    end
    | tyVariable => fun b =>
                    match b with
                    | tyVariable => left eq_refl
                    | _ => right _
                    end
    | tyExpr => fun b =>
                    match b with
                    | tyExpr => left eq_refl
                    | _ => right _
                    end
    | tyValue => fun b =>
                    match b with
                    | tyValue => left eq_refl
                    | _ => right _
                    end
    end; try solve [ intro x ; revert x ; apply tsym_neq ;
                     clear; compute; congruence ].
  Defined.

  Instance TSym_tsym : TSym tsym :=
  { symbolD := @tsymD
  ; symbol_dec := @tsym_dec }.

  Definition typ := mtyp tsym.

  Global Instance RType_typ : RType typ := RType_mtyp tsym _.
  Global Instance RTypeOk_typ : RTypeOk := RTypeOk_mtyp _ _.

  Global Instance Typ2_Fun : @Typ2 typ _ Fun := Typ2_Fun.
  Global Instance Typ2Ok_Fun : Typ2Ok Typ2_Fun := Typ2Ok_Fun.
  Global Instance Typ0_Prop : @Typ0 typ _ Prop := Typ0_sym tyProp.
  Global Instance Typ0Ok_Prop : Typ0Ok Typ0_Prop := Typ0Ok_sym tyProp.

  Global Instance RelDec_eq_typ : RelDec (@eq typ) := RelDec_Rty _.
  Global Instance RelDec_Correct_eq_typ : RelDec_Correct RelDec_eq_typ :=
    @RelDec_Correct_Rty _ _ _.

  (* Symbols *)
  Inductive imp_func :=
  | pVar (_ : I.var)
  | pNat (_ : nat)
  | pLocals_get | pLocals_upd
  | pEq (_ : typ)
  | pEval_expri
  | eVar | eConst | ePlus
  | natPlus
  (** Below here isn't really imp functions **)
  | pAp (_ _ : typ)
  | pPure (_ : typ)
  | pUpdate (_ : typ).

  Definition func := (SymEnv.func + imp_func + ilfunc typ)%type.

  Local Notation "! x" := (@tyBase0 tsym x) (at level 0).

  Arguments tyArr {_} _ _.

  Definition typeof_sym_imp (f : imp_func) : option typ :=
    match f with
    | pVar _ => Some !tyVariable
    | pNat _ => Some !tyValue
    | pLocals_get => Some (tyArr !tyVariable (tyArr !tyLocals !tyValue))
    | pLocals_upd => Some (tyArr !tyVariable (tyArr !tyValue (tyArr !tyLocals !tyLocals)))
    | pEq t => Some (tyArr t (tyArr t !tyProp))
    | pEval_expri => Some (tyArr !tyExpr (tyArr !tyLocals !tyValue))
    | eVar => Some (tyArr !tyVariable !tyExpr)
    | eConst => Some (tyArr !tyValue !tyExpr)
    | ePlus => Some (tyArr !tyExpr (tyArr !tyExpr !tyExpr))
    | natPlus => Some (tyArr !tyValue (tyArr !tyValue !tyValue))
    | pAp t u => Some (tyArr (tyArr !tyLocals (tyArr t u)) (tyArr (tyArr !tyLocals t) (tyArr !tyLocals u)))
    | pPure t => Some (tyArr t (tyArr !tyLocals t))
    | pUpdate t => Some (tyArr (tyArr !tyLocals !tyLocals)
                               (tyArr (tyArr !tyLocals t)
                                      (tyArr !tyLocals t)))
    end.

  Definition imp_func_eq (a b : imp_func) : option bool :=
    match a , b with
    | pVar a , pVar b => Some (a ?[ eq ] b)
    | pNat a , pNat b => Some (a ?[ eq ] b)
    | pLocals_get , pLocals_get => Some true
    | pLocals_upd , pLocals_upd => Some true
    | pEq a , pEq b => Some (a ?[ Rty ] b)
    | pEval_expri , pEval_expri => Some true
    | eVar , eVar => Some true
    | eConst , eConst => Some true
    | ePlus , ePlus => Some true
    | natPlus , natPlus => Some true
    | pAp t u , pAp t' u' => Some (t ?[ Rty ] t' && u ?[ Rty ] u')%bool
    | pPure t , pPure t' => Some (t ?[ Rty ] t')
    | pUpdate t , pUpdate t' => Some (t ?[ Rty ] t')
    | _ , _ => Some false
    end.

  Instance RSym_imp_func : SymI.RSym imp_func :=
  { typeof_sym := typeof_sym_imp
  ; symD := fun f =>
    match f as f return match typeof_sym_imp f with
                        | None => unit
                        | Some t => typD t
                        end
    with
    | pVar v => v
    | pNat n => n
    | pLocals_get => I.locals_get
    | pLocals_upd => I.locals_upd
    | pEq t => @eq _
    | pEval_expri => I.eval_iexpr
    | eVar => I.iVar
    | eConst => I.iConst
    | ePlus => I.iPlus
    | natPlus => plus
    | pPure t =>
      @Applicative.pure (RFun I.locals) (Applicative_Fun _) (typD t)
    | pAp t u =>
      @Applicative.ap (RFun I.locals) (Applicative_Fun _) (typD t) (typD u)
    | pUpdate t => I.update
    end
  ; sym_eqb := imp_func_eq
  }.

  Instance RSymOk_imp_func : SymI.RSymOk RSym_imp_func.
  constructor.
  - destruct a; destruct b; simpl; try congruence.
    all: match goal with
         | |- context [ if ?X then _ else _ ] =>
           consider X; intros; unfold Rty in *; try congruence
         end.
    f_equal; tauto.
    destruct H; congruence.
  Qed.

  Definition tyLProp := tyArr !tyLocals !tyHProp.

  Local Notation "a >> b" := (tyArr a b) (at level 31,right associativity).

  Require Import Coq.Lists.List.
  (** TODO: Note that this needs to be extensible! **)
  Definition fs : @SymEnv.functions typ _ :=
    SymEnv.from_list
      (@SymEnv.F typ _ (tyArr tyLProp (tyArr !tyCmd (tyArr tyLProp !tySProp)))
                 I.triple ::
       @SymEnv.F typ _ (tyArr !tyCmd (tyArr !tyCmd !tyCmd)) I.Seq ::
       @SymEnv.F typ _ (tyArr !tyVariable (tyArr !tyExpr !tyCmd)) I.Assign ::
       @SymEnv.F typ _ !tyCmd I.Skip ::
       @SymEnv.F typ _ (tyArr tyLProp !tyCmd) I.Assert ::
       @SymEnv.F typ _ (tyArr !tyExpr (tyArr !tyCmd (tyArr !tyCmd !tyCmd))) I.If ::
       @SymEnv.F typ _ (tyArr !tyValue !tyValue) S ::
                 (*     @SymEnv.F typ _ (tyArr tyVariable (tyArr tyExpr tyCmd))
               (I.Read) ::
     @SymEnv.F typ _ (tyArr tyExpr (tyArr tyExpr tyCmd))
               (Write) :: *)
                 (*     @SymEnv.F typ _ (tyArr tyValue (tyArr tyValue tyHProp))
               (PtsTo) :: *)
                 (* @SymEnv.F typ _ (tyArr tyValue tyProp) *)
                 (*           (Even.even) :: *)
                 (* @SymEnv.F typ _ (tyArr tyValue tyProp) *)
                 (*           (Even.odd) :: *)
                 (*
     @SymEnv.F typ _ (tyVariable >> (tyValue >> tyLProp) >> (tyValue >> tyLProp) >> tySProp)
               (function_spec) ::
                  *)
       nil).

  Definition lops : @logic_ops typ _ :=
    fun t : typ =>
      match t as t
             return loption (ILogic.ILogicOps@{Urefl Urefl} (TypesI.typD t))
      with
      | tyArr a b =>
        match a , b with
        | tyBase0 a , tyBase0 b =>
          match a as a in tsym na , b as b in tsym nb
                return match na as na , nb as nb
                             return tsym na -> tsym nb -> Type
                       with
                       | 0 , 0 => fun a b =>
                                    loption (ILogic.ILogicOps@{Urefl Urefl} (tsymD 0 a -> tsymD _ b))
                       | _ , _ => fun _ _ => unit
                       end a b
          with
          | tyLocals , tyHProp => lSome (I.ILogicOps_lprop)
          | _ , _ => lNone
          end
        | _ , _ => lNone
        end
      | tyBase0 l =>
        match l as l in tsym 0 return loption (ILogic.ILogicOps@{Urefl Urefl} (tsymD _ l)) with
        | tyProp => lSome _
        | tyHProp => lSome _
        | tySProp => lSome _
        | _ => lNone
        end
      | tyBase1 _ _ => lNone
      | tyBase2 _ _ _ => lNone
      | tyApp _ _ => lNone
      end.

  Definition eops : embed_ops _ :=
    fun t u =>
      match t as t
            return loption
                     (ILogic.EmbedOp (TypesI.typD t) (TypesI.typD u))
      with
      | tyBase0 t =>
        match t as t in tsym 0
              return loption (ILogic.EmbedOp (tsymD _ t) (TypesI.typD u))
        with
        | tyProp =>
          match u with
          | tyBase0 u =>
            match u as u in tsym 0
                  return loption (ILogic.EmbedOp Prop (tsymD 0 u))
            with
            | tyHProp => lSome I.EmbedOp_Prop_HProp
            | tySProp => lSome I.EmbedOp_Prop_SProp
            | _ => lNone
            end
          | tyArr a b =>
            match a as a , b as b
                  return loption (ILogic.EmbedOp Prop (TypesI.typD a -> TypesI.typD b))
            with
            | tyBase0 a , tyBase0 b =>
              match a as a in tsym na , b as b in tsym nb
                    return match na as na , nb as nb
                                 return tsym na -> tsym nb -> Type
                           with
                           | 0 , 0 => fun a b => loption (ILogic.EmbedOp Prop (tsymD _ a -> tsymD _ b))
                           | _ , _ => fun _ _ => unit
                           end a b
              with
              | tyLocals , tyHProp => lSome (@ILogic.EmbedOp_Fun _ _ I.EmbedOp_Prop_HProp _)
              | _ , _ => lNone
              end
            | _ , _ => lNone
            end
          | _ => lNone
          end
        | tyHProp =>
          match u with
          | tyArr a b =>
            match a as a , b as b
                  return loption (ILogic.EmbedOp I.HProp (TypesI.typD a -> TypesI.typD b))
            with
            | tyBase0 a , tyBase0 b =>
              match a as a in tsym na , b as b in tsym nb
                    return match na as na , nb as nb
                                 return tsym na -> tsym nb -> Type
                           with
                           | 0 , 0 => fun a b => loption (ILogic.EmbedOp I.HProp (tsymD _ a -> tsymD _ b))
                           | _ , _ => fun _ _ => unit
                           end a b
              with
              | tyLocals , tyHProp => lSome I.EmbedOp_HProp_lprop
              | _ , _ => lNone
              end
            | _ , _ => lNone
            end
          | _ => lNone
          end
        | _ => lNone
        end
      | _ => lNone
      end.

  Lemma tsym0_case : forall x : tsym 0,
      x = tyLocals \/ x = tyCmd \/ x = tyProp \/ x = tyHProp \/ x = tySProp
      \/ x = tyVariable \/ x = tyExpr \/ x = tyValue.
  Proof using.
    intro.
    refine
      match x as x in tsym n
            return match n as n return tsym n -> Prop with
                   | 0 => fun x => _
                   | S _ => fun _ => True
                   end x
      with
      | tyLocals => _
      | _ => _
      end; tauto.
  Qed.

  Theorem lops_ok : ILogicFunc.logic_opsOk lops.
  Proof.
    red.
    destruct g; simpl; auto.
    { destruct g1; auto.
      destruct g2; auto.
      clear.
      destruct (tsym0_case t);
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H
               end; subst; auto.
      destruct (tsym0_case t0);
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H
               end; subst; auto.
      simpl.
      eapply ILogic.ILogic_Fun. eapply I.ILogic_HProp. }
    { destruct (tsym0_case t);
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             end; subst; eauto with typeclass_instances; simpl. }
  Qed.

  Theorem eops_ok : ILogicFunc.embed_opsOk lops eops.
  Proof.
    red.
    destruct t; simpl; auto.
    + destruct t1; auto. destruct t2; auto.
      generalize (tsym0_case t); intro ;
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H; subst; auto
               end.
      generalize (tsym0_case t0); intro ;
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H; subst; auto
               end.
      intros; destruct (lops t'); trivial.
    + generalize (tsym0_case t); intro ;
        repeat match goal with
               | H : _ \/ _ |- _ => destruct H; subst; auto
               end.
      - destruct t'; simpl; auto.
        destruct t'1; simpl; auto.
        * destruct t'2; simpl; auto.
          generalize (tsym0_case t); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end.
          generalize (tsym0_case t0); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end.
          eapply ILogic.Embed_Fun.
        * generalize (tsym0_case t); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end; simpl.
          eapply I.Embed_Prop_HProp.
          eapply I.Embed_Prop_SProp.
      - destruct t'; simpl; auto.
        * destruct t'1; simpl; auto.
          destruct t'2; simpl; auto.
          generalize (tsym0_case t); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end.
          generalize (tsym0_case t0); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end.
          eapply ILogic.Embed_Fun.
        * generalize (tsym0_case t); intro ;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H; subst; auto
                 end.
      - intros. destruct (lops t'); auto.
  Qed.

  Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
    @ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _.

  Definition RS (fs' : functions typ RType_typ): SymI.RSym func :=
    SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func (join_functions fs fs')) _) _.
(*  Local Existing Instance RS. *)

  Instance RSOk fs' : SymI.RSymOk (RS fs').
  eapply RSymOk_sum; eauto with typeclass_instances.
  eapply RSymOk_sum; eauto with typeclass_instances.
  Defined.

  Definition Expr_expr (fs' : functions typ RType_typ)
  : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ (RS fs').
  Local Existing Instance Expr_expr.

  Definition ExprOk_expr fs' : ExprI.ExprOk (Expr_expr fs') := ExprOk_expr.
  Existing Instance ExprOk_expr.

  Instance RelDec_eq_imp_func : RelDec (@eq imp_func) :=
  { rel_dec := fun a b =>
    match a , b with
    | pVar a , pVar b => a ?[ eq ] b
    | pNat a , pNat b => a ?[ eq ] b
    | pLocals_get , pLocals_get => true
    | pLocals_upd , pLocals_upd => true
    | pEq a , pEq b => a ?[ eq ] b
    | pEval_expri , pEval_expri => true
    | eVar , eVar
    | eConst , eConst => true
    | pAp a a' , pAp b b' => (a ?[ eq ] b) && (a' ?[ eq ] b')
    | pPure a , pPure b => a ?[ eq ] b
    | pUpdate a , pUpdate b => a ?[ eq ] b
    | _ , _ => false
    end
  }.


  Instance RelDec_eq_func : RelDec (@eq func) :=
  { rel_dec := fun a b =>
    match a , b with
    | inl (inl a) , inl (inl b) => a ?[ eq ] b
    | inl (inr a) , inl (inr b) => a ?[ eq ] b
    | inr a , inr b => a ?[ eq ] b
    | _ , _ => false
    end
  }.

  Definition RelDec_eq_expr : RelDec (@eq (expr typ func)) :=
    @RelDec_eq_expr typ func _ _.

  Print fs.
  Definition fTriple : expr typ func := Inj (inl (inl 1%positive)).
  Definition fSeq : expr typ func := Inj (inl (inl 2%positive)).
  Definition fAssign : expr typ func := Inj (inl (inl 3%positive)).
  Definition fSkip : expr typ func := Inj (inl (inl 4%positive)).
  Definition fAssert : expr typ func := Inj (inl (inl 5%positive)).
  Definition fIf : expr typ func := Inj (inl (inl 6%positive)).
(*
  Definition fRead : expr typ func := Inj (inl (inl 4%positive)).
  Definition fWrite : expr typ func := Inj (inl (inl 5%positive)).
  Definition fPtsTo : expr typ func := Inj (inl (inl 8%positive)).
*)
  Definition fEven : expr typ func := Inj (inl (inl 9%positive)).
  Definition fOdd : expr typ func := Inj (inl (inl 10%positive)).
  Definition fS : expr typ func := Inj (inl (inl 7%positive)).


  Definition feVar : expr typ func := Inj (inl (inr eVar)).
  Definition feConst : expr typ func := Inj (inl (inr eConst)).
  Definition fePlus : expr typ func := Inj (inl (inr ePlus)).
  Definition fPlus : expr typ func := Inj (inl (inr natPlus)).

  Definition fVar (v : I.var) : expr typ func := Inj (inl (inr (pVar v))).
  Definition fConst (c : I.value) : expr typ func := Inj (inl (inr (pNat c))).
  Definition fAp (t u : typ) : expr typ func := Inj (inl (inr (pAp t u))).
  Definition fPure (t : typ) : expr typ func := Inj (inl (inr (pPure t))).
  Definition flocals_get : expr typ func := Inj (inl (inr pLocals_get)).
  Definition flocals_upd : expr typ func := Inj (inl (inr pLocals_upd)).
  Definition fupdate t : expr typ func := Inj (inl (inr (pUpdate t))).
  Definition feval_iexpr : expr typ func := Inj (inl (inr pEval_expri)).
  Definition fEq (t : typ) : expr typ func := Inj (inl (inr (pEq t))).

  Definition mkTriple (P c Q : expr typ func) : expr typ func :=
    App (App (App fTriple P) c) Q.
  Definition mkSeq (a b : expr typ func) : expr typ func :=
    App (App fSeq a) b.
  Definition mkAssign (a b : expr typ func) : expr typ func :=
    App (App fAssign a) b.
(*
  Definition mkRead (a b : expr typ func) : expr typ func :=
    App (App fRead a) b.
  Definition mkWrite (a b : expr typ func) : expr typ func :=
    App (App fWrite a) b.
*)
  Definition mkSkip : expr typ func := fSkip.

  Definition lex (l t : typ) (e : expr typ func) : expr typ func :=
    App (Inj (inr (ilf_exists t l))) (Abs t e).

(*Definition lstar (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (fStar l)  e) e'.
Definition lemp (l : typ) : expr typ func := fEmp l.
*)
  Definition land (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App (Inj (inr (ilf_and l))) e) e'.
  Definition ltrue (l : typ) : expr typ func :=
    Inj (inr (ilf_true l)).
  Definition lentails (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App (Inj (inr (ilf_entails l))) e) e'.
  Definition lor (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App (Inj (inr (ilf_or l))) e) e'.
  Definition lembed (t f : typ) (e : expr typ func) : expr typ func :=
    App (Inj (inr (ilf_embed f t))) e.
(*
  Definition lPtsTo (a b : expr typ func) : expr typ func :=
    App (App fPtsTo a) b.
*)

  Definition lap (t u : typ) (a b : expr typ func) : expr typ func :=
    App (App (fAp t u) a) b.
  Definition lpure (t : typ) (a : expr typ func) : expr typ func :=
    App (fPure t) a.
  Definition lupdate (t : typ) (a b : expr typ func) : expr typ func :=
    App (App (fupdate t) a) b.

(*
(** Testing function **)
Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs tyProp e)
          Typ0_Prop nil nil.
*)
  (** Reification *)
  Require Import MirrorCore.Reify.Reify.

  Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
  Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
  Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
  Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
  Local Notation "'#'" := RIgnore (only parsing, at level 0).

  Reify Declare Patterns patterns_imp_typ : typ.

  Reify Declare Typed Table term_table : BinNums.positive => typ.

  Reify Declare Syntax reify_imp_typ :=
    Patterns.CPatterns patterns_imp_typ.

  Reify Declare Patterns patterns_ilogic_func : ilfunc typ.
  Reify Declare Patterns patterns_imp_func : imp_func.
  Reify Declare Patterns patterns_imp : expr typ func.

  Definition mkLogic (x : ilfunc typ) : expr typ func :=
    ExprCore.Inj (inr x).
  Print func.
  Definition mkImp (x : imp_func) : expr typ func :=
    ExprCore.Inj (inl (inr x)).
  Definition mkExt (x : SymEnv.func) : expr typ func :=
    ExprCore.Inj (inl (inl x)).


  Reify Declare Syntax reify_imp :=
    Patterns.CFirst (   Patterns.CVar (@ExprCore.Var typ func)
                     :: Patterns.CMap mkLogic patterns_ilogic_func
                     :: Patterns.CMap mkImp patterns_imp_func
                     :: Patterns.CPatterns patterns_imp
                     :: Patterns.CApp (@ExprCore.App typ func)
                     :: Patterns.CAbs reify_imp_typ (@ExprCore.Abs typ func)
                     :: Patterns.CMap mkExt (Patterns.CTypedTable reify_imp_typ term_table)
                     :: nil).

  (** BEGIN LOGIC REIFY **)
  (** TODO: It would be nice to be able to put these elsewhere *)
  Reify Pattern patterns_ilogic_func += (!! @ILogic.lentails @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_entails typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.ltrue @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_true typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.lfalse @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_false typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.land @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_and typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.lor @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_or typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.limpl @ ?0 @ #) =>
    fun (x : function reify_imp_typ) => @ILogicFunc.ilf_impl typ x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.lexists @ ?0 @ # @ ?1) =>
    fun (x y : function reify_imp_typ) => @ILogicFunc.ilf_exists typ y x.
  Reify Pattern patterns_ilogic_func += (!! @ILogic.lforall @ ?0 @ # @ ?1) =>
    fun (x y : function reify_imp_typ) => @ILogicFunc.ilf_forall typ y x.

  (** Embedding Operators **)
  Reify Pattern patterns_ilogic_func += (!! @ILogic.embed @ ?0 @ ?1 @ #) =>
    fun (x y : function reify_imp_typ) => ILogicFunc.ilf_embed x y.

  (** Special cases for Coq's primitives **)
  Reify Pattern patterns_ilogic_func += (!!True) => ILogicFunc.ilf_true !tyProp.
  Reify Pattern patterns_ilogic_func += (!!False) => ILogicFunc.ilf_false !tyProp.
  Reify Pattern patterns_ilogic_func += (!!and) => ILogicFunc.ilf_and !tyProp.
  Reify Pattern patterns_ilogic_func += (!! or) => ILogicFunc.ilf_or !tyProp.

  Reify Pattern patterns_imp += (RPi (?0) (?1)) =>
    fun (x : function reify_imp_typ) (y : function reify_imp) =>
      ExprCore.App (mkLogic (@ILogicFunc.ilf_forall typ x !tyProp ))
                   (@ExprCore.Abs typ func x y).
  Reify Pattern patterns_imp += (RImpl (?0) (?1)) =>
    fun (x y : function reify_imp) =>
      ExprCore.App (ExprCore.App (mkLogic (@ILogicFunc.ilf_impl typ !tyProp)) x) y.
  (** END LOGIC REIFY **)



  (** BEGIN TYPE REIFY **)
  Reify Pattern patterns_imp_typ += (@RImpl (?0) (?1)) =>
    fun (a b : function reify_imp_typ) => tyArr a b.
  Reify Pattern patterns_imp_typ += (!! I.locals)  => !tyLocals.
  Reify Pattern patterns_imp_typ += (!! I.lprop)  => tyArr !tyLocals !tyHProp.
  Reify Pattern patterns_imp_typ += (!! I.icmd) => !tyCmd.
  Reify Pattern patterns_imp_typ += (!! I.SProp) => !tySProp.
  Reify Pattern patterns_imp_typ += (!! I.HProp) => !tyHProp.
  Reify Pattern patterns_imp_typ += (!! Prop) => !tyProp.
  Reify Pattern patterns_imp_typ += (!! I.var) => !tyVariable.
  Reify Pattern patterns_imp_typ += (!! I.iexpr) => !tyExpr.
  Reify Pattern patterns_imp_typ += (!! nat)  => !tyValue.
  Reify Pattern patterns_imp_typ += (!! I.value)  => !tyValue.
  Reify Pattern patterns_imp_typ += (!! Fun @ ?0 @ ?1) =>
    fun (a b : function reify_imp_typ) => tyArr a b.
  Reify Pattern patterns_imp_typ += (!! PreFun.Fun @ ?0 @ ?1) =>
    fun (a b : function reify_imp_typ) => tyArr a b.


  (** BEGIN TERM REIFY **)
  (** Reify imp_func **)
  Reify Pattern patterns_imp_func += (RHasType var (?!0)) =>
    fun (x : id I.var) => pVar x.
  Reify Pattern patterns_imp_func += (RHasType String.string (?!0)) =>
    fun (x : id I.var) => pVar x.
  Reify Pattern patterns_imp_func += (RHasType nat (?!0)) =>
    fun (x : id nat) => pNat x.
  Reify Pattern patterns_imp_func += (!! (@eq) @ ?0) =>
    fun (x : function reify_imp_typ) => pEq x.
  Reify Pattern patterns_imp_func += (!! I.locals_get) =>
    pLocals_get.
  Reify Pattern patterns_imp_func += (!! I.locals_upd) =>
    pLocals_upd.
  Reify Pattern patterns_imp_func += (!! I.eval_iexpr) =>
    pEval_expri.

  (** Expressions **)
  Reify Pattern patterns_imp_func += (!! I.iConst) => eConst.
  Reify Pattern patterns_imp_func += (!! I.iVar) => eVar.
  Reify Pattern patterns_imp_func += (!! I.iPlus) => ePlus.

  (** Arith **)
  Reify Pattern patterns_imp_func += (!! plus) => natPlus.

  (** Applicative **)
  Reify Pattern patterns_imp_func += (!! @Applicative.ap @ !! (PreFun.Fun I.locals) @ # @ ?0 @ ?1) =>
    fun (x y : function reify_imp_typ) => fAp x y.
  Reify Pattern patterns_imp += (!! @Applicative.pure @ !! (PreFun.Fun I.locals) @ # @ ?0) =>
    fun (x : function reify_imp_typ) => fPure x.

(*
  (** Commands **)
  Reify Pattern patterns_imp_func += (!! I.Skip) => fSkip.
  Reify Pattern patterns_imp += (!! I.Seq) => fSeq.
  Reify Pattern patterns_imp += (!! I.Assign) => fAssign.
  Reify Pattern patterns_imp += (!! I.Assert) => fAssert.
  Reify Pattern patterns_imp += (!! I.If) => fIf.

  (** Program Logic **)
Reify Pattern patterns_imp += (!! triple) => fTriple.
Reify Pattern patterns_imp += (!! eval_iexpr) => feval_iexpr.
Reify Pattern patterns_imp += (!! locals_get) => flocals_get.
Reify Pattern patterns_imp += (!! locals_upd) => flocals_upd.

Reify Pattern patterns_imp += (!! PtsTo) => fPtsTo.
*)

  (** Table Entries **)
  Local Notation "a >> b" := (tyArr a b) (at level 31,right associativity).

(*
  Reify Pattern patterns_imp += (!!I.triple) => fTriple.
  Reify Pattern patterns_imp += (!!I.Seq) => fSeq.
  Reify Pattern patterns_imp += (!!I.Assign) => fAssign.
  Reify Pattern patterns_imp += (!!I.Skip) => fSkip.
  Reify Pattern patterns_imp += (!!I.Assert) => fAssert.
  Reify Pattern patterns_imp += (!!I.If) => fIf.
*)

  Reify Seed Typed Table term_table += 1 =>
    [[ (tyLProp >> !tyCmd >> tyLProp >> !tySProp) , I.triple ]].
  Reify Seed Typed Table term_table += 2 =>
    [[ (!tyCmd >> !tyCmd >> !tyCmd) , I.Seq ]].
  Reify Seed Typed Table term_table += 3 =>
    [[ (!tyVariable >> !tyExpr >> !tyCmd) , I.Assign ]].
  Reify Seed Typed Table term_table += 4 => [[ !tyCmd , I.Skip ]].
  Reify Seed Typed Table term_table += 5 => [[ (tyLProp >> !tyCmd) , I.Assert ]].
  Reify Seed Typed Table term_table += 6 => [[ (!tyExpr >> !tyCmd >> !tyCmd >> !tyCmd) , I.If ]].

(*
  Reify Seed Typed Table term_table += 4 =>
    [[ (tyVariable >> tyExpr >> tyCmd) , Read ].
  Reify Seed Typed Table term_table += 5 => [ (tyExpr >> tyExpr >> tyCmd) , Write ].

  Reify Seed Typed Table term_table += 7 => [ (tyNat >> tyNat >> tyHProp) , PtsTo ].
  Reify Seed Typed Table term_table += 8 => [ (tyNat >> tyProp) , Even.even ].
  Reify Seed Typed Table term_table += 9 => [ (tyNat >> tyProp) , Even.odd ].
  Reify Seed Typed Table term_table += 10 => [ tyNat , O ].
  Reify Seed Typed Table term_table += 11 => [ (tyNat >> tyNat) , S ].
*)

  Definition elem_ctor : forall x : typ, (typD x) -> @SymEnv.function _ _ :=
    @SymEnv.F _ _.

  Ltac reify_imp e :=
    let k fs e :=
        pose e in
    reify_expr reify_imp k
               [[ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]]
               [[ e ]].

  Reify Pattern patterns_imp += (!! S) => (fS).

  Definition assert_at {T} (p : BinNums.positive) (a b : T) : Prop :=
    a = b.

  Fixpoint check_compat (p : BinNums.positive) (a b : SymEnv.functions _ _) : Prop :=
    match a , b with
    | FMapPositive.PositiveMap.Node l v r , FMapPositive.PositiveMap.Node l' v' r' =>
      match v , v' with
      | Some x , Some y => assert_at p x y
      | _ , _ => True
      end /\ check_compat (BinNums.xO p) l l' /\ check_compat (BinNums.xI p) r r'
    | _ , _ => True
    end.


  Goal True.
    reify_imp I.locals_upd.
    reify_imp (3 = 3).
    reify_imp I.Skip.
    reify_imp (ILogic.lentails True True).
    reify_imp ((True -> False) -> True).
    reify_imp (forall G P Q, ILogic.lentails G (I.triple P I.Skip Q)).
    exact I.
  Defined.

  Require Import MirrorCore.RTac.RTac.

  (** TODO(gmalecha): Specifying this like this is not ideal.
   ** Essentially this list is constructed from a
   ** [Print Transparent Dependencies] of a few terms and it would be
   ** good if we could implement it just like that.
   **)
  Ltac reduce_propD tbl g e := eval cbn beta iota zeta delta
    [ tbl g Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      RS ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip

      tbl Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym
      mkExt mkLogic mkImp

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip


  var uvar typeof_sym type_cast typD typ2_match typ2_cast typ2 tenv
      symD symAs
      HList.nth_error_get_hlist_nth ExprDsimul.ExprDenote.lambda_exprD
      HList.hlist_tl HList.hlist_hd
      ExprDsimul.ExprDenote.func_simul
      exprT_UseU exprT_UseV exprT_Inj
      ExprDsimul.ExprDenote.exprT_GetVAs
      ExprDsimul.ExprDenote.exprT_GetUAs
      AbsAppI.exprT_App
      exprT
      eq_trans
      eq_sym
      Rty
      Rsym
      Relim
      RFun
      OpenT
      ExprDsimul.ExprDenote.Rcast_val
      ExprDsimul.ExprDenote.Rcast

      BinPos.Pos.succ
      SymEnv.from_list
      FMapPositive.PositiveMap.empty
      FMapPositive.PositiveMap.add


      (* RS Dependencies *)
      Vector.vector_tl
      Vector.vector_hd
      Vector.vector_map
      Vector.vector_dec
      typeof_sym_imp
      typeof_sym
      ILogicFunc.typeof_func
      ModularTypes.type_for_arity
      type_cast
      typD
      ILogicFunc.typ2_cast_quant
      ILogicFunc.typ2_cast_bin
      typ2_cast
      typ2
      typ0
      typ0_cast
      typ
      tyLProp
      tsym_tag
      tsym_neq

      tsym_dec
      tsymD
      sym_eqb
      symD
      sumbool_rect
      sumbool_rec
      BinPos.Pos.succ
      String.string_dec
      RelDec.rel_dec
      Applicative.pure
      projT2
      projT1
      Nat.pred


      not
      nat_rect
      nat_rec
      nat_eq_eqdec
      ModularTypes.mtyp_dec
      ModularTypes.mtyp_cast
      ModularTypes.mtypD

      lops
      SymEnv.join_functions
      EqdepFacts.internal_eq_sym_involutive
      EqdepFacts.internal_eq_sym_internal
      EqdepFacts.internal_eq_rew_r_dep
      Injection.injection

      imp_func_eq
      SymEnv.func_typeof_sym
      SymEnv.funcD
      ILogicFunc.funcD
      SymEnv.ftype
      fs
      SymEnv.from_list
      FMapPositive.PositiveMap.find
      SymEnv.fdenote
      f_equal_nat
      f_equal
      BinPos.Pos.eqb
      PeanoNat.Nat.eqb
      eq_trans
      eq_sym
      eq_rect
      eq_ind_r
      eq_ind
      eq_equivalence
      PeanoNat.Nat.eq_dec
      eq_add_S
      eq_Transitive
      eq_Symmetric
      eq_Reflexive
      eops
      FMapPositive.PositiveMap.empty
      complement
      bool_rect
      bool_rec
      Bool.bool_dec
      Ascii.ascii_rect
      Ascii.ascii_rec
      Ascii.ascii_dec
      ModularTypes.applyn'
      ModularTypes.applyn
      Applicative.ap
      andb
      and_rect
      and_ind
      FMapPositive.PositiveMap.add
      Typ2_Fun
      ModularTypes.Typ2_Fun
      ModularTypes.Typ0_sym
      Typ0_Prop
      Rty
      String.RelDec_string
      Positive.RelDec_peq
      ILogicFunc.RelDec_ilfunc
      RelDec_eq_typ
      SymEnv.RelDec_eq_func
      Nat.RelDec_eq
      RelDec_Rty
      RType_typ
      ModularTypes.RType_mtyp
      SymSum.RSym_sum
      RSym_imp_func
      RSym_ilfunc
      ILogicFunc.RSym_ilfunc
      SymEnv.RSym_func
      RS
      RFun
      ModularTypes.Injective_tyApp
      Fun
      ILogic.EmbedOp_refl
      ILogic.EmbedOp_Fun
      Applicative_Fun
      UIP_trans.uip_trans
      UIP_trans.uip_prop_trans
      RS
      RFun
      ModularTypes.Injective_tyApp
      Fun
      Applicative_Fun
      Traversable.mapT
      List.Traversable_list Option.Applicative_option
      List.mapT_list
      Ctx.propD exprD_typ0 exprD Expr_expr app
      Quant._impls
      List.map
      HList.hlist_app
      amap_substD FMapSubst.SUBST.raw_substD UVarMap.MAP.fold FMapPositive.PositiveMap.fold FMapPositive.PositiveMap.xfoldi HList.nth_error_get_hlist_nth UVarMap.MAP.from_key FMapPositive.append Nat.pred BinPos.Pos.to_nat BinPos.Pos.iter_op Nat.add
      tsym_dec Quant._exists exprT_Inj
      UVarMap.MAP.from_key
      Nat.pred BinPos.Pos.to_nat BinPos.Pos.iter_op Nat.add  ModularTypes.mtyp_cast
      ModularTypes.symbol_dec ModularTypes.symbolD TSym_tsym
    ] in e.

(*
  Ltac reduce_propD tbl g e := eval cbv beta iota zeta delta
    [ tbl g Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      RS ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip
e tbl Quant._foralls goalD Ctx.propD exprD_typ0 exprD Expr_expr Expr.Expr_expr
      ExprDsimul.ExprDenote.lambda_exprD symAs typ0_cast
      typeof_sym type_cast RType_typ typ2_match
      typ2 Relim exprT_Inj eq_ind eq_rect eq_rec
      AbsAppI.exprT_App eq_sym
      typ0_cast
      typ2_cast sumbool_rec sumbool_rect eq_ind_r f_equal typ0 typ2 symD
      ExprDsimul.ExprDenote.func_simul Typ0_Prop Typ2_Fun typeof_sym
      mkExt mkLogic mkImp

      PeanoNat.Nat.eq_dec bool_rect bool_rec complement Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec
      typeof_sym RS SymSum.RSym_sum SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add BinPos.Pos.succ FMapPositive.PositiveMap.empty SymEnv.ftype RSym_imp_func typeof_sym_imp imp_func_eq
      FMapPositive.PositiveMap.empty
      ModularTypes.Typ0_sym
      ModularTypes.Injective_tyApp
      ILogicFunc.typ2_cast_bin ILogicFunc.typ2_cast_quant tsym_dec
      sumbool_rect sumbool_rec String.string_dec
      SymSum.RSym_sum RSym_imp_func SymEnv.RSym_func
      ModularTypes.RType_mtyp SymEnv.func_typeof_sym fs
      FMapPositive.PositiveMap.find BinPos.Pos.succ
      SymEnv.from_list FMapPositive.PositiveMap.add SymEnv.ftype
      SymEnv.funcD ModularTypes.Typ2_Fun ModularTypes.mtyp_cast ILogicFunc.RSym_ilfunc RSym_ilfunc ILogicFunc.typeof_func lops
      ILogicFunc.funcD typD ModularTypes.mtypD exprT OpenT tsymD
      fAssign fTriple fSkip


  var uvar typeof_sym type_cast typD typ2_match typ2_cast typ2 tenv
      symD symAs
      HList.nth_error_get_hlist_nth ExprDsimul.ExprDenote.lambda_exprD
      HList.hlist_tl HList.hlist_hd
      ExprDsimul.ExprDenote.func_simul
      exprT_UseU exprT_UseV exprT_Inj
      ExprDsimul.ExprDenote.exprT_GetVAs
      ExprDsimul.ExprDenote.exprT_GetUAs
      AbsAppI.exprT_App
      exprT
      eq_trans
      eq_sym
      Rty
      Rsym
      Relim
      RFun
      OpenT
      ExprDsimul.ExprDenote.Rcast_val
      ExprDsimul.ExprDenote.Rcast

      BinPos.Pos.succ
      SymEnv.from_list
      FMapPositive.PositiveMap.empty
      FMapPositive.PositiveMap.add


      (* RS Dependencies *)
      Vector.vector_tl
      Vector.vector_hd
      Vector.vector_map
      Vector.vector_dec
      typeof_sym_imp
      typeof_sym
      ILogicFunc.typeof_func
      ModularTypes.type_for_arity
      type_cast
      typD
      ILogicFunc.typ2_cast_quant
      ILogicFunc.typ2_cast_bin
      typ2_cast
      typ2
      typ0
      typ0_cast
      typ
      tyLProp
      tsym_tag
      tsym_neq

      tsym_dec
      tsymD

      sym_eqb
      symD
      sumbool_rect
      sumbool_rec
      BinPos.Pos.succ
      String.string_dec
      RelDec.rel_dec
      Applicative.pure
      projT2
      projT1
      Nat.pred


      not
      nat_rect
      nat_rec
      nat_eq_eqdec
      ModularTypes.mtyp_dec
      ModularTypes.mtyp_cast
      ModularTypes.mtypD

      lops
      SymEnv.join_functions
      EqdepFacts.internal_eq_sym_involutive
      EqdepFacts.internal_eq_sym_internal
      EqdepFacts.internal_eq_rew_r_dep
      Injection.injection

      imp_func_eq
      SymEnv.func_typeof_sym
      SymEnv.funcD
      ILogicFunc.funcD
      SymEnv.ftype
      fs
      SymEnv.from_list
      FMapPositive.PositiveMap.find
      SymEnv.fdenote
      f_equal_nat
      f_equal
      BinPos.Pos.eqb
      PeanoNat.Nat.eqb
      eq_trans
      eq_sym
      eq_rect
      eq_ind_r
      eq_ind
      eq_equivalence
      PeanoNat.Nat.eq_dec
      eq_add_S
      eq_Transitive
      eq_Symmetric
      eq_Reflexive
      eops
      FMapPositive.PositiveMap.empty
      ILogic.embed
      complement
      bool_rect
      bool_rec
      Bool.bool_dec
      Ascii.ascii_rect
      Ascii.ascii_rec
      Ascii.ascii_dec
      ModularTypes.applyn'
      ModularTypes.applyn
      Applicative.ap
      andb
      and_rect
      and_ind
      FMapPositive.PositiveMap.add
      Nat.add
      Typ2_Fun
      ModularTypes.Typ2_Fun
      ModularTypes.Typ0_sym
      Typ0_Prop
      Rty
      String.RelDec_string
      Positive.RelDec_peq
      ILogicFunc.RelDec_ilfunc
      RelDec_eq_typ
      SymEnv.RelDec_eq_func
      Nat.RelDec_eq
      RelDec_Rty
      RType_typ
      ModularTypes.RType_mtyp
      SymSum.RSym_sum
      RSym_imp_func
      RSym_ilfunc
      ILogicFunc.RSym_ilfunc
      SymEnv.RSym_func
      RS
      RFun
      ModularTypes.Injective_tyApp
      I.ILogicOps_lprop
      Fun
      EqdepFacts.Eq_rect_eq_on
      EqdepFacts.Eq_rect_eq
      EqdepFacts.Eq_dep_eq_on
      EqdepFacts.Eq_dep_eq
      ILogic.EmbedOp_refl
      ILogic.EmbedOp_Fun
      Applicative_Fun
      ModularTypes.symbol_dec ModularTypes.symbolD TSym_tsym
    ] in e.
*)

End ImpSyntax.
