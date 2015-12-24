Require Import Coq.Bool.Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ModularTypes.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Views.FuncView.
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

  Definition typ := mtyp tsym.

  Global Instance RType_typ : RType typ := RType_mtyp _ tsymD (@tsym_dec).
  Global Instance RTypeOk_typ : RTypeOk := RTypeOk_mtyp _ _ _.

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
    Require Import ExtLib.Tactics.Consider.
    all: match goal with
         | |- context [ if ?X then _ else _ ] =>
           consider X; intros; unfold Rty in *; try congruence
         end.
    f_equal; tauto.
    destruct H; congruence.
  Qed.

  Instance FuncView_ilfunc : FuncView func (ilfunc typ).
  Admitted.

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

  Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
    @ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _.

  Definition RS : SymI.RSym func :=
    SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) _) _.
  Local Existing Instance RS.

  Instance RSOk : SymI.RSymOk RS.
  eapply RSymOk_sum; eauto with typeclass_instances.
  eapply RSymOk_sum; eauto with typeclass_instances.
  Defined.

  Definition Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
  Local Existing Instance Expr_expr.

  Definition ExprOk_expr : ExprI.ExprOk Expr_expr := ExprOk_expr.
  Existing Instance ExprOk_expr.

(*
Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Definition SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
Definition SU : SubstI.SubstUpdate subst (expr typ func) :=
  @FMapSubst.SUBST.SubstUpdate_subst _ _.
Definition SO := FMapSubst.SUBST.SubstOk_subst.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance SO.
*)


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


  Definition fTriple : expr typ func := Inj (inl (inl 1%positive)).
  Definition fSeq : expr typ func := Inj (inl (inl 2%positive)).
  Definition fAssign : expr typ func := Inj (inl (inl 3%positive)).
  Definition fSkip : expr typ func := Inj (inl (inl 6%positive)).
  Definition fAssert : expr typ func := Inj (inl (inl 7%positive)).
(*
  Definition fRead : expr typ func := Inj (inl (inl 4%positive)).
  Definition fWrite : expr typ func := Inj (inl (inl 5%positive)).
  Definition fPtsTo : expr typ func := Inj (inl (inl 8%positive)).
*)
  Definition fEven : expr typ func := Inj (inl (inl 9%positive)).
  Definition fOdd : expr typ func := Inj (inl (inl 10%positive)).
  Definition fS : expr typ func := Inj (inl (inl 11%positive)).


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
  Definition mkExt (x : BinNums.positive) : expr typ func :=
    ExprCore.Inj (inl (inl x)).


  Reify Declare Syntax reify_imp :=
    Patterns.CFirst (   Patterns.CVar (@ExprCore.Var typ func)
                     :: Patterns.CMap mkLogic patterns_ilogic_func
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

  Print fs.

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

  Goal True.
    reify_imp I.Skip.
    reify_imp (ILogic.lentails True True).
    reify_imp ((True -> False) -> True).
    reify_imp (forall G P Q, ILogic.lentails G (I.triple P I.Skip Q)).
    Set Printing All.
    exact I.
  Defined.


End ImpSyntax.
