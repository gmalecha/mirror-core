Require Import List Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import MirrorCore.Generic.
Require Import MirrorCore.TypesExt.

Set Implicit Arguments.
Set Strict Implicit.

Section env.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Context {RTypeOk_typ : RTypeOk RType_typ}.
  Context {typ_arr : TypInstance2 typD Fun}.
  Context {typ_prop : TypInstance0 typD Prop}.
  Let tvArr := @typ2 _ _ _ typ_arr.
  Let arrow_match := @typ2_match _ _ _ typ_arr.
  Let arrow_in ts a b : (typD ts a -> typD ts b) -> typD ts (tvArr a b) :=
    @into _ _ (@typ2_iso _ _ _ typ_arr (fun x => x) ts a b).
  Let arrow_out ts a b : typD ts (tvArr a b) -> (typD ts a -> typD ts b) :=
    @outof _ _ (@typ2_iso _ _ _ typ_arr (fun x => x) ts a b).
  Let tvProp := @typ0 _ _ _ typ_prop.
  Let prop_match := @typ0_match _ _ _ typ_prop.
  Let prop_in ts : Prop -> typD ts tvProp := 
    @into _ _ (@typ0_iso _ _ _ typ_prop (fun x => x) ts).
  Let prop_out ts : typD ts tvProp -> Prop := 
    @outof _ _ (@typ0_iso _ _ _ typ_prop (fun x => x) ts).

  Definition typ_cast_val ts (a b : typ) (v : typD ts a) : option (typD ts b) :=
    match typ_cast (fun x => x) ts a b with
      | None => None
      | Some f => Some (f v)
    end.

  Definition func := nat.
  Record tfunction : Type := 
  { tfenv : nat ; tftype : typ }.
  Definition tfunctions := list tfunction.
  Definition var := nat.
  Definition uvar := nat.

  Unset Elimination Schemes.

  Inductive expr : Type :=
  | Const : forall t : typ, typD nil t -> expr
  | Var : var -> expr
  | Func : func -> list typ -> expr
  | App : expr -> list expr -> expr
  | Abs : typ -> expr -> expr
  | UVar : uvar -> expr
  | Equal : typ -> expr -> expr -> expr
  | Not : expr -> expr.

  Definition exprs : Type := list expr.

  Set Elimination Schemes.

  Section expr_ind.
    Variable P : expr -> Prop.
    Hypothesis HConst : forall (t : typ) (v : typD nil t), P (@Const t v).
    Hypothesis HVar : forall v : var, P (Var v).
    Hypothesis HFunc : forall f ts, P (Func f ts).
    Hypothesis HUVar : forall v : var, P (UVar v).
    Hypothesis HApp : forall f es, P f -> Forall P es -> P (App f es).
    Hypothesis HAbs : forall t e, P e -> P (Abs t e).
    Hypothesis HEqual : forall t e1 e2, P e1 -> P e2 -> P (Equal t e1 e2).
    Hypothesis HNot : forall e, P e -> P (Not e).
    
    Fixpoint expr_ind x : P x.
    Proof.
    refine (
      match x as x return P x with
        | Const _ _ => HConst _
        | Var _ => HVar _
        | UVar _ => HUVar _
        | Func _ _ => HFunc _ _
        | Abs _ _ => HAbs _ (expr_ind _)
        | App _ _ => HApp (expr_ind _) ((fix all es : Forall P es :=
          match es with
            | nil => Forall_nil _
            | e :: es => Forall_cons _ (expr_ind e) (all es)
          end) _)
        | Equal _ _ _ => HEqual _ (expr_ind _) (expr_ind _)
        | Not _ => HNot (expr_ind _)
      end).
    Qed.
  End expr_ind.

  Definition env : Type := list (sigT (typD nil)).

  Record function := F {
    fenv : nat ; 
    ftype : typ ;
    fdenote : parametric fenv nil (fun env => typD env ftype)
  }.

  Definition functions := list function.
  Definition variables := list typ.

  Variable funcs : functions.
  Variable meta_env : env.
  
  Definition lookupAs (ls : env) (t : typ) (i : nat)
    : option (typD nil t) :=
    match nth_error ls i with 
      | None => None
      | Some tv => 
        match typ_cast (fun x => x) _ (projT1 tv) t with
          | Some f => Some (f (projT2 tv))
          | None => None
        end
    end.

  Definition tenv := list typ.

  Fixpoint typeof (var_env : tenv) (e : expr) : option typ :=
    match e with
      | Const t _ => Some t
      | Var x => 
        match nth_error var_env x with
          | None => None
          | Some tv => Some tv
        end
      | UVar x => 
        match nth_error meta_env x with
          | None => None
          | Some tv => Some (projT1 tv)
        end
      | Func f ts =>
        match nth_error funcs f with
          | None => None
          | Some r => 
(*            if EqNat.beq_nat (length ts) (fenv r) then  *)
              Some (instantiate_typ (rev ts) (ftype r))
(*
            else
              None
*)
        end
      | App e es =>
        match typeof var_env e with
          | None => None
          | Some tf => type_of_apply tf (map (typeof var_env) es)
        end
      | Abs t e => 
        match typeof (t :: var_env) e with
          | None => None
          | Some t' => Some (tvArr t t')
        end
      | Equal _ _ _ => Some tvProp
      | Not _ => Some tvProp
    end.
  
  (** 
   ** The denotation function with binders must be total because we
   ** can't introduce the binder until we know that we are going to get
   ** the right type out, but, at the same time, we don't know we will
   ** succeed until after we've taken the denotation of the body, 
   ** which we can't do until we have the binder.
   **
   **)
  Fixpoint exprD' (var_env : tenv) (e : expr) (t : typ) {struct e} : 
    option (hlist (typD nil) var_env -> typD nil t).
  refine (
    match e as e return option (hlist (typD nil) var_env -> typD nil t) with
      | Const t' c => 
        match @typ_cast_val _ t' t c with
          | Some c => Some (fun _ => c)
          | None => None
        end
      | Var x => 
        match nth_error var_env x as z return z = nth_error var_env x -> option (hlist (typD nil) var_env -> typD nil t) with
          | None => fun _ => None
          | Some t' => fun pf => 
            match typ_cast (fun x => x) _ t' t with
              | Some f =>
                Some (fun e => match pf in _ = t''
                                     return match t'' with 
                                              | Some t => typD nil t
                                              | None => unit
                                            end -> typD nil t with
                                 | eq_refl => fun x => f x
                               end (hlist_nth e x))
              | None => None
            end
        end eq_refl
      | UVar x => 
        match lookupAs meta_env t x with
          | None => None
          | Some v => Some (fun _ => v)
        end
      | Func f ts' =>  
        match nth_error funcs f with
          | None => None
          | Some f =>
            match type_apply _ ts' _ _ (fdenote f) with
              | None => None
              | Some t' => 
                match @typ_cast_val _ (instantiate_typ (rev ts') (ftype f)) t t' with
                  | Some v => Some (fun _ => v)
                  | None => None
                end
            end
        end
      | Abs t' e =>
        @arrow_match nil (fun ty Ty => option (hlist (typD nil) var_env -> Ty))
           (fun lt rt =>
              match typ_cast (fun x => x) nil lt t' with
                | None => None
                | Some cast =>
                  match @exprD' (lt :: var_env) e rt with
                    | None => None
                    | Some a => Some (fun x y => a (Hcons y x))
                  end
              end)
           (fun _ => None)
           t 
      | App f xs => 
        match typeof var_env f with
          | None => None
          | Some tf =>
            match exprD' var_env f tf with
              | None => None
              | Some f =>
                (fix eval_args (t' : typ) (xs : list expr) {struct xs} : 
                  (hlist (typD nil) var_env -> typD nil t') ->
                  option (hlist (typD nil) var_env -> typD nil t) :=
                  match xs with
                    | nil =>
                      match typ_cast (fun x => x) _ t' t with
                        | None => fun _ => None
                        | Some cast => fun f => Some (fun g => cast (f g))
                      end
                    | x :: xs => 
                      @arrow_match nil
                         (fun ty Ty =>
                                   (hlist (typD nil) var_env -> Ty) ->
                            option (hlist (typD nil) var_env -> typD nil t))
                         (fun tl tr f => 
                            match exprD' var_env x tl with
                              | None => None
                              | Some xv => 
                                eval_args tr xs (fun e => f e (xv e))
                            end)
                         (fun _ _ => None)
                         t'
                  end) tf xs f
            end
        end
      | Equal t' e1 e2 =>
        @prop_match nil (fun ty Ty => option (hlist (typD nil) var_env -> Ty))
           (fun _ => 
              match exprD' var_env e1 t' , exprD' var_env e2 t' with
                | Some l , Some r => 
                  Some (fun g => equal (type := typeFor (typD := typD) nil t') (l g) (r g))
                | _ , _ => None
              end)
           (fun _ => None)
           t
      | Not e =>
        @prop_match nil (fun ty Ty => option (hlist (typD nil) var_env -> Ty))
           (fun _ => 
              match exprD' var_env e tvProp with
                | Some P => Some (fun g => not (prop_out (P g)))
                | _ => None
              end)
           (fun _ => None)
           t
    end).
  Defined.


  Definition exprD (var_env : env) (e : expr) (t : typ) : option (typD nil t) :=
    let (ts,vs) := split var_env in
    match exprD' ts e t with
      | None => None
      | Some f => Some (f vs)
    end.

  Fixpoint anyb {T} (p : T -> bool) (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls => if p l then true else anyb p ls
    end.

  Fixpoint mentionsU (u : nat) (e : expr) {struct e} : bool :=
    match e with
      | Const _ _ 
      | Var _ 
      | Func _ _ => false
      | UVar u' => EqNat.beq_nat u u'
      | App f es => 
        if mentionsU u f then true else
          (fix anyb ls : bool :=
            match ls with
              | nil => false
              | l :: ls => if mentionsU u l then true else anyb ls
            end) es
      | Abs _ e => mentionsU u e
      | Equal _ e1 e2 => if mentionsU u e1 then true else mentionsU u e2
      | Not e => mentionsU u e
    end.

  Definition const_seqb ts (a b : typ) (x : typD ts a) (y : typD ts b) : option bool :=
    match @typ_cast_val ts a b x with
      | None => None
      | Some x' => eqb ts b x' y
    end.

  Fixpoint expr_seq_dec (e1 e2 : expr) : bool.
  refine (
    match e1 , e2 with
      | Const t1 v1 , Const t2 v2 =>
        match @const_seqb nil _ _ v1 v2 with
          | Some x => x
          | None => false
        end
      | Var v1 , Var v2 => EqNat.beq_nat v1 v2
      | UVar v1 , UVar v2 => EqNat.beq_nat v1 v2
      | Func f1 ts1 , Func f2 ts2 =>
        if EqNat.beq_nat f1 f2 then 
          (fix check ts1 ts2 : bool :=
            match ts1 , ts2 with
              | nil , nil => true
              | t1 :: ts1 , t2 :: ts2 =>
                if typ_cast (fun x => x) nil t1 t2 then check ts1 ts2 else false
              | _ , _ => false
            end) ts1 ts2
        else false
      | App f1 es1 , App f2 es2 =>
        if expr_seq_dec f1 f2 then
          (fix check es1 es2 : bool :=
            match es1 , es2 with
              | nil , nil => true
              | e1 :: es1 , e2 :: es2 =>
                if expr_seq_dec e1 e2 then check es1 es2 else false
              | _ , _ => false
            end) es1 es2
        else
          false
      | Abs t1 e1 , Abs t2 e2 => 
        if typ_cast (fun x => x) nil t1 t2 then expr_seq_dec e1 e2
        else false
      | Equal t1 e1 e2 , Equal t1' e1' e2' =>
        if typ_cast (fun x => x) nil t1 t1' then 
          if expr_seq_dec e1 e1' then 
            if expr_seq_dec e2 e2' then true
            else false
          else false
        else false
      | Not e1 , Not e2 => expr_seq_dec e1 e2
      | _ , _ => false
    end).
  Defined.

  Theorem const_seqb_ok : forall ts t1 t2 a b,
    match @const_seqb ts t1 t2 a b with
      | None => True
      | Some true => 
        exists cast : typD ts t2 -> typD ts t1, equal (type := typeFor ts t1) a (cast b)
      | Some false =>
        exists cast : typD ts t2 -> typD ts t1, ~equal (type := typeFor ts t1) a (cast b)
    end.
  Proof.
    intros.
    unfold const_seqb, typ_cast_val. 
    consider (typ_cast (fun x => x) ts t1 t2); intros; auto.
    consider (eqb ts t2 (p a) b); intros; auto.
    specialize (@eqb_ok _ _ _ _ ts t2 (p a) b).
    rewrite H0.
(*
    destruct (typ_cast_iso _ _ _ H) as [ ? [ ? ? ] ].
    destruct b0; intros.
    { exists x. subst.
      destruct (typ_cast_iso _ _ _ H1) as [ ? [ ? ? ] ].
      rewrite H in H4. inversion H4; clear H4; subst. 
      admit. }
    { exists x; subst.
      intro. apply H3; clear H3; subst. admit. }
  Qed.
*) 
  Admitted.

(*
  Theorem expr_seq_dec_eq : forall e1 e2, 
    expr_seq_dec e1 e2 = true -> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros; try congruence.
    { generalize (const_seqb_ok t t0 v t1). 
      destruct (const_seqb t t0 v t1); subst; auto.
      destruct 1; subst; auto.
      admit. congruence. }
    { consider (EqNat.beq_nat v v0); subst; auto. }
    { consider (EqNat.beq_nat f f0); intros; subst.
      f_equal.
      generalize dependent l; induction ts0; destruct l; simpl in *; try congruence.
      change typ_eqb with (@rel_dec _ _ _); intros.
      consider (a ?[ eq ] t); try congruence; intros; subst.
      f_equal. eapply IHts0; auto. }
    { consider (EqNat.beq_nat v u); subst; auto. }
    { consider (expr_seq_dec e1 e2); intros.
      f_equal; eauto. clear - H1 H.
      generalize dependent l; induction H.
      { destruct l; simpl; auto; try congruence. }
      { destruct l0; simpl; auto; try congruence.
        consider (expr_seq_dec x e); intros.
        f_equal; auto. } }
    { change typ_eqb with (@rel_dec _ _ _) in *. consider (t ?[ eq ] t0).
      intros; subst. f_equal; auto. }
    { change typ_eqb with (@rel_dec _ _ _) in *.
      consider (t ?[ eq ] t0);
      consider (expr_seq_dec e1_1 e2_1); 
      consider (expr_seq_dec e1_2 e2_2); intros; subst.
      f_equal; auto. }
    { f_equal; auto. }
  Qed.
*)

End env.

Arguments Func {_ _} _ _.
Arguments Const {_ _} _ _.
Arguments UVar {_ _} _.
Arguments Var {_ _} _.
Arguments Abs {_ _} _ _.
Arguments App {_ _} _ _.

Export TypesExt.
