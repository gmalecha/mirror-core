Require Import List Bool.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Types.

Set Implicit Arguments.
Set Strict Implicit.

Section env.
  
  Variable ts : types.

  Definition func := nat.
  Record tfunction : Type := 
  { tfenv : nat ; tftype : typ }.
  Definition tfunctions := list tfunction.
  Definition var := nat.
  Definition uvar := nat.

  Unset Elimination Schemes.

  Inductive expr : Type :=
  | Const : forall t : typ, typD ts nil t -> expr
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
    Hypothesis HConst : forall (t : typ) (v : typD ts nil t), P (@Const t v).
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
        | Const _ _ => HConst _ _
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

  Definition env : Type := list (sigT (typD ts nil)).

  Record function := F {
    fenv : nat ; 
    ftype : typ ;
    fdenote : parametric fenv nil (fun env => typD ts env ftype)
  }.

  Definition Default_signature : function :=
  {| fenv := 0
   ; ftype := tvProp
   ; fdenote := True
   |}.

  Definition functions := list function.
  Definition variables := list typ.

  Variable funcs : functions.
  Variable meta_env : env.
  
  Definition lookupAs (ls : env) (t : typ) (i : nat)
    : option (typD ts nil t) :=
    match nth_error ls i with 
      | None => None
      | Some tv => 
        match typ_eq_odec (projT1 tv) t with
          | Some pf =>
            Some match pf in _ = t return typD ts nil t with
                   | refl_equal => projT2 tv
                 end
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
          | Some r => Some (instantiate_typ (rev ts) (ftype r))
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
    option (hlist (typD ts nil) var_env -> typD ts nil t) :=
    match e as e return option (hlist (typD ts nil) var_env -> typD ts nil t) with
      | Const t' c => 
        match typ_eq_odec t' t with
          | Some pf => 
            Some (fun _ => match pf in _ = t return typD ts nil t with 
                             | refl_equal => c
                           end)
          | None => None
        end
      | Var x => 
        match nth_error var_env x as z return nth_error var_env x = z -> _ with
          | None => fun _ => None
          | Some t' => fun pf => 
            match typ_eq_odec t' t with
              | Some pf' => 
                Some (fun e => match pf' in _ = t return typD ts nil t with 
                                 | eq_refl => match eq_sym pf in _ = t''
                                                return match t'' with 
                                                         | Some t => typD ts nil t
                                                         | None => unit
                                                       end -> typD ts nil t' with
                                                | eq_refl => fun x => x
                                              end (hlist_nth e x)
                               end)
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
            match type_apply _ _ ts' _ _ (fdenote f) with
              | None => None
              | Some t' => 
                match typ_eq_odec (instantiate_typ (rev ts') (ftype f)) t with
                  | Some pf =>
                    Some (fun _ => match pf in _ = t' return typD ts nil t' with
                                     | eq_refl => t'
                                   end)
                  | None => None
                end
            end
        end
      | Abs t' e =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t) with
          | tvArr lt rt =>
            match @exprD' (lt :: var_env) e rt with
              | None => None
              | Some a => Some (fun x y => a (Hcons y x))
            end
          | _ => None
        end
      | App f xs => 
        match typeof var_env f with
          | None => None
          | Some tf =>
            match exprD' var_env f tf with
              | None => None
              | Some f =>
                (fix eval_args (t' : typ) (xs : list expr) {struct xs} : 
                  (hlist (typD ts nil) var_env -> typD ts nil t') ->
                  option (hlist (typD ts nil) var_env -> typD ts nil t) :=
                  match xs with
                    | nil => match typ_eq_odec t' t with
                               | None => fun _ => None
                               | Some pf => fun f =>
                                 Some match pf in _ = t' return _ with
                                        | eq_refl => f
                                      end
                             end
                    | x :: xs => 
                      match t' as t' 
                        return (hlist (typD ts nil) var_env -> typD ts nil t') ->
                        option (hlist (typD ts nil) var_env -> typD ts nil t)
                        with
                        | tvArr tl tr => fun f =>
                          match exprD' var_env x tl with
                            | None => None
                            | Some xv => eval_args tr xs (fun e => f e (xv e))
                          end
                        | _ => fun _ => None
                      end                
                  end) tf xs f
            end
        end
      | Equal t' e1 e2 =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t) with
          | tvProp =>
            match exprD' var_env e1 t' , exprD' var_env e2 t' with
              | Some l , Some r => Some (fun g => equiv _ t' (l g) (r g))
              | _ , _ => None
            end
          | _ => None
        end            
      | Not e =>
        match t as t return option (hlist (typD ts nil) var_env -> typD ts nil t) with
          | tvProp =>
            match exprD' var_env e tvProp with
              | Some e => Some (fun g => ~(e g))
              | None => None
            end
          | _ => None
        end
    end.

  Fixpoint split_env (g : env) : { ls : tenv & hlist (typD ts nil) ls } :=
    match g as g return { ls : tenv & hlist (typD ts nil) ls } with
      | nil => existT _ nil Hnil
      | existT t v :: gs =>
        match split_env gs with
          | existT a b =>
            existT _ (t :: a) (Hcons v b)
        end
    end.

  Definition exprD (var_env : env) (e : expr) (t : typ) : option (typD ts nil t) :=
    let (ts,vs) := split_env var_env in
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

  Fixpoint expr_seq_dec (e1 e2 : expr) : bool.
  refine (
    match e1 , e2 with
      | Const t1 v1 , Const t2 v2 =>
        match const_seqb _ _ _ _ v1 v2 with
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
                if typ_eqb t1 t2 then check ts1 ts2 else false
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
        if typ_eqb t1 t2 then expr_seq_dec e1 e2
        else false
      | Equal t1 e1 e2 , Equal t1' e1' e2' =>
        if typ_eqb t1 t1' then 
          if expr_seq_dec e1 e1' then 
            if expr_seq_dec e2 e2' then true
            else false
          else false
        else false
      | Not e1 , Not e2 => expr_seq_dec e1 e2
      | _ , _ => false
    end).
  Defined.

  Theorem const_seqb_ok : forall ts ts' t1 t2 a b,
    match const_seqb ts ts' t1 t2 a b with
      | None => True
      | Some true => exists pf : t2 = t1, a = match pf in _ = t return typD ts ts' t with
                                                 | eq_refl => b
                                               end
      | Some false => t1 <> t2 \/ 
        exists pf : t2 = t1, a <> match pf in _ = t return typD ts ts' t with
                                    | eq_refl => b
                                  end
    end.
  Proof.
    destruct t1; destruct t2; simpl; auto; intros.
    consider (nat_eq_odec n n0); intros; subst.
    { clear H.
      match goal with
        | |- match ?X with _ => _ end =>
          consider X
      end; intros; auto.
      destruct b0. 
      cut (a = b). 
      { clear. intros; subst. exists eq_refl. auto. }
      { generalize dependent (nth_error ts0 n0). destruct e; intros.
        generalize (Eqb_correct t a b). rewrite H; auto.
        destruct b. }
      { right. exists eq_refl.
        generalize dependent (nth_error ts0 n0). destruct e; intros.
        generalize (Eqb_correct t a b). rewrite H; auto.
        destruct b. } }
    { apply nat_eq_odec_None in H. left. congruence. }
  Qed.

  Theorem expr_seq_dec_eq : forall e1 e2, 
    expr_seq_dec e1 e2 = true -> e1 = e2.
  Proof.
    induction e1; destruct e2; simpl; intros; try congruence.
    { generalize (const_seqb_ok ts nil t t0 v t1). 
      destruct (const_seqb ts nil t t0 v t1); subst; auto.
      destruct 1; subst; auto.
      congruence. }
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

End env.

Arguments Func {_} _ _.
Arguments Const {_} _ _.
Arguments UVar {_} _.
Arguments Var {_} _.
Arguments Abs {_} _ _.
Arguments App {_} _ _.

Export Types.
