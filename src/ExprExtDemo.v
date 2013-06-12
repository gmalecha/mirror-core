Require Import List Bool.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Vector.
Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.Iso.
Require Import MirrorCore.IsoTac.
Require Import MirrorCore.TypesExt.
Require Import MirrorCore.ExprExt.

Set Implicit Arguments.
Set Strict Implicit.

(** AXIOMS **)
Require Import FunctionalExtensionality.

Section Demo.

  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Context {RType_typ : RType typD}.
  Context {RTypeOk_typ : RTypeOk RType_typ}.
  Context {typ_arr : TypInstance2 typD Fun}.
  Context {typ_m : TypInstance1 typD m}.
  Context {typ_nat : TypInstance0 typD nat}.
  Let tvNat := @typ0 _ typD _ typ_nat.
  Let nat_match := @typ0_match _ typD _ typ_nat.
  Let nat_into (F : Type -> Type) ts : F nat -> F (typD ts tvNat) :=
    sinto (iso := @typ0_iso _ _ _ typ_nat ts) F.
  Let tvArr := @typ2 _ typD _ typ_arr.
  Let arr_match := @typ2_match _ typD _ typ_arr.
  Let arr_into (F : Type -> Type) ts a b : F (typD ts a -> typD ts b) -> F (typD ts (tvArr a b)) :=
    sinto (iso := @typ2_iso _ _ _ typ_arr ts a b) F.
  Let arr_outof (F : Type -> Type) ts a b : F (typD ts (tvArr a b)) -> F (typD ts a -> typD ts b) :=
    soutof (iso := @typ2_iso _ _ _ typ_arr ts a b) F.
  Let tvM := @typ1 _ typD _ typ_m.
  Let m_match := @typ1_match _ typD _ typ_m.
  Let m_into (F : Type -> Type) ts a : F (m (typD ts a)) -> F (typD ts (tvM a)) :=
    sinto (iso := @typ1_iso _ _ _ typ_m ts a) F.
  Let m_outof (F : Type -> Type) ts a : F (typD ts (tvM a)) -> F (m (typD ts a)) :=
    soutof (iso := @typ1_iso _ _ _ typ_m ts a) F.

  Inductive mexpr : Type :=
  | Bind : typ -> typ -> mexpr -> mexpr -> mexpr
  | Ret  : typ -> mexpr -> mexpr
  | Plus : mexpr -> mexpr -> mexpr
  | Const : nat -> mexpr
  | Var : nat -> mexpr
  | Abs : typ -> mexpr -> mexpr
  | App : typ -> mexpr -> mexpr -> mexpr.

  Fixpoint liftBy (skip : nat) (e : mexpr) (l : nat) : mexpr :=
    match e with
      | Bind t1 t2 m1 m2 => Bind t1 t2 (liftBy skip m1 l) (liftBy skip m2 l) 
      | Ret t1 m1 => Ret t1 (liftBy skip m1 l)
      | Plus lhs rhs => Plus (liftBy skip lhs l) (liftBy skip rhs l)
      | Const v => Const v
      | Var v => 
        match Compare_dec.nat_compare v skip with
          | Eq 
          | Lt => Var v
          | Gt => Var (v - l)
        end
      | Abs t m => Abs t (liftBy (S skip) m l)
      | App t f x => App t (liftBy skip f l) (liftBy skip x l)
    end.

  Fixpoint subst (skip : nat) (e : mexpr) (w : mexpr) : mexpr :=
    match e with
      | Bind t1 t2 m1 m2 => Bind t1 t2 (subst skip m1 w) (subst skip m2 w)
      | Ret t1 m1 => Ret t1 (subst skip m1 w)
      | Plus l r => Plus (subst skip l w) (subst skip r w)
      | Const n => Const n
      | Var n => 
        if EqNat.beq_nat n skip then liftBy 0 w skip else Var (n - 1)          
      | Abs t m => Abs t (subst (S skip) m w)
      | App t l r => App t (subst skip l w) (subst skip r w)
    end.

  Fixpoint mexprD (g : list typ) (e : mexpr) (t : typ) {struct e} : option (hlist (typD nil) g -> typD nil t).
  refine (
      match e with
        | Var v =>
          match nth_error g v as nt 
                return (hlist (typD nil) g -> match nt with
                                                | None => unit
                                                | Some t => typD nil t
                                              end)
                    -> option (hlist (typD nil) g -> typD nil t)
          with
            | None => fun _ => None
            | Some t' => match typ_cast (fun x => x) nil t' t with
                           | None => fun _ => None
                           | Some cast => fun get => Some (fun g => cast (get g))
                         end
          end (fun g => hlist_nth g v)
        | Abs t' body =>
          arr_match nil (fun ty Ty => option (hlist (typD nil) g -> Ty))
             (fun d r => 
                match typ_cast (typD := typD) (fun x => x) nil t' d with 
                  | None => None
                  | Some cast_d => 
                    match mexprD (d :: g) body r with
                      | None => None
                      | Some f => Some (fun g x => f (Hcons x g))
                    end                        
                end)
             (fun _ => None)
             t
        | App t' m m' =>
          match mexprD g m (tvArr t' t) , mexprD g m' t' with
            | Some v , Some v' => Some (fun g => 
                                          let f := v g in
                                          let x := v' g in
                                          arr_outof (fun x => x) nil _ _ f x)
            | _ , _ => None
          end
        | Const n =>
          nat_match nil (fun ty Ty => option (hlist (typD nil) g -> Ty))
             (fun _ => Some (fun _ => n))
             (fun _ => None)
             t
        | Plus l r =>
          nat_match nil (fun ty Ty => option (hlist (typD nil) g -> Ty) ->
                                      option (hlist (typD nil) g -> Ty) ->
                                      option (hlist (typD nil) g -> Ty))
             (fun _ l r => 
                match l , r with
                  | Some l , Some r => 
                    Some (fun g => l g + r g)
                  | _ , _ => None
                end)
             (fun _ _ _ => None)
             t (mexprD g l t) (mexprD g r t)
        | Ret t' e =>
          m_match nil (fun ty Ty => option (hlist (typD nil) g -> Ty))
            (fun t'' => 
               match typ_cast (fun x => x) nil t' t'' with
                 | None => None
                 | Some cast => 
                   match mexprD g e t' with 
                     | None => None
                     | Some r => Some (fun g => ret (cast (r g)))
                   end
               end)
            (fun _ => None)
            t
        | Bind t' t'' c k => 
          m_match nil (fun ty Ty => option (hlist (typD nil) g -> Ty))
            (fun t''' =>
               match typ_cast (typD := typD) (fun x => typD nil t' -> m x) nil t'' t''' with
                 | None => None
                 | Some cast =>
                   match mexprD g c (tvM t') , mexprD g k (tvArr t' (tvM t'')) with
                     | Some cv , Some kv => Some (fun g => bind _ _)
                     | _ , _ => None
                   end
               end)
            (fun _ => None)
            t
      end).
  (** TODO: Coq doesn't type check when this is inline **)
  eapply m_outof. eapply cv. eapply g0.
  eapply cast. eapply m_outof. eapply arr_outof. eapply kv. eapply g0.
  Defined.

  Definition mexpr_dec (a b : mexpr) : {a = b} + {a <> b}.
    assert (forall a b : typ, {a = b} + {a <> b}).
    { intros. generalize (typ_eqb_ok a0 b0). 
      destruct (typ_eqb a0 b0). left. apply H. reflexivity.
      right. intro. apply H in H0. congruence. }
    decide equality.
    decide equality.
    decide equality.
  Defined.

  Definition mexpr_eq (a b : mexpr) : option bool :=
    match mexpr_dec a b with
      | left _ => Some true
      | right _ => Some false
    end.    

  Instance Expr_mexpr : Expr typD mexpr :=
  { exprD := fun _ g e t => 
               match Generic.split g with
                 | existT te env =>
                   match mexprD te e t with
                     | None => None
                     | Some f => Some (f env)
                   end
               end
  ; expr_eq := mexpr_eq
  }.

  Context {TypInstance0Ok_nat : TypInstance0_Ok typ_nat}.
  Context {TypInstance1Ok_m : TypInstance1_Ok typ_m}.
  Context {TypInstance2Ok_arr : TypInstance2_Ok typ_arr}.

  Ltac solver :=
        eauto with typeclass_instances ; 
        try eapply (@typ2_isoOk _ _ _ _ TypInstance2Ok_arr) ;
        try eapply (@typ1_isoOk _ _ _ _ TypInstance1Ok_m) ;
        try eapply (@typ0_isoOk _ _ _ _ TypInstance0Ok_nat) ;
        idtac.
  Theorem soutof_red : forall A B i o F,
                         @soutof A B {| siso := fun x => {| into := i x ; outof := o x |} |} F = 
                         o F.
    reflexivity.
  Qed.
  Theorem sinto_red : forall A B i o F,
                         @sinto A B {| siso := fun x => {| into := i x ; outof := o x |} |} F = 
                         i F.
    reflexivity.
  Qed.

  Ltac using_s :=
    match goal with
      | |- appcontext [ @into ?A ?B (@siso ?C ?D ?E ?F) ] =>
        change (@into A B (@siso C D E F))
          with (@sinto _ _ E F)
      | |- appcontext [ @outof ?A ?B (@siso ?C ?D ?E ?F) ] =>
        change (@outof A B (@siso C D E F))
          with (@soutof _ _ E F)
    end.

  Theorem P_iff : forall T P (x y : T), x = y -> (P x <-> P y).
  Proof.
    clear; intros; subst; firstorder.
  Qed.

  Ltac unfold_all := 
    subst tvNat nat_match nat_into  
          tvArr  arr_match  arr_into  arr_outof 
          tvM  m_match  m_into  m_outof; simpl in *.

    
  Ltac go :=
    repeat (   (rewrite soutof_red)
            || (rewrite sinto_red)
            || (erewrite soutof_sinto by solver) 
            || (erewrite sinto_soutof by solver) 
            || (erewrite sinto_option by solver)
            || (erewrite soutof_option by solver)
            || (erewrite into_outof by solver)
            || (erewrite outof_into by solver)
            || (erewrite soutof_const by solver)
            || (erewrite sinto_const by solver)
            || (erewrite soutof_app' by solver)
            || (erewrite sinto_app' by solver)
            || (erewrite soutof_app'' by solver)
            || (erewrite sinto_app'' by solver)
            || (erewrite soutof_app by solver)
            || (erewrite sinto_app by solver)
            || (erewrite typ0_match_typ0 by solver)
            || (erewrite typ1_match_typ1 by solver)
            || (erewrite typ2_match_typ2 by solver)
            || match goal with
                 | |- context [ @typ_cast _ _ ?CLS ?F ?TS ?X ?X ] => 
                   let H := fresh in
                   let H' := fresh in
                   destruct (@typ_cast_refl _ _ CLS _ TS X  F) as [ ? [ H H' ] ] ; 
                 eauto with typeclass_instances ;
                 rewrite H
               end
            || using_s).

  Instance FuncInstance0_plus : FuncInstance0 typD mexpr plus :=
  { typ0_witness := TypInstance0_app2 typ_arr _ (TypInstance0_app2 typ_arr _ _)
  ; ctor0 := Abs tvNat (Abs tvNat (Plus (Var 1) (Var 0)))
  ; ctor0_match := fun R caseCtor caseElse e =>
                     match e as e return R e with
                       | Abs t (Abs t' (Plus (Var 1) (Var 0))) =>
                         nat_match nil 
                                   (fun ty Ty => R (Abs ty (Abs t' (Plus (Var 1) (Var 0))))) 
                                   (fun _ => nat_match nil 
                                                       (fun ty Ty => R (Abs tvNat (Abs ty (Plus (Var 1) (Var 0))))) 
                                                       caseCtor
                                                       (fun _ => caseElse _)
                                                       t')
                                   (fun _ => caseElse _)
                                   t
                       | e => caseElse e
                     end
  }.
  
  Instance FuncInstance0Ok_plus : FuncInstance0Ok FuncInstance0_plus.
  Proof.
    constructor.
    { simpl; intros.
      destruct (Generic.split vs).
      unfold Fun.
      unfold_all.
      go.
      eapply P_iff.
      apply functional_extensionality; intro; 
      apply functional_extensionality; intro.
      go.
      repeat rewrite H2.
      simpl. go. reflexivity. }
    { simpl; intros.
      unfold_all. unfold Fun.
      go. reflexivity. }
  Qed.

  Require Import ExtLib.Data.Fin.

  Definition SApp_plus : @SymAppN typ mexpr 0 ((fun _ => tvNat) :: (fun _ => tvNat) :: nil) tvNat :=
    @mkSymAppN _ _ 0 ((fun _ => tvNat) :: (fun _ => tvNat) :: nil) tvNat
              (fun _ a => Plus (vector_hd a) (vector_hd (vector_tl a)))
              (fun e => 
                 match e with
                   | Plus l r => Some (Vnil _, Vcons l (Vcons r (Vnil _)))
                   | _ => None
                 end).

  Definition SApp_ret1 : @SymAppN typ mexpr 1 (vector_hd :: nil) tvM.
  refine (
      @mkSymAppN _ _ 1 (vector_hd :: nil) tvM
                (fun ts v => Ret (vector_hd ts) (vector_hd v))
                (fun e => match e with
                            | Ret t' v => 
                              Some (Vcons t' (Vnil _), Vcons v (Vnil _))
                            | _ => None
                          end)).
  Defined.


  Definition SApp_ret0 T (ti : TypInstance0 typD T) : @SymAppN typ mexpr 0 ((fun _ => @typ0 _ _ _ ti) :: nil) (tvM (@typ0 _ _ _ ti)).
  refine (
      let t := @typ0 _ _ _ ti in
      @mkSymAppN _ _ 0 ((fun _ => t) :: nil) (tvM t)
                (fun _ v => Ret t (vector_hd v))
                (fun e => match e with
                            | Ret t' v => 
                              @typ0_match _ _ _ ti nil (fun _ _ => option (vector typ 0 * vector mexpr 1)) 
                                          (fun _ => Some (Vnil _, Vcons v (Vnil _)))
                                          (fun _ => None)
                                          t'
                            | _ => None
                          end)).
  Defined.

  Definition SApp_bind2 
  : @SymAppN typ mexpr 2 ((fun x => tvM (vector_hd x)) :: (fun x => tvArr (vector_hd x) (tvM (vector_hd (vector_tl x)))):: nil) (fun _ => tvM).
  refine (
      @mkSymAppN typ mexpr 2 ((fun x => tvM (vector_hd x)) :: (fun x => tvArr (vector_hd x) (tvM (vector_hd (vector_tl x)))):: nil) (fun _ => tvM)
                 (fun ts v => Bind (vector_hd ts) (vector_hd (vector_tl ts)) (vector_hd v) (vector_hd (vector_tl v)))
                 (fun e => match e with
                            | Bind t1' t2' v v' => 
                              Some (Vcons t1' (Vcons t2' (Vnil _)), Vcons v (Vcons v' (Vnil _)))
                            | _ => None
                          end)).
  Defined.


  Definition SApp_bind0 T1 T2 (ti1 : TypInstance0 typD T1) (ti2 : TypInstance0 typD T2) 
  : @SymAppN typ mexpr 0 ((fun _ => tvM (@typ0 _ _ _ ti1)) :: (fun _ => tvArr (@typ0 _ _ _ ti1) (tvM (@typ0 _ _ _ ti2))) :: nil) (tvM (@typ0 _ _ _ ti2)).
  refine (
      let t1 := @typ0 _ _ _ ti1 in
      let t2 := @typ0 _ _ _ ti2 in
      @mkSymAppN _ _ 0 ((fun _ => tvM t1) :: (fun _ => tvArr t1 (tvM t2)) :: nil) (tvM t2)
                (fun _ v => Bind t1 t2 (vector_hd v) (vector_hd (vector_tl v)))
                (fun e => match e with
                            | Bind t1' t2' v v' => 
                              @typ0_match _ _ _ ti1 nil (fun _ _ => option (vector typ 0 * vector mexpr 2))
                                          (fun _ =>
                                             @typ0_match _ _ _ ti2 nil (fun _ _ => option (vector typ 0 * vector mexpr 2))
                                                         (fun _ => Some (Vnil _, Vcons v (Vcons v' (Vnil _))))
                                                         (fun _ => None)
                                                         t2')
                                          (fun _ => None)
                                          t1'
                            | _ => None
                          end)).
  Defined.

  Definition gen_app (d r : typ) : AppInstance typD mexpr (tvArr d r) d r.
  refine ( 
    let iso ts := Iso_flip (@siso _ _ (@typ2_iso _ _ _ typ_arr ts d r) (fun x => x)) in
    {| fun_iso := iso
     ; sapp := fun ts l r => (into (iso := iso ts) l) r
     ; app1 := fun f x => App d f x
     ; app1_check := fun e => match e with
                                | App _ f x => Some (f,x)
                                | _ => None
                              end
    |}).
  Defined.





  Definition Lambda_abs : Lambda typ mexpr.
  refine 
    {| lambda := Abs
     ; lambda_check := fun e =>
                         match e with
                           | Abs t e => Some (t,e)
                           | _ => None
                         end
     ; subst0 := subst 0
     |}.
  Defined.

End Demo.
