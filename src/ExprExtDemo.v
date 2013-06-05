Require Import List Bool.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.TypesExt.
Require Import MirrorCore.ExprExt.

Set Implicit Arguments.
Set Strict Implicit.

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
    into (Iso := @typ0_iso _ _ _ typ_nat F ts).
  Let tvArr := @typ2 _ typD _ typ_arr.
  Let arr_match := @typ2_match _ typD _ typ_arr.
  Let arr_into (F : Type -> Type) ts a b : F (typD ts a -> typD ts b) -> F (typD ts (tvArr a b)) :=
    into (Iso := @typ2_iso _ _ _ typ_arr F ts a b).
  Let arr_outof (F : Type -> Type) ts a b : F (typD ts (tvArr a b)) -> F (typD ts a -> typD ts b) :=
    outof (Iso := @typ2_iso _ _ _ typ_arr F ts a b).
  Let tvM := @typ1 _ typD _ typ_m.
  Let m_match := @typ1_match _ typD _ typ_m.
  Let m_into (F : Type -> Type) ts a : F (m (typD ts a)) -> F (typD ts (tvM a)) :=
    into (Iso := @typ1_iso _ _ _ typ_m F ts a).
  Let m_outof (F : Type -> Type) ts a : F (typD ts (tvM a)) -> F (m (typD ts a)) :=
    outof (Iso := @typ1_iso _ _ _ typ_m F ts a).

  Inductive mexpr : Type :=
  | Bind : typ -> typ -> mexpr -> mexpr -> mexpr
  | Ret  : typ -> mexpr -> mexpr
  | Plus : mexpr -> mexpr -> mexpr
  | Const : nat -> mexpr
  | Var : nat -> mexpr
  | Abs : typ -> mexpr -> mexpr.

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
    { admit. }
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

  Instance FuncInstance0_plus : FuncInstance0 plus :=
  { typ0_witness := TypInstance0_app2 typ_arr _ (TypInstance0_app2 typ_arr _ _)
  ; ctor0 := Abs tvNat (Abs tvNat (Plus (Var 1) (Var 0)))
  }.
  simpl.