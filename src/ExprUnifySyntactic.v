Require Import List.
Require Import Expr.
Require Import ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable ts : types.
  
  Definition exprUnify : unifier ts.
  red.
  refine (fun Subst Subst_Subst Prover Facts =>
    (** TODO: Use the prover in places where I return [None] **)
    (fix exprUnify (n : nat) : Subst -> expr ts -> expr ts -> option Subst :=
      match n with 
        | 0 => fun _ _ _ => None
        | S n =>
          (fix unify s (e1 e2 : expr ts) {struct e1} : option Subst :=
            match e1 , e2 with
              | Const t1 v1 , Const t2 v2 =>
                match const_seqb ts _ t1 t2 v1 v2 with
                  | Some true => Some s
                  | _ => None
                end
              | UVar u1 , UVar u2 => 
                if EqNat.beq_nat u1 u2 then Some s
                else
                  match Subst.set _ _ u1 (UVar u2) s with
                    | None => Subst.set _ _ u2 (UVar u1) s
                    | x => x
                  end
              | UVar u1 , _ => 
                match Subst.lookup _ _ u1 s with
                  | None => Subst.set _ _ u1 e2 s
                  | Some e1' => exprUnify n s e1' e2
                end
              | _ , UVar u2 => 
                match Subst.lookup _ _ u2 s with
                  | None => Subst.set _ _ u2 e1 s
                  | Some e2' => exprUnify n s e1 e2'
                end
              | Var v1 , Var v2 =>
                if EqNat.beq_nat v1 v2 then Some s else None
              | Func f1 ts1 , Func f2 fs2 =>
                if EqNat.beq_nat f1 f2 then Some s else None
              | App e1 es1 , App e2 es2 =>
                match unify s e1 e2 with
                  | None => None
                  | Some s' =>
                    (fix unifyArgs (s : Subst) (es1 es2 : exprs ts) {struct es1} : option Subst :=
                      match es1 , es2 with
                        | nil , nil => Some s
                        | e1 :: es1 , e2 :: es2 =>
                          match unify s e1 e2 with
                            | None => None
                            | Some s' => unifyArgs s' es1 es2
                          end
                        | _ , _ => None
                      end) s es1 es2
                end
              | Abs t1 e1 , Abs t2 e2 =>
                (* t1 = t2 since both terms have the same type *)
                (** TODO: I have to handle the change in binding structure.
                 ** For example,
                 ** (fun x => x) ~ (fun x => ?1) doesn't work
                 ** because the ?1 isn't going to have x in scope
                 **)
                unify s e1 e2
              | _ , _ => None 
            end)
      end) 10).
  Defined.

End typed.