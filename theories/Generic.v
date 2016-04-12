Require Import Coq.Lists.List.
Require Import ExtLib.Data.Vector.

Set Implicit Arguments.
Set Strict Implicit.

Section quant.
  Variable T : Type.

  Fixpoint quant (n : nat) : Type :=
    match n with
      | 0 => T
      | S n => T -> quant n
    end.

  Fixpoint qapply (n : nat) (ls : list T) : quant n -> option T :=
    match n as n , ls return quant n -> option T with
      | 0 , nil => fun t => Some t
      | S n , l :: ls => fun f => @qapply n ls (f l)
      | _ , _ => fun _ => None
    end.

  Fixpoint qapply_v (n : nat) : vector T n -> quant n -> T :=
    match n as n return vector T n -> quant n -> T with
      | 0 => fun _ x => x
      | S n => fun args x => qapply_v (vector_tl args) (x (vector_hd args))
    end.

  Fixpoint parametric (n : nat) (k : list T -> Type) : Type :=
    match n with
      | 0 => k nil
      | S n => forall T : T, parametric n (fun acc => k (T :: acc))
    end.

  Fixpoint papply (n : nat) (k : list T -> Type) (ls : list T)
  : parametric n k -> option (k ls) :=
    match n as n return parametric n k -> option (k ls) with
      | 0 =>
        match ls as ls return parametric 0 k -> option (k ls) with
          | nil => Some
          | _ :: _ => fun _ => None
        end
      | S n' =>
        match ls as ls return parametric (S n') k -> option (k ls) with
          | nil => fun _ => None
          | t :: ts => fun x => papply n' (fun acc => k (t :: acc)) ts (x t)
        end
    end.

End quant.

Section paraquant.
  Variable T : Type.
  Variable K : T -> Type.
  Fixpoint paraquant (n : nat) : quant T n -> Type :=
    match n as n return quant T n -> Type with
      | 0 => fun x => K x
      | S n => fun x => forall y, paraquant n (x y)
    end.

  Fixpoint paraquant_apply (n : nat) (ls : list T) {struct n}
  : forall q (f : paraquant n q), match qapply _ ls q with
                                    | None => unit:Type
                                    | Some x => K x
                                  end :=
    match n as n
        , ls as ls
          return forall q : quant T n,
                   paraquant n q ->
                   match qapply n ls q with
                     | Some x => K x
                     | None => unit
                   end
    with
      | 0 , nil => fun _ x => x
      | S _ , nil => fun _ _ => tt
      | 0 , _ :: _ => fun _ _ => tt
      | S n , l :: ls => fun q P => paraquant_apply n ls _ (P l)
    end.

End paraquant.
