Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section symbols_prod.
  Context {A B typ : Type}.
  Context {RType_typ : RType typ}.
  Context {RSymA : RSym A} {RSymB : RSym B}.
  Context {RSymAOk : RSymOk RSymA} {RSymBOk : RSymOk RSymB}.

  Context {Typ2_Prod : Typ2 RType_typ prod}.

  Let tyProd := @typ2 _ _ _ _.

  Definition typeof_prod (p : A * B) := 
      match typeof_sym (fst p), typeof_sym (snd p) with
      | Some t, Some u => Some (tyProd t u)
      | _, _ => None
      end.

  Definition prodD (p : A * B) : match typeof_prod p with
                                 | Some t => typD t
                                 | None => unit : Type
                                 end. 
  Proof.
    refine (
        let (a, b) as q return match typeof_prod q with
                               | Some t => typD t
                               | None => unit : Type
                               end := p in
          (match typeof_sym a as x return 
                match x with
                | Some t => typD t
                | None => unit
                end ->
                match typeof_sym b with
                | Some t => typD t
                | None => unit
                end ->
                match
                  match x with
                  | Some t =>
                    match typeof_sym b with
                    | Some u => Some (tyProd t u)
                    | None => None
                    end
                  | None => None
                  end
                with
                | Some t => typD t
                | None => unit
                end with
          | Some t => 
            fun c d =>
            match typeof_sym b as x return
                  match x with
                  | Some t => typD t
                  | None => unit
                  end ->
                  match
                    match x with
                    | Some u => Some (tyProd t u)
                    | None => None
                    end
                  with
                  | Some t => typD t
                  | None => unit
                  end
            with
            | Some u => fun d => eq_rect_r (fun T : Type => T) (c, d) (typ2_cast t u)
            | None => fun _ => tt
            end d
          | None => fun _ _ => tt
          end) (symD a) (symD b)).
  Defined.

  Global Instance RSymProd : RSym (A * B) := {
    typeof_sym := typeof_prod;
    symD := prodD;                           
    sym_eqb p q :=
      match sym_eqb (fst p) (fst q), sym_eqb (snd p) (snd q) with
      | Some b1, Some b2 => Some (andb b1 b2)
      | _, _ => None
      end
  }.

  Global Instance RSymProdOk : RSymOk RSymProd.
  Proof.
    constructor.
    intros p q; destruct p, q; simpl.
    remember (sym_eqb a a0) as o1.
    remember (sym_eqb b b0) as o2.
    destruct o1, o2; try apply I.
    specialize (sym_eqbOk (RSymOk := RSymAOk) a a0);
    specialize (sym_eqbOk (RSymOk := RSymBOk) b b0); intros.
    rewrite <- Heqo1 in H0; rewrite <- Heqo2 in H.
    destruct b1, b2; simpl; subst; congruence.
  Qed.

End symbols_prod.