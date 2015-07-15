Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.

Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section symbols_sum.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable func1 func2 : Type.

  Variable RSym_func1 : RSym func1.
  Variable RSym_func2 : RSym func2.

  Instance RSym_sum : RSym (func1 + func2) :=
  { typeof_sym := fun f => match f with
                             | inl f => typeof_sym f
                             | inr f => typeof_sym f
                           end
  ; symD := fun f => match f as f
                              return match match f with
                                             | inl f => typeof_sym f
                                             | inr f => typeof_sym f
                                           end with
                                       | None => unit
                                       | Some t => typD t
                                     end
                        with
                          | inl f => symD f
                          | inr f => symD f
                        end
  ; sym_eqb := fun x y =>
                 match x , y with
                   | inl x , inl y => sym_eqb x y
                   | inr x , inr y => sym_eqb x y
                   | _ , _ => Some false
                 end
  }.

  Hypothesis RSymOk_func1 : RSymOk RSym_func1.
  Hypothesis RSymOk_func2 : RSymOk RSym_func2.

  Instance RSymOk_sum : RSymOk RSym_sum.
  Proof.
    constructor.
    intros.
    destruct a; destruct b; simpl; try congruence.
    { generalize (sym_eqbOk f f0).
      destruct (sym_eqb f f0); auto.
      destruct b; congruence. }
    { generalize (sym_eqbOk f f0).
      destruct (sym_eqb f f0); auto.
      destruct b; congruence. }
  Qed.
End symbols_sum.

Section RSym_OneOf.
  Context {typ : Type} {RType_typ : RType typ}.



  Instance RSym_Empty_set : RSym (Empty_set) := {
    typeof_sym s := None;
    symD := fun f => match f return unit with end;
    sym_eqb := fun f _ => match f return option bool with end
  }.

  Definition typeof_sym_OneOf {m : pmap Type}
    (H : forall p, RSym (match pmap_lookup' m p with | Some T => T | None => Empty_set end))
    (s : OneOf m) : option typ :=
    match s with
      | Build_OneOf _ x v =>
        match pmap_lookup' m x as o return o = pmap_lookup' m x -> option typ with
          | Some T => 
            fun pf =>
              let RSym_p := 
                  eq_rect_r (fun o => RSym (match o with 
                                              | Some T => T 
                                              | None => Empty_set 
                                            end)) (H x) pf in 
              let v' :=
                  eq_rect_r (fun o => match o with 
                                        | Some T => T 
                                        | None => Empty_set 
                                      end) v pf in 
              typeof_sym (RSym := RSym_p) v'
          | None => fun _ => None
        end eq_refl
    end.
  

  Definition symD_OneOf (m : pmap Type) 
    (H : forall p, RSym (match pmap_lookup' m p with | Some T => T | None => Empty_set end))
    (f : OneOf m) : match typeof_sym_OneOf H f with
                      | Some t => typD t
                      | None => unit:Type
                    end.
 refine (
    match f as f' return f = f' -> 
                         match typeof_sym_OneOf H f' with
                           | Some t => typD t
                           | None => unit:Type
                         end with
      | Build_OneOf _ x v => 
        fun eqf => 
          match pmap_lookup' m x as o 
                return o = pmap_lookup' m x -> 
                       match typeof_sym_OneOf H {| SumN.index := x; value := v |} with
                         | Some t => typD t
                         | None => unit:Type
                       end with
            | Some T => 
              fun pf =>
                let RSym_p := 
                    eq_rect_r (fun o => RSym (match o with 
                                                | Some T => T 
                                                | None => Empty_set 
                                              end)) (H x) pf in 
                let v' :=
                    eq_rect_r (fun o => match o with 
                                          | Some T => T 
                                          | None => Empty_set 
                                        end) v pf in 
              let v'' := symD (RSym := RSym_p) v' in _ 
            | None =>
              fun pf => 
                let RSym_p := 
                    eq_rect_r (fun o => RSym (match o with 
                                                | Some T => T 
                                                | None => Empty_set 
                                              end)) (H x) pf in 
                let v' :=
                    eq_rect_r (fun o => match o with 
                                          | Some T => T 
                                          | None => Empty_set 
                                        end) v pf in _
          end eq_refl
    end eq_refl).
simpl.
generalize dependent (H x).
clear H.
clear eqf.
revert v v'.
rewrite <- pf.
intros.
apply v''.

intros; simpl.
generalize dependent (H x).
clear H eqf.
revert v v'.
rewrite <- pf.
intros.
apply tt.

Defined.

  Definition sym_eqb_OneOf
    (m : pmap Type) 
    (H : forall p, RSym (match pmap_lookup' m p with | Some T => T | None => Empty_set end))
    (f1 f2 : OneOf m) : option bool :=
    match f1, f2 with
      | Build_OneOf _ x1 v1, Build_OneOf _ x2 v2 =>
        match Pos.eq_dec x1 x2 with
          | left eqx =>
            match pmap_lookup' m x1 as o return o = pmap_lookup' m x1 -> option bool with
              | Some _ => 
                fun eqo =>
                  let v1' := eq_rect_r (fun o => match o with 
                                                   | Some T => T 
                                                   | None => Empty_set 
                                                 end) v1 eqo in
                  let v2' := eq_rect_r (fun x => match pmap_lookup' m x with 
                                                   | Some T => T 
                                                   | None => Empty_set 
                                                 end) v2 eqx in 
                  let v2' := eq_rect_r (fun o => match o with 
                                                   | Some T => T 
                                                   | None => Empty_set 
                                                 end) v2' eqo in
                  let RSym_x := eq_rect_r (fun o => RSym (match o with 
                                                            | Some T => T 
                                                            | None => Empty_set 
                                                          end)) (H x1) eqo in 
                  @sym_eqb typ RType_typ _ RSym_x v1' v2'
              | None => fun _ => None
            end eq_refl
          | right _ => None
        end
    end.

  Instance RSymOneOf (m : pmap Type) 
    (H : forall p, RSym (match pmap_lookup' m p with | Some T => T | None => Empty_set end)) :
    RSym (OneOf m) := 
    {
      typeof_sym s := typeof_sym_OneOf H s;
      symD f := symD_OneOf H f;
      sym_eqb f1 f2 := sym_eqb_OneOf H f1 f2
    }.


  Instance RSym_Empty : RSym (OneOf Empty) := {
    typeof_sym s := None;
    symD := fun f => match OneOf_Empty f return unit with end;
    sym_eqb := fun f _ => match OneOf_Empty f return option bool with end
  }.

Instance RSymOk_OneOf (m : pmap Type) 
  (H1 : forall p, RSym (match pmap_lookup' m p with | Some T => T | None => Empty_set end)) 
  (H2 : forall p, RSymOk (H1 p)) :
  RSymOk (RSymOneOf m H1) := {
    sym_eqbOk f1 f2 :=
        match f1 as f1' return f1 = f1' -> 
                               match sym_eqb f1 f2 with
                                 | Some true => f1 = f2
                                 | Some false => f1 <> f2
                                 | None => True
                               end with
          | Build_OneOf _ x1 v1 => 
            fun eqf1 => 
              match f2 as f2' return f2 = f2' -> 
                                     match sym_eqb f1 f2 with
                                       | Some true => f1 = f2
                                       | Some false => f1 <> f2
                                       | None => True
                                     end with
                | Build_OneOf _ x2 v2 => 
                  fun eqf2 =>
                    match Pos.eq_dec x1 x2 with
                      | left eqx =>
                        match pmap_lookup' m x1 as o return 
                              o = pmap_lookup' m x1 ->
                              match sym_eqb f1 f2 with
                                | Some true => f1 = f2
                                | Some false => f1 <> f2
                                | None => True
                              end with
                          | Some T => fun eqT => _
                          | None => _
                        end eq_refl
                      | right _ => _
                    end       
              end eq_refl
        end eq_refl
}.
subst.
simpl.
generalize dependent (H2 x2).
generalize dependent (H1 x2).
clear H2 H1.
revert v2 v1.
unfold eq_rect_r, eq_rect, eq_sym.
simpl.
destruct (Pos.eq_dec x2 x2); [|congruence].
simpl.
cbv -[pmap_lookup'].
admit. (* Problems with dependent types *)
Admitted.

End RSym_OneOf.