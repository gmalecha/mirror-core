Require Import ExtLib.Data.Map.FMapPositive.
Require Import ExtLib.Data.SumN.
Require Import ExtLib.Tactics.

Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section RSym_OneOf.
  Context {typ : Type} {RType_typ : RType typ} {RTypeOk_typ : RTypeOk}.

  Instance RSym_Empty_set : RSym (Empty_set) :=
  { typeof_sym s := None
  ; symD := fun f => match f return unit with end
  ; sym_eqb := fun f _ => match f return option bool with end
  }.

  Definition typeof_sym_OneOf {m : pmap Type}
    (H : forall p, RSym (match pmap_lookup' m p with
                         | Some T => T
                         | None => Empty_set
                         end))
    (s : OneOf m) : option typ :=
    match s with
      | mkOneOf _ x v =>
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
    (H : forall p, RSym (match pmap_lookup' m p with
                         | Some T => T
                         | None => Empty_set
                         end))
    (f : OneOf m)
  : match typeof_sym_OneOf H f with
    | Some t => typD t
    | None => unit:Type
    end.
  refine (
    match f as f' return f = f' ->
                         match typeof_sym_OneOf H f' with
                           | Some t => typD t
                           | None => unit:Type
                         end with
      | mkOneOf _ x v =>
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
    (H : forall p, RSym (match pmap_lookup' m p with
                         | Some T => T
                         | None => Empty_set
                         end))
    (f1 f2 : OneOf m) : option bool :=
    match Pos.eq_dec (index _ f1) (index _ f2) with
    | left pf =>
      match pf in _ = T
            return RSym (match pmap_lookup' m T with
                         | Some T => T
                         | None => Empty_set
                         end) ->
                   match pmap_lookup' m (index _ f1) with
                   | Some T => T
                   | None => Empty_set
                   end ->
                   match pmap_lookup' _ T with
                   | Some T => T
                   | None => Empty_set
                   end ->
                   option bool
      with
      | eq_refl => @sym_eqb _ _ _
      end (H _) (value m f1) (value _ f2)
    | right _ => None
    end.

  Instance RSymOneOf (m : pmap Type)
    (H : forall p, RSym (match pmap_lookup' m p with
                         | Some T => T
                         | None => Empty_set
                         end))
  : RSym (OneOf m) :=
  { typeof_sym s := typeof_sym_OneOf H s
  ; symD f := symD_OneOf H f
  ; sym_eqb f1 f2 := sym_eqb_OneOf H f1 f2
  }.

  Instance RSym_Empty : RSym (OneOf Empty) :=
  { typeof_sym s := None
  ; symD := fun f => match OneOf_Empty f return unit with end
  ; sym_eqb := fun f _ => match OneOf_Empty f return option bool with end
  }.

  Instance RSymOk_OneOf (m : pmap Type)
           (H1 : forall p, RSym (match pmap_lookup' m p with
                                 | Some T => T
                                 | None => Empty_set
                                 end))
           (H2 : forall p, RSymOk (H1 p))
  : RSymOk (RSymOneOf m H1) :=
  { sym_eqbOk f1 f2 :=
      match f1 as f1'
            return match sym_eqb f1' f2 with
                   | Some true => f1' = f2
                   | Some false => f1' <> f2
                   | None => True
                   end
      with
      | mkOneOf _ x1 v1 =>
          match f2 as f2'
                return
                match sym_eqb (mkOneOf _ x1 v1) f2' with
                | Some true => (mkOneOf _ x1 v1) = f2'
                | Some false => (mkOneOf _ x1 v1) <> f2'
                | None => True
                end
          with
          | mkOneOf _ x2 v2 => _
          end
      end
  }.
  simpl. unfold sym_eqb_OneOf. simpl.
  destruct (Pos.eq_dec x1 x2).
  { destruct e.
    generalize (@sym_eqbOk _ _ _ _ (H2 x1) v1 v2).
    destruct (sym_eqb v1 v2); auto.
    { destruct b; intros; subst; auto.
      intro. inv_all.
      apply H. rewrite H3. clear - RTypeOk_typ.
      rewrite (UIP_refl x). reflexivity. } }
  { trivial. }
  Defined.

End RSym_OneOf.