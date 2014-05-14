Section foo.
  Variable ts : types.

  Inductive sym : Type := And | Other.
  Instance RSym_sym : RSym (typD ts) sym :=
  { typeof_sym := fun s =>
                    match s with
                      | And => Some (tyArr tyProp (tyArr tyProp tyProp))
                      | Other => Some (tyArr tyProp tyProp)
                    end
  ; symD := fun s =>
              match s as s return match match s with
                                          | And => Some (tyArr tyProp (tyArr tyProp tyProp))
                                          | Other => Some (tyArr tyProp tyProp)
                                        end
                                  with
                                    | None => unit
                                    | Some t => typD ts nil t
                                  end
              with
                | And => and
                | Other => not
              end
  ; sym_eqb := fun _ _ => None
  }.
  Inductive Rbase := Impl | Eq.
  Definition typeForRbase (_ : Rbase) : typ := tyProp.
  Definition T := expr sym.

  Fixpoint RD (r : R Rbase) : relation (typD ts nil (typeForR typeForRbase r)) :=
    match r with
      | Rpointwise l r =>
        (fun f g => forall x y, RD l x y -> RD r (f x) (g y))
      | RInj Impl => Basics.impl
      | RInj Eq => @eq Prop
    end.

  Definition respects (f : expr sym) (r : R Rbase) : option (R Rbase) :=
    match f , r with
      | App (Inj And) _ , RInj Impl => Some (RInj Impl)
      | App (Inj And) _ , RInj Eq => Some (RInj Eq)
      | Inj And , Rpointwise (RInj Impl) (RInj Impl) => Some (RInj Impl)
      | _ , _ => None
    end.

  Definition atomic (e : expr sym) :
    (forall e', TransitiveClosure.rightTrans (@expr_acc sym) e' e -> R Rbase -> T)
    -> R Rbase -> T :=
    fun _ _ => e.

  Definition app : T -> T -> T := App.

  Definition TR (us vs : env (typD ts)) (r : R Rbase) (t : T) (v : typD ts nil (typeForR typeForRbase r)) : Prop :=
    exists v',
      exprD us vs t (typeForR typeForRbase r) = Some v' /\
      (RD r v v' \/ v = v').

  Theorem Hatomic
  : forall us vs e r x result,
      exprD us vs e (typeForR typeForRbase r) = Some x ->
      @atomic e (fun e _ => setoid_rewrite respects atomic app e) r = result ->
      TR us vs r result x.
  Proof.
    intros.
    generalize dependent ((fun (e0 : expr sym)
        (_ : TransitiveClosure.rightTrans (expr_acc (func:=sym)) e0 e) =>
      setoid_rewrite respects atomic app e0)).
    intros.
    unfold atomic in *. subst. red.
    match goal with
      | H : ?X = _ |- context [ ?Y ] =>
        change Y with X ; rewrite H
    end.
    eexists; split; eauto.
  Qed.

  Theorem Hrespects_typ
  : forall r r' e,
      respects e r = Some r' ->
      forall us vs t,
        typeof_expr us vs e = Some t ->
        t = (tyArr (typeForR typeForRbase r') (typeForR typeForRbase r)).
  Proof.
    destruct e; destruct r; simpl; intros; try congruence.
    forward.
    forward; subst. inv_all. subst. reflexivity.
    forward; subst; inv_all; subst.
    unfold type_of_apply in *.
    destruct r; inv_all; subst; inv_all; subst.
    forward. subst; inv_all; subst. reflexivity.
    forward. subst; inv_all; subst; reflexivity.
    forward.
  Qed.

  Theorem Happ
  : forall us vs t1 t2 r1 r2 v1 v2 f,
      respects f t2 = Some t1 ->
      exprD us vs f (typeForR typeForRbase (Rpointwise t1 t2)) = Some v1 ->
      @TR us vs (Rpointwise t1 t2) r1 v1 ->
      @TR us vs t1 r2 v2 ->
      @TR us vs t2 (app r1 r2) (v1 v2).
  Proof.
    unfold app, TR; simpl; intros.
    destruct H1. destruct H2.
    destruct H1; destruct H2.
    red_exprD.
    destruct (typeof_expr_exprD _ us vs r1 (tyArr (typeForR typeForRbase t1) (typeForR typeForRbase t2))).
    unfold WellTyped_expr in H6.
(*
    rewrite H6. 2: eexists. 2: eapply H1.
    clear H5 H6. rewrite H1. rewrite H2.
    rewrite typ_cast_typ_refl.
    eexists; split; eauto.
    intuition; subst.
    { left. eapply H5.
*)
  Admitted.
End foo.