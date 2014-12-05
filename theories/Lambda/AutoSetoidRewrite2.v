Require Import Coq.Classes.Morphisms.
Require Import Coq.PArith.BinPos.
Require Import Coq.Relations.Relations.
Require Import Coq.FSets.FMapPositive.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Recur.GenRec.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprTac.
Require Import MirrorCore.Lambda.AppN.

Set Implicit Arguments.
Set Strict Implicit.

Section setoid.
  Context {typ : Type}.
  Context {func : Type}.
  Context {RType_typD : RType typ}.
  Context {Typ2_Fun : Typ2 RType_typD Fun}.
  Context {RSym_func : RSym func}.

  (** Reasoning principles **)
  Context {RTypeOk_typD : RTypeOk}.
  Context {Typ2Ok_Fun : Typ2Ok Typ2_Fun}.
  Context {RSymOk_func : RSymOk RSym_func}.
  Context {Typ0_Prop : Typ0 _ Prop}.
  Context {RelDec_eq_typ : RelDec (@eq typ)}.
  Context {RelDec_eq_func : RelDec (@eq func)}.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Variable Rbase : Type.
  Variable Req : Rbase -> Rbase -> bool.

  Inductive R : Type :=
  | Rinj (r : Rbase)
  | Rrespects (l r : R)
  | Rpointwise (t : typ) (r : R).

  Variable RbaseD : Rbase -> forall t : typ, option (relation (typD t)).
  Fixpoint RD (r : R) (t : typ) : option (relation (typD t)) :=
    match r with
      | Rinj r => RbaseD r t
      | Rrespects l r =>
        typ2_match (F:=Fun) (fun T => option (relation T)) t
                   (fun lt rt =>
                      match RD l lt , RD r rt with
                        | Some l , Some r => Some (respectful l r)
                        | _ , _ => None
                      end)
                   None
      | Rpointwise _t r =>
        typ2_match (F:=Fun) (fun T => option (relation T)) t
                   (fun lt rt =>
                      match type_cast t _t with
                        | Some _ =>
                          match RD r rt with
                            | Some r => Some (pointwise_relation (typD lt) r)
                            | _ => None
                          end
                        | None => None
                      end)
                   None
    end.


  Definition mrw (T : Type) : Type :=
    option T.
  Definition rw_ret {T} (val : T) : mrw T :=
    Some val.
  Definition rw_bind {T U} (c : mrw T) (k : T -> mrw U) : mrw U :=
    match c with
      | None => None
      | Some v => k v
    end.
  Definition rw_orelse {T} (c1 c2 : mrw T) : mrw T :=
    match c1 with
      | None => c2
      | z => z
    end.
  Definition rw_fail {T} : mrw T := None.

  Section rw_map2.
    Context {T U V : Type}.
    Variable f : T -> U -> mrw V.

    Fixpoint rw_map2 (ts : list T) (us : list U) : mrw (list V) :=
      match ts , us with
        | nil , nil => rw_ret nil
        | t :: ts , u :: us =>
          rw_bind (f t u) (fun v =>
                             rw_bind (rw_map2 ts us)
                                     (fun vs => rw_ret (v :: vs)))
        | _ , _ => rw_fail
      end.
  End rw_map2.


  Let rewrite_expr :=
    forall (es : list (expr typ func * (R -> mrw (expr typ func))))
           (rg : R),
      mrw (expr typ func).
  Section setoid_rewrite.
    Variable respectfulness
    : expr typ func -> rewrite_expr.


    Fixpoint setoid_rewrite2 (e : expr typ func)
             (es : list (expr typ func * (R -> mrw (expr typ func)))) (rg : R)
    : mrw (expr typ func) :=
      match e with
        | App f x =>
          setoid_rewrite2 f ((x, setoid_rewrite2 x nil) :: es) rg
        | Abs t e' =>
          match es with
            | nil => match rg with
                       | Rpointwise _t (*=t*) rg' =>
                         rw_bind (setoid_rewrite2 e' nil rg')
                                 (fun e'' => rw_ret (Abs t e''))
                       | _ => respectfulness (Abs t e') es rg
                     end
            | _ => respectfulness (Abs t e') es rg
          end
        | Var v => respectfulness (Var v) es rg
        | UVar u => respectfulness (UVar u) es rg
        | Inj i => respectfulness (Inj i) es rg
      end.

    Definition setoid_rewrite2_rec tus tvs (ls : list (expr typ func * (R -> mrw (expr typ func)))) : Prop :=
      Forall (fun e =>
                forall t eD,
                  exprD' tus tvs t (fst e) = Some eD ->
                  forall r e' rD,
                    snd e r = Some e' ->
                    RD r t = Some rD ->
                    exists eD',
                      exprD' tus tvs t e' = Some eD' /\
                      forall us vs,
                        rD (eD us vs) (eD' us vs)) ls.

    Hypothesis respectfulness_sound
    : forall e e' tus tvs t es rg rD eesD,
        respectfulness e es rg = Some e' ->
        RD rg t = Some rD ->
        exprD' tus tvs t (apps e (map fst es)) = Some eesD ->
        setoid_rewrite2_rec tus tvs es ->
        exists eesD',
          exprD' tus tvs t e' = Some eesD' /\
          forall us vs,
            rD (eesD us vs) (eesD' us vs).

    Theorem setoid_rewrite2_sound
    : forall e e' tus tvs t es rg rD eesD,
        setoid_rewrite2 e es rg = Some e' ->
        RD rg t = Some rD ->
        exprD' tus tvs t (apps e (map fst es)) = Some eesD ->
        setoid_rewrite2_rec tus tvs es ->
        exists eesD',
          exprD' tus tvs t e' = Some eesD' /\
          forall us vs,
            rD (eesD us vs) (eesD' us vs).
    Proof.
      induction e; simpl; intros; eauto using respectfulness_sound.
      { (* App *)
        eapply IHe1 in H; eauto.
        constructor; eauto.
        simpl. intros. eapply IHe2; eauto. constructor. }
      { (* Abs *)
        destruct es; eauto.
        destruct rg; eauto.
        unfold rw_bind in H.
        consider (setoid_rewrite2 e nil rg).
        - intros. inversion H3; clear H3; subst.
          rewrite exprD'_apps in H1; eauto. simpl in H1.
          unfold apps_sem' in H1.
          simpl in H1.
          { consider (typeof_expr tus (t :: tvs) e); intros.
            - consider (exprD' tus tvs (typ2 t t2) (Abs t e)); intros.
              + consider (type_cast (typ2 t t2) t0); intros.
                * inv_all. subst.
                  revert H3.
                  autorewrite with exprD_rw. simpl.
                  destruct r.
                  repeat rewrite typ2_match_zeta; eauto.
                  repeat rewrite type_cast_refl; eauto.
                  consider (exprD' tus (t :: tvs) t2 e); intros.
                  { autorewrite with eq_rw in H5.
                    inv_all; subst.
                    simpl in H0. rewrite typ2_match_zeta in H0; eauto.
                    consider (type_cast (typ2 t t2) t1); intros.
                    - generalize dependent (typ2_cast t t2).
                      intro e1. autorewrite with eq_rw.
                      consider (RD rg t2); intros.
                      + inv_all; subst.
                        eapply IHe in H; eauto.
                        2: constructor.
                        forward_reason.
                        change_rewrite H.
                        eexists; split; eauto.
                        destruct r. unfold Rcast. simpl.
                        unfold relation. intros. autorewrite with eq_rw.
                        red. intros. eapply H6.
                      + inversion H6.
                    - clear - H5. autorewrite with eq_rw in H5. inversion H5. }
                  { autorewrite with eq_rw in H5. inversion H5. }
                * inversion H5.
              + inversion H4.
            - inversion H3. }
        - inversion 2. }
    Qed.
  End setoid_rewrite.

  Section bottom_up.
    Context (reflexive transitive : R -> bool)
            (rw : expr typ func -> R -> option (expr typ func))
            (respectful : expr typ func -> list (expr typ func) -> R -> option (list R)).

    Definition bottom_up (e : expr typ func) (r : R) : option (expr typ func) :=
      setoid_rewrite2
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
	     match respectful e es r with
	       | None => rw (apps e es) r
	       | Some rs =>
		 rw_bind (rw_map2 (fun f r => (snd f) r) efs rs)
			 (fun es' => rw_ret (apps e es'))
	     end
	     (if reflexive r then rw_ret (apps e es) else rw_fail))
        e nil r.
  End bottom_up.

  Section top_down.
    Context (reflexive transitive : R -> bool)
            (rw : expr typ func -> R -> option (expr typ func))
            (respectful : expr typ func -> list (expr typ func) -> R -> option (list R)).

    Fixpoint top_down (f : nat) (e : expr typ func) (r : R) {struct f}
    : option (expr typ func) :=
      setoid_rewrite2
        (fun e efs r =>
	   let es := map fst efs in
           rw_orelse
             (rw_bind (rw (apps e es) r)
                      (fun e' =>
                         if transitive r then
                           match f with
                             | 0 => rw_ret e'
                             | S f => top_down f e' r
                           end
                         else
                           rw_ret e'))
             match respectful e es r with
	       | None => if reflexive r then rw_ret (apps e es) else rw_fail
	       | Some rs =>
	         rw_orelse
                   (rw_bind (rw_map2 (fun f r => (snd f) r) efs rs)
		            (fun es' => rw_ret (apps e es')))
                   (if reflexive r then rw_ret (apps e es) else rw_fail)
	     end)
        e nil r.
  End top_down.

End setoid.

(*
Definition my_respectfulness (f : expr typ func)
           (es : list (expr typ func * (RG -> mrw (expr typ func))))
           (rg : RG)
: mrw (expr typ func) :=
  rw_ret (apps f (List.map (fun x => fst x) es)).


Definition my_respectfulness' (f : expr nat nat)
               (es : list (expr nat nat * (RG (typ:=nat) nat -> mrw (typ:=nat) nat (expr nat nat))))
               (rg : RG (typ:=nat) nat)
    : mrw (typ:=nat) nat (expr nat nat) :=
      rw_ret (apps f (List.map (fun x => snd x rg) es)).

  Fixpoint build_big (n : nat) : expr nat nat :=
    match n with
      | 0 => Inj 0
      | S n => App (build_big n) (build_big n)
    end.

  Time Eval vm_compute in
      match setoid_rewrite2 (Rbase:=nat) (@my_respectfulness nat nat nat) (build_big 24) nil (RGinj 0) (rsubst_empty _) with
        | Some e => true
        | None => false
      end.
*)


(*
  Variable typeof_Rbase : Rbase -> option typ.
  Fixpoint typeof_R (r : R) : option typ :=
    match r with
      | Rinj r => typeof_Rbase r
      | Rrespects l r =>
        match typeof_R l , typeof_R r with
          | Some lt , Some rt => Some (typ2 lt rt)
          | _ , _ => None
        end
      | Rpointwise t r =>
        match typeof_R r with
          | Some rt => Some (typ2 t rt)
          | None => None
        end
    end.

  Variable RbaseD : forall r : Rbase, match typeof_Rbase r with
                                        | None => unit
                                        | Some t => relation (typD t)
                                      end.
  Fixpoint RD (r : R) : match typeof_R r with
                          | None => unit
                          | Some t => relation (typD t)
                        end.
  refine
    match r as r
          return match typeof_R r with
                   | None => unit
                   | Some t => relation (typD t)
                 end
    with
      | Rinj r => RbaseD r
      | Rrespects l r =>
        
      | Rpointwise t r => _
    end.
  simpl.
*)