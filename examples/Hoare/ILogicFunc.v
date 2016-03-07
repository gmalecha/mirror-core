Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import McExamples.Hoare.ILogic.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable RelDec_typ_eq : RelDec (@eq typ).
  Variable RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq.

  Inductive ilfunc :=
  | ilf_entails (logic : typ)
  | ilf_true (logic : typ)
  | ilf_false (logic : typ)
  | ilf_and (logic : typ)
  | ilf_or (logic : typ)
  | ilf_impl (logic : typ)
  | ilf_exists (arg logic : typ)
  | ilf_forall (arg logic : typ)
  (** It may be a little nicer to remove embed **)
  | ilf_embed (from to : typ).
(* | fref (fi : positive) *)

  Global Instance RelDec_ilfunc : RelDec (@eq ilfunc) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | ilf_entails t, ilf_entails t'
		   | ilf_true t, ilf_true t'
		   | ilf_false t, ilf_false t'
		   | ilf_and t, ilf_and t'
		   | ilf_or t, ilf_or t'
		   | ilf_impl t, ilf_impl t' => t ?[eq] t'
		   | ilf_forall a t, ilf_forall a' t'
		   | ilf_exists a t, ilf_exists a' t'
		   | ilf_embed a t, ilf_embed a' t' => a ?[eq] a' && t ?[eq] t'
(*		   | fref r, fref r' => r ?[eq] r' *)
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
  Qed.

  (** TODO: Build an ordered map over types **)
  (** the canonical implementation doesn't work!
  Inductive tree : (typ -> Type) -> Type :=
  | Node : forall F, option (F tyProp) ->
           tree (fun t => tree (fun u => F (tyArr t u))) ->
           tree F
  | Empty : forall F, tree F.
  **)

  Inductive loption (t : Type) : Type :=
  | lSome : t -> loption t
  | lNone.
  Global Arguments lNone {_}.

  Definition logic_ops := forall (t : typ),
    loption (ILogicOps@{Urefl Urefl} (typD t)).
  Definition embed_ops := forall (t u : typ),
    loption (EmbedOp (typD t) (typD u)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
              | lSome T => @ILogic _ T
              | lNone => True
              end.
  Definition embed_opsOk (ls : logic_ops) (es : embed_ops) : Prop :=
    forall t t',
      match ls t , ls t' , es t t' return Prop with
        | lSome a , lSome b , lSome T => @Embed _ _ a _ T
        | _ , _ , _ => True
      end.

  Variable gs : logic_ops.
  Variable es : embed_ops.

  Variable Typ2_tyArr : Typ2 _ RFun.
  Variable Typ0_tyProp : Typ0 _ Prop.

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
  Let tyProp : typ := @typ0 _ _ _ _.

  Definition typeof_func (f : ilfunc) : option typ :=
    match f with
    | ilf_true t
    | ilf_false t =>
      match gs t with
      | lSome _ => Some t
      | lNone => None
      end
    | ilf_entails t =>
      match gs t with
      | lSome _ => Some (tyArr t (tyArr t tyProp))
      | lNone => None
      end
    | ilf_and t
    | ilf_or t
    | ilf_impl t =>
      match gs t with
      | lSome _ => Some (tyArr t (tyArr t t))
      | lNone => None
      end
    | ilf_forall a t
    | ilf_exists a t =>
      match gs t with
      | lSome _ => Some (tyArr (tyArr a t) t)
      | lNone => None
      end
    | ilf_embed a b =>
      match es a b with
      | lNone => None
      | lSome _ => Some (tyArr a b)
      end
    end.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t
      with
      | eq_refl => match eq_sym (typ2_cast b c) in _ = t
                         return _ -> t with
                   | eq_refl => f
                   end
      end.

  Definition typ2_cast_quant (a b c : typ)
  : ((typD a -> typD b) -> typD c) -> typD (tyArr (tyArr a b) c) :=
    fun f =>
      match eq_sym (typ2_cast (tyArr a b) c) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast a b) in _ = t
                           return t -> _ with
                       | eq_refl => f
                     end
      end.

  Definition funcD (f : ilfunc) :
    match typeof_func f return Type@{Urefl} with
    | Some t => typD t
    | None => unit
    end.
  refine (
    match f as f
          return match typeof_func f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | ilf_true t =>
        match gs t as x
              return (match match x with
			      | lSome _ => Some t
			      | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome t => @ltrue _ t
	  | lNone => tt
        end
      | ilf_false t =>
        match gs t as x
              return (match match x with
			      | lSome _ => Some t
			      | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome t => @lfalse _ t
	  | lNone => tt
        end
      | ilf_entails t =>
        match gs t as x
              return (match match x with
			    | lSome _ => Some (tyArr t (tyArr t tyProp))
			    | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome C =>
            match eq_sym (typ2_cast t (tyArr t tyProp)) in _ = t
                  return t with
              | eq_refl =>
                match eq_sym (typ2_cast t tyProp) in _ = t
                      return _ -> t with
                  | eq_refl =>
                    match eq_sym (typ0_cast (F := Prop)) in _ = t
                          return _ -> _ -> t
                    with
                      | eq_refl => @lentails _ _
                    end
                end
            end
	  | lNone => tt
        end
      | ilf_and t =>
        match gs t as x
              return (match match x with
			      | lSome _ => Some (tyArr t (tyArr t t))
			      | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome t => typ2_cast_bin _ _ _ (@land _ _)
	  | lNone => tt
        end
      | ilf_impl t =>
        match gs t as x
              return (match match x with
			      | lSome _ => Some (tyArr t (tyArr t t))
			      | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome t => typ2_cast_bin _ _ _ (@limpl _ _)
	  | lNone => tt
        end
      | ilf_or t =>
        match gs t as x
              return (match match x with
			      | lSome _ => Some (tyArr t (tyArr t t))
			      | lNone => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | lSome t => typ2_cast_bin _ _ _ (@lor _ _)
	  | lNone => tt
        end
      | ilf_exists a t =>
        match gs t as x return (match match x with
					| lSome _ => Some (tyArr (tyArr a t) t)
					| lNone => None
				      end
                                      return Type@{Urefl}
                                with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | lSome t0 => typ2_cast_quant _ _ _ (@lexists _ t0 (typD a))
	  | lNone => tt
        end
      | ilf_forall a t =>
        match gs t as x return (match match x with
					| lSome _ => Some (tyArr (tyArr a t) t)
					| lNone => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | lSome t0 => typ2_cast_quant _ _ _ (@lforall _ _ _)
	  | lNone => tt
        end
      | ilf_embed t u =>
        match es t u as x
              return match match x with
			     | lSome _ => Some (tyArr t u)
			     | lNone => None
			   end with
		       | Some t0 => typD t0
		       | None => unit
		     end
        with
	  | lSome t0 =>
            match eq_sym (typ2_cast t u) in _ = t return t
            with
              | eq_refl => @embed _ _ _
            end
	  | lNone => tt
        end
    end).
  Defined.

  Global Instance RSym_ilfunc : RSym ilfunc :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

  Require Import MirrorCore.Views.Ptrns.

  (** TODO: There should be a general proof for this *)
  Ltac ptrn_ok_1 :=
    let do_it H :=
        let x := fresh in
        intro x; destruct x; simpl; try solve [ right; compute; reflexivity ] ;
        match goal with
        | H' : _ |- _ =>
          lazymatch H' with
          | H => fail 2
          | _ =>
            let H'' := fresh in
            let x'' := fresh in
            destruct (H H') as [ [ x'' H'' ] | H'' ] ;
              [ left ; exists x'' ; try solve [ compute ; intros; eapply H'' ]
              | right ; try solve [ compute; intros; eapply H'' ] ]
          end
        end
    in
    intros;
    match goal with
    | H : ptrn_ok ?X |- ptrn_ok (_ ?X) => do_it H
    end.

  (** TODO: This should move into MirrorCore.Views.Ptrn *)
  Definition Mtwo {T U V W X} (f : T -> U -> X)
             (p1 : ptrn T V) (p2 : V -> ptrn U W)
             (x1 : T) (x2 : U) : M X W :=
    fun _T good bad =>
      p1 x1 _T (fun v => p2 v x2 _T good (fun u => bad (f x1 u)))
         (fun t => bad (f t x2)).
  Definition Myes {X T} (m : M X T) res : Prop :=
    forall T good bad, m T good bad = good res.
  Definition Mno {X T} (m : M X T) x : Prop :=
    forall T good bad, m T good bad = bad x.
  Definition Mok {X T} (m : M X T) (x : X) : Prop :=
    (exists y, Myes m y) \/ Mno m x.
  Lemma Mtwo_ok {T U V W X} f p1 p2 x1 x2
    : ptrn_ok p1 ->
      (forall v, ptrn_ok (p2 v)) ->
      Mok (@Mtwo T U V W X f p1 p2 x1 x2) (f x1 x2).
  Proof.
    intros.
    destruct (H x1) as [ [ ? ? ] | ].
    - destruct (H0 x x2) as [ [ ? ? ] | ].
      + left. exists x0.
        unfold Mtwo, Succeeds in *.
        red; intros.
        rewrite H1. apply H2.
      + right. red in H1. red in H2.
        red. compute; intros.
        rewrite H1. apply H2.
    - right. red in H1.
      compute; intros. apply H1.
  Qed.

  Lemma Mrebuild_Succeeds : forall {X Y} (p' : ptrn X Y) {T} p f v x,
      (forall T0 (good : T -> T0) (bad : X -> T0),
          Mrebuild (X:=Y) f (p x) good bad = good v) ->
      (forall T0 good bad, p x T0 good (fun x : Y => p' (f x) T0 bad (fun _ : X => good v)) = p x T0 good bad) ->
      Succeeds x p v.
  Proof.
    red. intros.
    unfold Mrebuild in *.
    specialize (H T0 good (fun x => @p' x T0 bad (fun _ => good v))).
    simpl in H.
    rewrite H0 in H. assumption.
  Qed.

  Lemma Mtwo_Succeeds : forall {X Y Z} (p2' : ptrn Z Y) {T T'}
                               (p1 : ptrn X T) (p2 : T -> ptrn Y T') (f : X -> Y -> Z) v arg logic,
      ptrn_ok p1 ->
      (forall T0 (good : _ -> T0) bad,
          Mtwo (X:=Z) f p1 p2 arg logic good bad = good v) ->
      (forall T0 (good : _ -> T0) bad x logic, p2 x logic T0 good
                                                  (fun u : Y => p2' (f arg u) T0 bad (fun _ : Z => good v)) = p2 x logic T0 good bad) ->
      exists val,
        Succeeds arg p1 val /\ Succeeds logic (p2 val) v.
  Proof.
    intros. unfold Mtwo in *.
    destruct (H arg); clear H.
    - destruct H2. exists x.
      split; auto.
      red in H. setoid_rewrite H in H0.
      red. intros. specialize (H0 T0 good).
      specialize (H0 (fun z => p2' z T0 bad (fun _ => good v))).
      simpl in H0.
      rewrite H1 in H0. assumption.
    - clear H1.
      unfold Fails in H2.
      setoid_rewrite H2 in H0.
      specialize (H0 bool (fun _ => true) (fun _ => false)). inversion H0.
  Qed.

  Ltac solve_Succeeds1 :=
    match goal with
    | |- Succeeds ?e (?p' _ _) ?v -> _ =>
      destruct e;
        let H := fresh in
        try solve [ intro H ; specialize (H bool (fun _ => true) (fun _ => false)); inversion H
                  | intros; eexists; split; auto;
                    red in H; simpl in H ;
                    eapply (@Mrebuild_Succeeds _ _ (p' _ get)) in H; [ auto | reflexivity ] ]
    end.

  Ltac solve_Succeeds2 :=
    match goal with
    | |- Succeeds ?e (?p' _ _ _ _) ?v -> _ =>
      destruct e;
        let H := fresh in
        try solve [ intro H ; specialize (H bool (fun _ => true) (fun _ => false)); inversion H
                  | do 2 eexists; split; eauto;
                    red in H; simpl in H ;
                    eapply Mtwo_Succeeds with (p2':=p' _ _ ignore (fun _ => get)) in H; eauto ]
    end.

  Definition fptrn_lentails {T} (k : ptrn typ T) : ptrn ilfunc T :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mrebuild ilf_entails (k t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance fptrn_lentails_ok {T} (p : ptrn typ T)
  : ptrn_ok p -> ptrn_ok (fptrn_lentails p).
  Proof. ptrn_ok_1. Qed.

  Global Instance SucceedsE_fptrn_lentails {T} e k (v : T) : SucceedsE e (fptrn_lentails k) v :=
  { s_result := exists t, e = ilf_entails t /\ Succeeds t k v }.
  Proof. abstract solve_Succeeds1. Defined.

  Definition fptrn_ltrue {T} (k : ptrn typ T) : ptrn ilfunc T :=
    fun x =>
      match x with
      | ilf_true t => Mrebuild ilf_true (k t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance fptrn_ltrue_ok {T} (p : ptrn typ T)
  : ptrn_ok p -> ptrn_ok (fptrn_ltrue p).
  Proof. ptrn_ok_1. Qed.

  Global Instance SucceedsE_fptrn_ltrue {T} e k (v : T) : SucceedsE e (fptrn_ltrue k) v :=
  { s_result := exists t, e = ilf_true t /\ Succeeds t k v }.
  Proof. abstract solve_Succeeds1. Defined.

  Definition fptrn_lfalse {T} (k : ptrn typ T) : ptrn ilfunc T :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mrebuild ilf_false (k t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance fptrn_lfalse_ok {T} (p : ptrn typ T)
  : ptrn_ok p -> ptrn_ok (fptrn_lfalse p).
  Proof. ptrn_ok_1. Qed.

  Global Instance SucceedsE_fptrn_lfalse {T} e k (v : T) : SucceedsE e (fptrn_lfalse k) v :=
  { s_result := exists t, e = ilf_false t /\ Succeeds t k v }.
  Proof. abstract solve_Succeeds1. Defined.

  Definition fptrn_land {T} (k : ptrn typ T) : ptrn ilfunc T :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mrebuild ilf_and (k t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance fptrn_land_ok {T} (p : ptrn typ T)
  : ptrn_ok p -> ptrn_ok (fptrn_land p).
  Proof. ptrn_ok_1. Qed.

  Global Instance SucceedsE_fptrn_land {T} e k (v : T) : SucceedsE e (fptrn_land k) v :=
  { s_result := exists t, e = ilf_and t /\ Succeeds t k v }.
  Proof. abstract solve_Succeeds1. Defined.

  Definition fptrn_limpl {T} (k : ptrn typ T) : ptrn ilfunc T :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mrebuild ilf_impl (k t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.
  Global Instance fptrn_limpl_ok : ltac:(PtrnOk @fptrn_limpl) := ltac:(ptrn_ok_1).

  Global Instance SucceedsE_fptrn_limpl {T} e k (v : T) : SucceedsE e (fptrn_limpl k) v :=
  { s_result := exists t, e = ilf_impl t /\ Succeeds t k v }.
  Proof. abstract solve_Succeeds1. Defined.

  Definition fptrn_lforall {T U} (k : ptrn typ T) (k' : T -> ptrn typ U)
  : ptrn ilfunc U :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mtwo ilf_forall k k' u t
      | ilf_exists u t => Mfail (ilf_exists u t)
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance fptrn_lforall_ok {T U} (p : ptrn typ T) (p' : T -> ptrn typ U)
  : ptrn_ok p -> (forall x, ptrn_ok (p' x)) -> ptrn_ok (fptrn_lforall p p').
  Proof.
    intros. red. destruct x; try solve [ right ; compute; reflexivity ].
    eapply Mtwo_ok; assumption.
  Qed.

  Global Instance SucceedsE_fptrn_lforall {T U} (p : ptrn typ T) (p' : T -> ptrn typ U) e v
  : ptrn_ok p -> SucceedsE e (fptrn_lforall p p') v :=
  { s_result := exists t l : typ, e = ilf_forall t l /\
                                  exists val,
                                    Succeeds t p val /\
                                    Succeeds l (p' val) v }.
  Proof. abstract solve_Succeeds2. Defined.

  Definition fptrn_lexists {T U} (k : ptrn typ T) (k' : T -> ptrn typ U)
  : ptrn ilfunc U :=
    fun x =>
      match x with
      | ilf_true t => Mfail (ilf_true t)
      | ilf_false t => Mfail (ilf_false t)
      | ilf_and t => Mfail (ilf_and t)
      | ilf_or t => Mfail (ilf_or t)
      | ilf_impl t => Mfail (ilf_impl t)
      | ilf_forall u t => Mfail (ilf_forall u t)
      | ilf_exists u t => Mtwo ilf_exists k k' u t
      | ilf_entails t => Mfail (ilf_entails t)
      | ilf_embed u t => Mfail (ilf_embed u t)
      end.

  Global Instance ptrn_lexists_ok {T U} (p : ptrn typ T) (p' : T -> ptrn typ U)
  : ptrn_ok p -> (forall x, ptrn_ok (p' x)) -> ptrn_ok (fptrn_lexists p p').
  Proof.
    intros. red. destruct x; try solve [ right ; compute; reflexivity ].
    eapply Mtwo_ok; assumption.
  Qed.

  Global Instance SucceedsE_fptrn_lexists {T U} (p : ptrn typ T) (p' : T -> ptrn typ U) e v
  : ptrn_ok p -> SucceedsE e (fptrn_lexists p p') v :=
  { s_result := exists t l : typ, e = ilf_exists t l /\
                                  exists val,
                                    Succeeds t p val /\
                                    Succeeds l (p' val) v }.
  Proof. abstract solve_Succeeds2. Defined.

End typed.
