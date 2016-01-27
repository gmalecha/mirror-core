(** This file contains the [forwardy] tactic which works mostly
 ** like [forward] but is specialized to generate slightly better
 ** proofs
 **)

Lemma match_option_False
: forall T (P : Prop) (x : option T) (K : T -> Prop),
    (forall y, x = Some y -> K y -> P) ->
    match x with
      | None => False
      | Some y => K y
    end ->
    P.
Proof.
  clear. intros.
  destruct x; eauto. destruct H0.
Qed.

Lemma match_option_None
: forall (T U : Type) (P : Prop) (x : option T) z (K : T -> option U),
    (forall y, x = Some y -> K y = Some z -> P) ->
    match x with
      | None => None
      | Some y => K y
    end = Some z ->
    P.
Proof.
  clear. intros.
  destruct x; eauto. inversion H0.
Qed.

Lemma match_bool_false_None
: forall (T U : Type) (P : Prop) (x : bool) z (K : option U),
    (x = true -> K = Some z -> P) ->
    match x with
      | false => None
      | true => K
    end = Some z ->
    P.
Proof.
  destruct x; try congruence. intuition.
Qed.

Lemma match_bool_true_None
: forall (T U : Type) (P : Prop) (x : bool) z (K : option U),
    (x = false -> K = Some z -> P) ->
    match x with
      | false => K
      | true => None
    end = Some z ->
    P.
Proof.
  destruct x; try congruence. intuition.
Qed.

Lemma match_eq_None
: forall T U (F : T -> Type) (a b : T) (pf : a = b) (P : Prop) (x : option U) z (K : U -> option (F a)),
    (forall y, x = Some y ->
               match pf in _ = U return option (F U) with
                 | eq_refl => K y
               end = Some z -> P) ->
    match pf in _ = U return option (F U) with
      | eq_refl => match x with
                     | None => None
                     | Some y => K y
                   end
    end = Some z ->
    P .
Proof.
  destruct pf. intros.
  destruct x; eauto. congruence.
Qed.

(** TODO(gmalecha): I could do better by remembering P
 **)
Ltac forwardy :=
  let rec continue :=
      repeat match goal with
               | |- match ?X with None => False | Some x => @?F x end -> ?P =>
                 refine (@match_option_False _ P X F _) ; do 2 intro
               | |- match ?X with None => None | Some x => @?F x end = Some ?Y -> ?P =>
                 refine (@match_option_None _ _ P X Y F _) ; do 2 intro
               | |- match ?X in _ = T return option (@?F T) with
                      | eq_refl => match ?Y with
                                     | None => None
                                     | Some x => (@?G x)
                                   end
                    end = Some ?Z -> ?P =>
                 refine (@match_eq_None _ _ F _ _ X P Y Z G _) ; do 2 intro
               | |- (let (x,y) := ?X in _) = Some _ -> _ =>
                 destruct X
               | |- (let (x,y) := ?X in _) -> _ =>
                 destruct X
             end
  in
  repeat match goal with
           | H : match ?X with None => False | Some x => @?F x end |- ?P =>
             revert H ; refine (@match_option_False _ P X F _) ;
             do 2 intro ; continue ; intro
           | H : match ?X with None => None | Some x => @?F x end = Some ?Y |- ?P =>
             revert H ; refine (@match_option_None _ _ P X Y F _) ;
             do 2 intro ; continue ; intro
           | H : match ?X in _ = T return option (@?F T) with
                   | eq_refl => match ?Y with
                                  | None => None
                                  | Some x => (@?G x)
                                end
                 end = Some ?Z |- ?P =>
             revert H ; refine (@match_eq_None _ _ F _ _ X P Y Z G _) ;
             do 2 intro ; continue ; intro
           | H : (let (x,y) := ?X in _) = Some _ |- _ =>
             destruct X
         end.
