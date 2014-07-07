Require Import ExtLib.Data.Eq.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI3.
Require Import MirrorCore.EProver2.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.LemmaApply.
Require Import MirrorCore.STac.Core.

Set Implicit Arguments.
Set Strict Implicit.

Section parameterized.
  Variable typ : Type.
  Variable expr : Type.
  Variable subst : Type.
  Variable RType_typ : RType typ.
  Variable Typ0_Prop : Typ0 _ Prop.
  Let tyProp : typ := @typ0 _ _ _ _.

  Variable vars_to_uvars : nat -> nat -> expr -> expr.
  Variable exprUnify : tenv typ -> tenv typ -> nat -> expr -> expr -> typ -> subst -> option subst.
  Variable instantiate : (nat -> option expr) -> nat -> expr -> expr.

  Section solve_but_last.
    Variable Subst_subst : Subst subst expr.
    Variables tus tvs : list typ.
    Variable tac : stac typ expr subst.

    Fixpoint solve_all_but_last
             (es : list expr)
             (sub : subst) {struct es}
    : Result typ expr subst :=
      match es with
        | nil => @Solved _ _ _ nil nil sub
        | e :: es =>
          let e := instantiate (fun u => lookup u sub) 0 e in
          match tac tus tvs sub e with
            | Solved nil nil sub' =>
              solve_all_but_last es sub'
            | More tus tvs sub e =>
              match es with
                | nil => More tus tvs sub e
                | _ => @Fail _ _ _
              end
            | _ => @Fail _ _ _
          end
      end.

  End solve_but_last.

  Section eapply_other.
    Variable Subst_subst : Subst subst expr.
    Variable SU : SubstUpdate subst expr.

    Definition fuel := 100.
    Let eapplicable :=
      @eapplicable typ expr tyProp subst vars_to_uvars
                   exprUnify.

    (** This of this like:
     **   eapply lem ; [ solve [ tac ] | solve [ tac ] | .. | try solve [ tac ] ]
     ** i.e. first eapply the lemma and then require that all side-conditions
     ** except the last are solved by the prover [tac], currently with
     ** empty facts.
     **)
    Definition eapply_other
               (lem : lemma typ expr expr)
               (tac : stac typ expr subst)
    : stac typ expr subst :=
      let len_vars := length lem.(vars) in
      fun tus tvs sub e =>
      match eapplicable sub tus tvs lem e with
        | None => @Fail _ _ _
        | Some sub' =>
          let len_uvars := length tus in
          match pull (expr := expr) len_uvars len_vars sub' with
            | Some sub'' =>
              (** If we have instantiated everything then we can be a little
               ** bit more efficient
               **)
              let premises :=
                  map (fun e => instantiate (fun u => lookup u sub) 0
                                            (vars_to_uvars 0 len_uvars e))
                      lem.(premises)
              in
              solve_all_but_last _ tus tvs tac premises sub''
            | None =>
              let premises := map (vars_to_uvars 0 len_uvars) lem.(premises) in
              match
                solve_all_but_last _ (tus ++ lem.(vars)) tvs tac
                                   premises sub'
              with
                | Fail => @Fail _ _ _
                | Solved tus' tvs' sub'' =>
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' => @Solved _ _ _ nil nil sub'''
                  end
                | More tus tvs sub'' e =>
                  (** TODO: In this case it is not necessary to pull everything
                   ** I could leave unification variables in place
                   **)
                  match pull (expr := expr) len_uvars len_vars sub'' with
                    | None => @Fail _ _ _
                    | Some sub''' => More (firstn len_uvars tus) tvs sub''' e
                  end
              end
          end
      end.
  End eapply_other.


  Variable Expr_expr : Expr RType_typ expr.
  Variable ExprOk_expr : ExprOk Expr_expr.
  Variable Subst_subst : Subst subst expr.
  Variable SubstOk_subst : @SubstOk _ _ _ _ Expr_expr Subst_subst.
  Variable SubstUpdate_subst : SubstUpdate subst expr.
  Variable SubstUpdateOk_subst : SubstUpdateOk SubstUpdate_subst SubstOk_subst.
  Variable UnifySound_exprUnify : unify_sound _ exprUnify.

  Require Import ExtLib.Data.List.
  Require Import ExtLib.Structures.Traversable.

  Theorem solve_all_but_last_sound
  : forall tus tvs (tac : stac typ expr subst) (prems : list expr) (sub : subst),
      stac_sound tac ->
      match solve_all_but_last _ tus tvs tac prems sub with
        | Fail => True
        | Solved tus' tvs' s' =>
          match mapT (F := option) (T := list) (goalD Expr_expr Typ0_Prop tus tvs) prems with
            | Some Gs =>
              match substD tus tvs sub with
                | Some sV =>
                  match substD (tus ++ tus') (tvs ++ tvs') s' with
                    | Some s'V =>
                      forall (us : hlist (typD nil) tus)
                             (vs : hlist (typD nil) tvs),
                        (exists
                            (us' : hlist (typD nil) tus')
                            (vs' : hlist (typD nil) tvs'),
                            s'V (hlist_app us us') (hlist_app vs vs')) ->
                        Forall (fun G => G us vs) Gs /\ sV us vs
                    | None => False
                  end
                | None => True
              end
            | None => True
          end
        | More tus' tvs' s' g' =>
          match mapT (F := option) (T := list) (goalD Expr_expr Typ0_Prop tus tvs) prems with
            | Some Gs =>
              match substD tus tvs sub with
                | Some sV =>
                  match goalD Expr_expr Typ0_Prop (tus ++ tus') (tvs ++ tvs') g' with
                    | Some G' =>
                      match substD (tus ++ tus') (tvs ++ tvs') s' with
                        | Some s'V =>
                          forall (us : hlist (typD nil) tus)
                                 (vs : hlist (typD nil) tvs),
                            (exists
                                (us' : hlist (typD nil) tus')
                                (vs' : hlist (typD nil) tvs'),
                                s'V (hlist_app us us') (hlist_app vs vs') /\
                                G' (hlist_app us us') (hlist_app vs vs')) ->
                            Forall (fun G => G us vs) Gs /\ sV us vs
                        | None => False
                      end
                    | None => False
                  end
                | None => True
              end
            | None => True
          end
      end.
  Proof.
    intros.
    induction prems.
    { simpl. forward. admit. }
    { admit. }
  Qed.

  Hypothesis vars_to_uvars_spec : forall (tus0 : tenv typ) (e : expr) (tvs0 : list typ)
     (t : typ) (tvs' : list typ)
     (val : hlist (typD nil) tus0 ->
            hlist (typD nil) (tvs0 ++ tvs') -> typD nil t),
   exprD' tus0 (tvs0 ++ tvs') e t = Some val ->
   exists
     val' : hlist (typD nil) (tus0 ++ tvs') ->
            hlist (typD nil) tvs0 -> typD nil t,
     exprD' (tus0 ++ tvs') tvs0 (vars_to_uvars (length tvs0) (length tus0) e)
       t = Some val' /\
     (forall (us : hlist (typD nil) tus0) (vs' : hlist (typD nil) tvs')
        (vs : hlist (typD nil) tvs0),
      val us (hlist_app vs vs') = val' (hlist_app us vs') vs).

  Theorem APPLY_sound
  : forall lem tac,
      @lemmaD typ _ expr _ expr (@goalD _ _ _ _ _ ) (@typ0 _ _ _ _)
              (fun P => match typ0_cast nil in _ = T return T
                        with
                          | eq_refl => P
                        end)
              nil nil lem ->
      stac_sound tac ->
      stac_sound (eapply_other _ _ lem tac).
  Proof.
    intros. red. intros.
    unfold eapply_other.
    consider (eapplicable tyProp vars_to_uvars exprUnify s tus tvs lem g); auto; intros.
    eapply (@eapplicable_sound _ _ _ _ _ tyProp (@typ0_cast _ _ _ _)) in H1; eauto.
    { consider (pull (length tus) (length (vars lem)) s0); intros.
      { generalize (@solve_all_but_last_sound tus tvs tac
                      (map
                         (fun e : expr =>
                            instantiate (fun u : nat => lookup u s) 0
                                         (vars_to_uvars 0 (length tus) e)) (premises lem))
                      s1 H0).
        match goal with
          | |- match ?X with _ => _ end -> match ?Y with _ => _ end =>
            change Y with X; consider X; intros
        end; auto.
        { admit. (** Big **) }
        { admit. (** Big **) } }
      { generalize (@solve_all_but_last_sound (tus ++ vars lem) tvs tac
                      (map (vars_to_uvars 0 (length tus)) (premises lem))
                      s0 H0).
        match goal with
          | |- match ?X with _ => _ end -> match match ?Y with _ => _ end with _ => _ end =>
            change Y with X; consider X; intros
        end; auto.
        { admit. (** Big **) }
        { forward.
          red in H. simpl in H.
          forward.
          destruct H7.
          unfold goalD in *. forward.
          inv_all. subst.
          subst tyProp.
          assert (lemmaD' Expr_expr
                          (fun (tus0 tvs0 : tenv typ) (g0 : expr) =>
                             match typ0_cast nil in (_ = t) return (ResType tus0 tvs0 t) with
                               | eq_refl => exprD' tus0 tvs0 g0 (typ0 (F:=Prop))
                             end)
                          (fun x : typD nil (typ0 (F:=Prop)) =>
                             match typ0_cast nil in (_ = t) return t with
                               | eq_refl => x
                             end) nil nil lem = Some P1).
          { revert H. clear.
            unfold lemmaD'. forward.
            inv_all; subst.
            unfold ResType.
            rewrite eq_option_eq. reflexivity. }
          clear H.
          specialize (H9 P1 P0 _ H10 eq_refl H6).
          admit. } } }
    { admit. (** BUG **) }
  Qed.

End parameterized.
