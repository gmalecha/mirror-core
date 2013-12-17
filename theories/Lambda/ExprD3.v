Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.ListNth.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Cases.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprDI.
Require Import MirrorCore.Lambda.ExprT.

Set Implicit Arguments.
Set Strict Implicit.

Module EXPR_DENOTE_core <: ExprDenote_core.

  Create HintDb exprD_rw discriminated.

  Section with_types.
    Context {typ : Type}.
    Context {typD : list Type -> typ -> Type}.
    Context {func : Type}.
    Context {RType_typ : RType typD}.
    Context {typ_arr : TypInstance2 typD Fun}.
    Context {RSym_func : RSym typD func}.


    Context {RTypeOk_typ : RTypeOk RType_typ}.
    Context {typ_arrOk : TypInstance2_Ok typ_arr}.

    Let tyArr := @typ2 _ typD _ typ_arr.
    Let tyArr_outof ts l r : typD ts (typ2 l r) -> typD ts l -> typD ts r :=
      @Iso.soutof _ _ (typ2_iso ts l r) (fun x => x).
    Let tyArr_into ts l r : (typD ts l -> typD ts r) -> typD ts (typ2 l r) :=
      @Iso.sinto _ _ (typ2_iso ts l r) (fun x => x).

    Fixpoint exprD_simul' (e : expr typ func) (uvar_env var_env : tenv typ) {struct e} :
      option { t : typ & hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> typD nil t } :=
      let Z t := hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> typD nil t in
      match e return option (sigT Z) with
        | Var x =>
          match nth_error var_env x as pf
                return pf = nth_error var_env x ->
                       option (sigT Z)
          with
            | None => fun _ => None
            | Some t => fun pf =>
              Some (existT _ t (fun _ e => match pf in _ = t''
                                               return match t'' with
                                                        | Some t => typD nil t
                                                        | None => unit
                                                      end -> typD nil t with
                                           | eq_refl => fun x => x
                                         end (hlist_nth e x)))
          end eq_refl
        | UVar x =>
          match nth_error uvar_env x as pf
                return pf = nth_error uvar_env x ->
                       option { t : typ & Z t }
          with
            | None => fun _ => None
            | Some t => fun pf =>
              Some (existT _ t (fun e => match pf in _ = t''
                                               return match t'' with
                                                        | Some t => typD nil t
                                                        | None => unit
                                                      end -> hlist (typD nil) var_env -> typD nil t with
                                           | eq_refl => fun x _ => x
                                         end (hlist_nth e x)))
          end eq_refl

        | Inj f =>
          match typeof_sym f as z
                return match z with
                         | None => unit
                         | Some ft => typD nil ft
                       end -> _
          with
            | None => fun _ => None
            | Some ft => fun val =>
                           Some (existT Z ft (fun _ _ => val))
          end (symD f)
        | Abs t' e =>
          match exprD_simul' e uvar_env (t' :: var_env) with
            | None => None
            | Some (existT t v) =>
              Some (existT Z
                           (tyArr t' t) (fun u g => tyArr_into (fun x => v u (Hcons x g))))
          end
        | App f x =>
          match exprD_simul' f uvar_env var_env with
            | None => None
            | Some (existT ft f) =>
              @typ2_matchW _ _ _ typ_arr nil ft
                (fun x =>
                   (hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> x)
                   -> option (sigT Z))
                (fun l r =>
                   match exprD' x uvar_env var_env l with
                     | None => fun _ => None
                     | Some x => fun f =>
                       Some (existT Z r (fun u v => (f u v) (x u v)))
                              end)
                (fun _ => fun _ => None)
                f
          end
      end
    with exprD' (e : expr typ func) (uvar_env var_env : tenv typ) (t : typ) {struct e} :
           option (hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> typD nil t) :=
           match e with
             | Var x =>
               match nth_error var_env x as z
                     return z = nth_error var_env x ->
                            option (hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> typD nil t)
               with
                 | None => fun _ => None
                 | Some t' => fun pf =>
                                match type_cast nil t' t with
                                  | Some f =>
                                    Some (fun _ e => match pf in _ = t''
                                                         return match t'' with
                                                                  | Some t => typD nil t
                                                                  | None => unit
                                                                end -> typD nil t with
                                                     | eq_refl => fun x => f (fun x => x) x
                                                   end (hlist_nth e x))
                                  | None => None
                                end
               end eq_refl
             | UVar x =>
               match nth_error uvar_env x as z
                     return z = nth_error uvar_env x ->
                            option (hlist (typD nil) uvar_env -> hlist (typD nil) var_env -> typD nil t)
               with
                 | None => fun _ => None
                 | Some t' => fun pf =>
                                match type_cast nil t' t with
                                  | Some f =>
                                    Some (fun e _ => match pf in _ = t''
                                                         return match t'' with
                                                                  | Some t => typD nil t
                                                                  | None => unit
                                                                end -> typD nil t with
                                                     | eq_refl => fun x => f (fun x => x) x
                                                   end (hlist_nth e x))
                                  | None => None
                                end
               end eq_refl
             | Inj f =>
               match symAs f t with
                 | None => None
                 | Some val => Some (fun _ _ => val)
               end
             | Abs t' e =>
               @typ2_matchW _ _ _ typ_arr nil t
                            (fun T => option (hlist (typD nil) uvar_env ->
                                              hlist (typD nil) var_env -> T))
                            (fun lt rt =>
                               match type_cast nil lt t' with
                                 | None => None
                                 | Some cast =>
                                   match @exprD' e uvar_env (t' :: var_env) rt with
                                     | None => None
                                     | Some f =>
                                       Some (fun u x y =>
                                               f u (@Hcons _ (typD nil) _ _
                                                         (cast (fun x => x) y) x))
                                   end
                               end)
                            (fun _ => None)
             | App f x =>
               match exprD_simul' f uvar_env var_env with
                 | Some (existT tf f) =>
                   @typ2_matchW _ _ _ typ_arr nil tf
                                (fun T =>
                                   (hlist (typD nil) uvar_env ->
                                    hlist (typD nil) var_env -> T) ->
                                   option (hlist (typD nil) uvar_env ->
                                           hlist (typD nil) var_env ->
                                           typD nil t))
                                (fun lt rt => fun f =>
                                   match exprD' x uvar_env var_env lt with
                                     | None => None
                                     | Some x =>
                                       match type_cast nil rt t with
                                         | None => None
                                         | Some cast =>
                                           Some (fun u v =>
                                                   cast (fun x => x) ((f u v) (x u v)))
                                       end
                                   end)
                                (fun _ => fun _ => None)
                                f
                 | _ => None
               end
           end.

    Definition exprD (e : expr typ func) (uvar_env var_env : env typD) (t : typ)
    : option (typD nil t) :=
      let (tus,us) := split_env uvar_env in
      let (tvs,vs) := split_env var_env in
      match exprD' e tus tvs t with
        | None => None
        | Some f => Some (f us vs)
      end.

    Theorem split_env_nth_error : forall ve v tv,
      nth_error ve v = Some tv <->
      match nth_error (projT1 (split_env ve)) v as t
      return match t with
               | Some v => typD nil v
               | None => unit
             end -> Prop
      with
        | None => fun _ => False
        | Some v => fun res => tv = existT _ v res
      end (hlist_nth (projT2 (split_env ve)) v).
    Proof.
      induction ve; simpl; intros.
      { destruct v; simpl in *; intuition; inversion H. }
      { destruct v; simpl in *.
        { intuition.
          { inversion H; subst. destruct tv; reflexivity. }
          { subst. destruct a. reflexivity. } }
        { eapply IHve. } }
    Qed.

    Theorem exprD'_Var : forall us ve v t,
      exprD' (Var v) us ve t =
      match nth_error ve v as z
          return z = nth_error ve v ->
                 option (hlist (typD nil) us -> hlist (typD nil) ve -> typD nil t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match type_cast _ t' t with
              | Some f =>
                Some (fun _ e => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD nil t
                                              | None => unit
                                            end -> typD nil t with
                                 | eq_refl => fun x => f (fun x => x) x
                               end (hlist_nth e v))
              | None => None
            end
        end eq_refl.
    Proof. reflexivity. Qed.

    Theorem exprD'_UVar : forall us ve v t,
      exprD' (UVar v) us ve t =
      match nth_error us v as z
          return z = nth_error us v ->
                 option (hlist (typD nil) us -> hlist (typD nil) ve -> typD nil t)
        with
          | None => fun _ => None
          | Some t' => fun pf =>
            match type_cast _ t' t with
              | Some f =>
                Some (fun e _ => match pf in _ = t''
                                     return match t'' with
                                              | Some t => typD nil t
                                              | None => unit
                                            end -> typD nil t with
                                 | eq_refl => fun x => f (fun x => x) x
                               end (hlist_nth e v))
              | None => None
            end
        end eq_refl.
    Proof. reflexivity. Qed.

    Theorem exprD'_Abs : RTypeOk RType_typ -> TypInstance2_Ok typ_arr ->
                         forall us ve t  e u,
       exprD' (Abs t e) us ve u =
       @typ2_matchW _ _ _ typ_arr nil u
                            (fun T => option (hlist (typD nil) us ->
                                              hlist (typD nil) ve -> T))
                            (fun lt rt =>
                               match type_cast nil lt t with
                                 | None => None
                                 | Some cast =>
                                   match @exprD' e us (t :: ve) rt with
                                     | None => None
                                     | Some f =>
                                       Some (fun u x y =>
                                               f u (@Hcons _ (typD nil) _ _
                                                         (cast (fun x => x) y) x))
                                   end
                               end)
                            (fun _ => None).
    Proof. reflexivity. Qed.

    Theorem exprD'_Sym : forall us ve f t,
      exprD' (@Inj typ func f) us ve t =
      match symAs f t with
        | None => None
        | Some val => Some (fun _ _ => val)
      end.
    Proof. reflexivity. Qed.

   Lemma exprD'_exprD_simul' : forall e us ve t val,
     exprD_simul' e us ve = Some (@existT _ _ t val) ->
     exists val', exprD' e us ve t = Some val'
                  /\ forall a b, val a b = val' a b.
   Proof.
     induction e; simpl; intros.
     { match goal with
         | H : context [ @eq_refl ?X ?Y ] |- _ =>
           generalize dependent (@eq_refl X Y)
       end.
       pattern (nth_error ve v) at 1 3 7.
       destruct (nth_error ve v); try congruence.
       intros. inv_all. subst. subst.
       destruct (type_cast_refl nil t0) as [ ? [ ? ? ] ].
       simpl in *.
       match goal with
         | H : ?X = _ |- context [ ?Y ] =>
           change Y with X; rewrite H
       end.
       eexists; split; eauto.
       intros; simpl.
       match goal with
         | |- _ ?X = _ ?Y =>
           change Y with X ; generalize X
       end. rewrite <- e.
       intros. rewrite H0. reflexivity. }
     { unfold symAs.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       inv_all; subst. subst.
       destruct (type_cast_refl nil t0) as [ ? [ ? ? ] ].
       simpl in *.
       match goal with
         | H : ?X = _ |- context [ ?Y ] =>
           change Y with X; rewrite H
       end.
       eexists; split; eauto.
       simpl. intros. rewrite H0. reflexivity. }
     { forward. subst.
       destruct (@typ2_matchW_case _ _ _ _ _ _ nil x).
       { do 3 destruct H. destruct H.
         rewrite H2 in *.
         (** TODO: isofunctors **)
         admit. }
       { rewrite H in *. congruence. } }
     { forward. inv_all; subst. subst.
       unfold tyArr.
       rewrite (@typ2_matchW_typ2 _ _ _ _ _ _ nil).
       destruct (type_cast_refl nil t) as [ ? [ ? ? ] ].
       match goal with
         | H : ?X = _ |- context [ ?Y ] =>
           change Y with X; rewrite H
       end.
       eapply IHe in H0; clear IHe.
       destruct H0 as [ ? [ ? ? ] ].
       rewrite H0.
       (** TODO: isofunctors **)
       admit. }
     { match goal with
         | H : context [ @eq_refl ?X ?Y ] |- _ =>
           generalize dependent (@eq_refl X Y)
       end.
       pattern (nth_error us u) at 1 3 7.
       destruct (nth_error us u); try congruence.
       intros. inv_all. subst. subst.
       destruct (type_cast_refl nil t0) as [ ? [ ? ? ] ].
       simpl in *.
       match goal with
         | H : ?X = _ |- context [ ?Y ] =>
           change Y with X; rewrite H
       end.
       eexists; split; eauto.
       intros; simpl.
       match goal with
         | |- _ ?X _ = _ ?Y =>
           change Y with X ; generalize X
       end. rewrite <- e.
       intros. rewrite H0. reflexivity. }
   Qed.

(*
   Lemma exprD'_typeof : forall e ve t val,
     exprD' ve e t = Some val ->
     typeof_expr (typeof_env us) ve e = Some t.
   Proof.
     induction e; simpl; intros.
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error ve v)
                   (f : forall F : Type -> Type, F (typD nil t') -> F (typD nil t)) :=
               (fun e : hlist (typD nil) ve =>
                          match
                            pf in (_ = t'')
                            return
                            (match t'' with
                               | Some t0 => typD nil t0
                               | None => unit
                             end -> typD nil t)
                          with
                            | eq_refl => fun x : typD nil t' => f (fun x : Type => x) x
                          end (hlist_nth e v))
           in
           match
             nth_error ve v as z
             return
             (z = nth_error ve v ->
              option (hlist (typD nil) ve -> typD nil t))
           with
             | Some t' =>
               fun pf : Some t' = nth_error ve v =>
                 match typ_cast_typ ts nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error ve v => None
           end eq_refl = Some val -> nth_error ve v = Some t).
       intro zzz; clearbody zzz; revert zzz.
       gen_refl. destruct (nth_error ve v); try congruence; intros.
       match goal with
         | _ : match ?X with _ => _ end = _ |- _ =>
           consider X; try congruence; intros
       end.
       generalize (typ_cast_typ_eq _ _ _ _ H); intros. subst; auto. }
     { unfold symAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence; intros.
       simpl in *.
       forward.
       generalize (typ_cast_typ_eq _ _ _ _ H); intros.
       congruence. }
     { specialize (IHe1 ve).
       consider (exprD_simul' ve e1); try congruence; intros.
       destruct s. destruct x; try congruence.
       eapply exprD'_exprD_simul' in H.
       eapply IHe1 in H. rewrite H.
       specialize (IHe2 ve x1).
       destruct (exprD' ve e2 x1); try congruence.
       specialize (IHe2 _ eq_refl). rewrite IHe2.
       simpl. change (typ_eqb x1 x1) with (x1 ?[ eq ] x1).
       rewrite rel_dec_eq_true; eauto with typeclass_instances.
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ H0). congruence. }
     { destruct t0; try congruence.
       specialize (IHe (t :: ve) t0_2).
       match goal with
         | H : match ?X with _ => _ end = _ |- _ =>
           consider X; intros; try congruence
       end.
       generalize (@typ_cast_typ_eq _ _ _ _ _ H); intro; subst.
       destruct (exprD' (t :: ve) e t0_2); try congruence.
       erewrite IHe; eauto. }
     { unfold lookupAs, typeof_env in *.
       rewrite nth_error_map.
       destruct (nth_error us u); try congruence.
       destruct s; simpl.
       repeat match goal with
                | H : match ?X with _ => _ end = _ |- _ =>
                  consider X; intros; try congruence
              end.
       specialize (typ_cast_typ_eq _ _ _  _ H). congruence. }
   Qed.

   Lemma exprD_simul'_None : forall e ve,
     match exprD_simul' ve e with
       | None => typeof_expr (typeof_env us) ve e = None
       | Some t => typeof_expr (typeof_env us) ve e = Some (projT1 t)
     end.
   Proof.
     induction e; simpl; intros.
     { change (
           let zzz t (pf : Some t = nth_error ve v) :=
               (fun e : hlist (typD nil) ve =>
                  match
                    pf in (_ = t'')
                    return
                    (match t'' with
                       | Some t0 => typD nil t0
                       | None => unit
                     end -> typD nil t)
                  with
                    | eq_refl => fun x : typD nil t => x
                  end (hlist_nth e v))
           in
           match
             match
               nth_error ve v as pf
               return
               (pf = nth_error ve v ->
                option {t : typ & hlist (typD nil) ve -> typD nil t})
             with
               | Some t =>
                 fun pf : Some t = nth_error ve v =>
                   Some
                     (existT (fun x1 : typ => hlist (typD nil) ve -> typD nil x1)
                             t
                             (zzz t pf))
               | None => fun _ : None = nth_error ve v => None
             end eq_refl
           with
             | Some t => nth_error ve v = Some (projT1 t)
             | None => nth_error ve v = None
           end).
       intro zzz; clearbody zzz; revert zzz.
       destruct (nth_error ve v); auto. }
     { generalize (symD f). forward. }
     { specialize (IHe1 ve). specialize (IHe2 ve).
       destruct (exprD_simul' ve e1).
       { destruct s; simpl in *.
         rewrite IHe1.
         destruct x; simpl; try match goal with
                                  | |- context [ match ?X with _ => _ end ] =>
                                    destruct X; reflexivity
                                end.
         consider (exprD_simul' ve e2); intros; try rewrite IHe2.
         { destruct s. generalize (exprD'_exprD_simul' _ H).
           consider (exprD' ve e2 x1); intros.
           { simpl.
             consider (typ_eqb x1 x); auto; intros.
             eapply exprD'_typeof in H0.
             eapply exprD'_typeof in H1. congruence. }
           { simpl. consider (typ_eqb x1 x); auto; intros.
             subst. congruence. } }
         { rewrite H0.
           consider (exprD' ve e2 x1); auto; intros.
           exfalso. apply exprD'_typeof in H1. congruence. } }
       { rewrite IHe1. auto. } }
     { specialize (IHe (t :: ve)).
       consider (exprD_simul' (t :: ve) e); intros.
       { destruct s. simpl. rewrite IHe. reflexivity. }
       { rewrite H0. auto. } }
     { rewrite nth_error_typeof_env.
       destruct (nth_error us u); auto.
       destruct s. reflexivity. }
   Qed.

   Lemma exprD'_typeof_None : forall e ve t,
     exprD' ve e t = None ->
     typeof_expr (typeof_env us) ve e <> Some t.
   Proof.
     induction e; simpl; intros.
     { revert H.
       change (
           let zzz t' (pf : Some t' = nth_error ve v)
                   (f : forall F : Type -> Type, F (typD nil t') -> F (typD nil t))  :=
               (fun e : hlist (typD nil) ve =>
              match
                pf in (_ = t'')
                return
                  (match t'' with
                   | Some t0 => typD nil t0
                   | None => unit
                   end -> typD nil t)
              with
              | eq_refl => fun x : typD nil t' => f (fun x : Type => x) x
              end (hlist_nth e v))
           in
           match
             nth_error ve v as z
             return
             (z = nth_error ve v ->
              option (hlist (typD nil) ve -> typD nil t))
           with
             | Some t' =>
               fun pf : Some t' = nth_error ve v =>
                 match typ_cast_typ ts nil t' t with
                   | Some f =>
                     Some (zzz t' pf f)
                   | None => None
                 end
             | None => fun _ : None = nth_error ve v => None
           end eq_refl = None -> nth_error ve v <> Some t
         ).
       intro zzz; clearbody zzz; revert zzz; gen_refl.
       destruct (nth_error ve v); try congruence; intros.
       intro. inv_all; subst.
       rewrite typ_cast_typ_refl in *. congruence. }
     { unfold symAs in *.
       generalize dependent (symD f).
       destruct (typeof_sym f); try congruence.
       intros. intro. inv_all; subst.
       simpl in *.
       rewrite typ_cast_typ_refl in *. congruence. }
     { consider (exprD_simul' ve e1); intros.
       { destruct s. eapply exprD'_exprD_simul' in H.
         rewrite (exprD'_typeof _ _ H).
         destruct x; simpl;
         try match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 destruct X; intuition congruence
             end.
         consider (exprD' ve e2 x1); intros.
         { erewrite exprD'_typeof by eauto.
           intro. consider (typ_eqb x1 x1); try congruence; intros; inv_all.
           subst. rewrite typ_cast_typ_refl in *. congruence. }
         { specialize (IHe2 _ _ H0).
           destruct (typeof_expr (typeof_env us) ve e2); try congruence.
           consider (typ_eqb x1 t1); congruence. } }
       { generalize (exprD_simul'_None e1 ve).
         rewrite H. intro. rewrite H1. intuition congruence. } }
     { consider (typeof_expr (typeof_env us) (t :: ve) e); intros.
       2: intuition congruence.
       intro. inv_all; subst.
       rewrite typ_cast_typ_refl in *.
       specialize (IHe (t :: ve) t1).
       destruct (exprD' (t :: ve) e t1); try congruence.
       apply IHe; eauto. }
     { unfold lookupAs in *.
       rewrite nth_error_typeof_env.
       destruct (nth_error us u); intuition; try congruence.
       destruct s. simpl in *; inv_all; subst.
       rewrite typ_cast_typ_refl in *. congruence. }
   Qed.

  Theorem typeof_expr_eq_exprD_False : forall l ve e t x,
    typecheck_expr (typeof_env us) (l :: typeof_env ve) e t = true ->
    exprD (existT _ l x :: ve) e t = None ->
    False.
  Proof.
    intros. unfold exprD in *. simpl in *.
    consider (exprD' (l :: projT1 (split_env ve)) e t); try congruence; intros.
    eapply exprD'_typeof_None in H0.
    unfold typecheck_expr in *.
    rewrite split_env_projT1 in H0. unfold typeof_env in *.
    destruct (typeof_expr (map (projT1 (P:=typD nil)) us)
         (l :: map (projT1 (P:=typD nil)) ve) e).
    consider (Some t0 ?[ eq ] Some t); try congruence.
    simpl in *. congruence.
  Qed.
*)

  Axiom exprD'_App
  : RTypeOk RType_typ ->
    TypInstance2_Ok typ_arr ->
    forall us ve t e arg,
      exprD' (App e arg) us ve t =
      Monad.bind (typeof_expr us ve e)
           (fun t' =>
              @typ2_matchW _ _ _ typ_arr nil t'
                           (fun T =>
                              option (hlist (typD nil) us -> hlist (typD nil) ve -> T) ->
                              option (hlist (typD nil) us -> hlist (typD nil) ve -> typD nil t))
                           (fun l r => fun f' =>
                                         match f'
                                               , exprD' arg us ve l
                                               , type_cast nil r t
                                         with
                                           | Some f , Some x , Some cast =>
                                             Some (fun (u : hlist (typD nil) us)
                                                       (g : hlist (typD nil) ve) =>
                                                     cast (fun x => x) ((f u g) (x u g)))
                                           | _ , _ , _ =>
                                             None
                                         end)
                           (fun _ => fun _ => None)
                           (exprD' e us ve t')).
(*
  Proof.
    simpl; intros.
    consider (exprD_simul' ve e); intros.
    { destruct s; generalize (exprD'_exprD_simul' _ H).
      intro.
      rewrite (exprD'_typeof _ _ H0).
      destruct x; auto.
      rewrite H0. reflexivity. }
    { generalize (exprD_simul'_None e ve).
      rewrite H. intro.
      rewrite H0. auto. }
  Qed.
*)
  End with_types.

End EXPR_DENOTE_core.
