Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.POption.
Require Import ExtLib.Data.HList.
Require Import MirrorCore.Util.PositivePolyMap.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Views.View.
Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.PolymorphicF.
Require Import MirrorCore.Types.ModularTypesT.
Require Import MirrorCore.Types.MTypeUnifyT.

Set Implicit Arguments.
Set Strict Implicit.

Module PolyInst (Import RT : TypeLang) (Import RU : TypeLangUnify with Module RT := RT).
  Section with_symbols.
    Context {tsym : kind -> Type}
            {TS : TSym kindD tsym}.
    Context {sym : Type}
            {RS : @RSym _ (@RT.RType_type tsym TS) sym}.

    Local Fixpoint build_vars p (n : list kind) : hlist (type tsym) n :=
      match n with
      | nil => Hnil
      | n :: ns => Hcons (tyVar _ n p) (build_vars (Pos.succ p) ns)
      end.

    Local Fixpoint get_vars {T} n p
    : forall (ok : hlist (type tsym) n -> T) (bad : T) (m : pmap { n : kind & type tsym n }), T :=
      match n as n return (hlist (type tsym) n -> T) -> T -> pmap { n : kind & type tsym n } -> T with
      | nil => fun ok _ _ => ok Hnil
      | n :: ns => fun ok bad m =>
                    match pmap_lookup m p with
                    | pNone => bad
                    | pSome (existT _ n' z) =>
                      match kind_eq_dec n' n with
                      | right _ => bad
                      | left pf =>
                        get_vars (Pos.succ p)
                                 (fun vs => ok (Hcons match pf in _ = X return type tsym X with
                                                   | eq_refl => z
                                                   end vs)) bad m
                      end
                    end
      end.

    Definition sym_unifier : Type :=
      forall {T} (a b : sym),
        pmap { n : kind & type tsym n } ->
        (pmap { n : kind & type tsym n } -> T) ->
        T -> T.

    Section with_symbol_unify.
      Variable sym_unify : sym_unifier.

      (** NOTE: This function does not need to be complete
       ** TODO: We should really stop looking at the term as
       **       soon as we have instantiated everything
       **)
      Local Fixpoint get_types {T} (a b : expr (type tsym Kstar) sym)
            (s : pmap { n : kind & type tsym n })
            (ok : pmap { n : kind & type tsym n } -> T) (bad : T) {struct a}
        : T :=
        match a , b with
        | App fa aa , App fb ab =>
          get_types fa fb s
                    (fun s' => get_types aa ab s' ok bad)
                    bad
        | Inj a , Inj b =>
          @sym_unify _ a b s ok bad
        | _ , _ => ok s
        end.

      Variable T : Type.
      Variable getE : T -> expr (type tsym Kstar) sym.

      Definition get_inst {n} (t : polymorphic (type tsym) n T)
                 (w : expr (type tsym Kstar) sym)
      : option (hlist (type tsym) n) :=
        let t' := inst t (build_vars 1 n) in
        get_types (getE t') w (pmap_empty _)
                  (get_vars 1 Some None)
                  None.

    End with_symbol_unify.

    Definition unify_sym_by_type {T} (a b : sym)
               (s : pmap { n : kind & type tsym n })
               (ok : pmap { n : kind & type tsym n } -> T)
               (bad : T) : T :=
      match typeof_sym a
          , typeof_sym b
      with
      | Some ta , Some tb =>
        match type_unify _ _ ta tb s with
        | Some s' => ok s'
        | None => bad
        end
      | _ , _ => bad
      end.

  End with_symbols.

End PolyInst.