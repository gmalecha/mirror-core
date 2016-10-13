(* First-cut of work on VST reification *)
(* TODO: get the relevant parts of VST imported
   (I guess, see what Joey's mc_reify does) *)

(* from my bedrock stuff *)
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.CTypes.ModularTypes.
Require Import MirrorCore.CTypes.TSymOneOf.

(* from Joey's stuff (floyd_funcs.v)
   looks as though a couple things
   in Floyd are missing though
   (renamed?)
 *)
Require Import MirrorCore.Lambda.ExprCore.
(* need to qualify this import *)
(*Require Import floyd_funcs.*)
Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.TypesI.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.Fun.
(*Require Import progs.list_dt. *)
Require Import Coq.FSets.FMapPositive.
Require Export veric.expr.
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.common.Values.
Require Export msl.shares.
Require Export compcert.common.AST.
Require Export compcert.lib.Integers.
Require Export Coq.ZArith.BinInt.
Require Export compcert.lib.Floats.
Require Export veric.juicy_extspec.
Require Export compcert.cfrontend.Clight.
Require Export veric.seplog.
Require Export floyd.nested_field_lemmas.
Require Export floyd.efield_lemmas.
(*Require Export floyd.type_id_env.*)
Require Export compcert.cfrontend.Cop.
(*Require Export floyd.data_at_lemmas.*)
Require Export veric.SeparationLogic.
Require Export floyd.field_at.
Require Export floyd.sc_set_load_store.
Require veric.SeparationLogicSoundness.
Require Import veric.tycontext.
Require Import veric.semax.
Require Import floyd.local2ptree.



(* TODO: Perhaps name this better. *)
Inductive typ' : nat -> Type :=
| tyMpred : typ' 0
| tyList : typ' 1
(* todo - add to this list as needed *)
.

Import ListNotations.
Locate assertD.

Let _p := 1%positive.

(* remove_global_spec is one of Joey's things *)
(* more dependencies for our first goal *)

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.


(* mc_reify.symexe.v *)
Locate remove_global_spec.
SearchAbout tycontext.

(* from reverse_defs.v *)
(* These seem too complicated.
   Let's learn to create a minimal
   one from test_semax.v *)
Definition Delta : tycontext := 
mk_tycontext
             (PTree.Node
                (PTree.Node PTree.Leaf None
                   (PTree.Node
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (tptr t_struct_list, false)) PTree.Leaf)
                            None PTree.Leaf)) None PTree.Leaf)) None
                (PTree.Node
                   (PTree.Node PTree.Leaf None
                      (PTree.Node
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (tptr t_struct_list, true)) PTree.Leaf)
                            None PTree.Leaf) None PTree.Leaf)) None
                   (PTree.Node
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (tptr t_struct_list, true)) PTree.Leaf)
                            None PTree.Leaf)) None
                      (PTree.Node
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (tptr t_struct_list, false)) PTree.Leaf)
                            None PTree.Leaf) None PTree.Leaf))))
             (PTree.empty type) (tptr t_struct_list)
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf None
                      (PTree.Node
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (Tarray t_struct_list 3 noattr))
                               PTree.Leaf) None PTree.Leaf) None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some
                                  (Tfunction
                                     (Tcons (tptr t_struct_list) Tnil)
                                     (tptr t_struct_list) cc_default))
                               PTree.Leaf) None PTree.Leaf))) None
                   (PTree.Node PTree.Leaf None
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some (Tfunction Tnil tint cc_default))
                               PTree.Leaf) None PTree.Leaf)))) None
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some
                                  (Tfunction
                                     (Tcons (tptr t_struct_list) Tnil) tint
                                     cc_default)) PTree.Leaf) None PTree.Leaf))
                      None PTree.Leaf) None PTree.Leaf))
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf None
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some
                                  (WITH x : share * list val * val PRE 
                                   [(_p, tptr t_struct_list)]
                                   (let (p0, p1) := x in
                                    let (sh0, contents0) := p0 in
                                    PROP  (writable_share sh0)
                                    LOCAL  (temp _p p1)
                                    SEP 
                                    (`(lseg LS sh0 contents0 p1 nullval)))
                                   POST  [tptr t_struct_list]
                                   (let (p0, _) := x in
                                    let (sh0, contents0) := p0 in
                                    `(lseg LS sh0 (rev contents0)) retval
                                      `nullval))) PTree.Leaf) None PTree.Leaf)))
                   None
                   (PTree.Node PTree.Leaf None
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some
                                  (WITH u : unit PRE  []
                                   main_pre prog u POST  [tint]
                                   main_post prog u)) PTree.Leaf) None
                            PTree.Leaf)))) None
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf None
                         (PTree.Node
                            (PTree.Node PTree.Leaf
                               (Some
                                  (WITH x : share * list int * val PRE 
                                   [(_p, tptr t_struct_list)]
                                   (let (p0, p1) := x in
                                    let (sh0, contents0) := p0 in
                                    PROP  (* () *)
                                    LOCAL  (temp _p p1)
                                    SEP 
                                    (`(lseg LS sh0 
                                         (map Vint contents0) p1 nullval)))
                                   POST  [tint]
                                   (let (p0, _) := x in
                                    let (_, contents0) := p0 in
                                    local
                                      (`(eq (Vint (sum_int contents0)))
                                         retval)))) PTree.Leaf) None
                            PTree.Leaf)) None PTree.Leaf) None PTree.Leaf)).

Definition Struct_env := (@PTree.Node type (@PTree.Leaf type) 
                     (@None type)
                     (@PTree.Node type
                        (@PTree.Node type
                           (@PTree.Node type
                              (@PTree.Node type
                                 (@PTree.Node type 
                                    (@PTree.Leaf type)
                                    (@Some type
                                       (Tstruct _struct_list
                                          (Fcons _head tint
                                             (Fcons _tail
                                                (Tcomp_ptr _struct_list
                                                  noattr) Fnil)) noattr))
                                    (@PTree.Leaf type)) 
                                 (@None type) (@PTree.Leaf type))
                              (@None type) (@PTree.Leaf type)) 
                           (@None type) (@PTree.Leaf type)) 
                        (@None type) (@PTree.Leaf type))).


Goal
forall {Espec : OracleKind} (contents : list val),
(semax
(remove_global_spec Delta) (*empty_tycontext*)
(assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
(Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
(normal_ret_assert (assertD [] (localD (PTree.set _p (Values.Vint Int.zero) (PTree.empty val)) (PTree.empty (type * val))) []))).


(* Joey's suggested first example. Just a single set *)
(* _p should be a positive number. it may be that any would work. *)
(*
Goal
forall {Espec : OracleKind} (contents : list val),
(semax
(remove_global_spec Delta) (*empty_tycontext*)
(assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
(Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
(normal_ret_assert (assertD [] (localD (PTree.set _p (Values.Vint Int.zero) (PTree.empty val)) (PTree.empty (type * val))) []))).
intros.
unfold empty_tycontext, Delta, remove_global_spec.
rforward.
intros.
apply derives_refl.
Qed.
*)

(* look at Joey's mc_reify/types *)
(* here are Joey's types and denotation code *)
Inductive typ :=
| tyArr : typ -> typ -> typ
| tytycontext
| tyc_expr
| tyc_type
| tyenviron
| tyval
| tyshare
| tyident
| tylist : typ -> typ
| tyint
| tyZ
| tynat
| typositive
| tybool
| tycomparison
| tytc_assert
| tyint64
| tyfloat
| tyfloat32
| tyattr
| tysignedness
| tyintsize
| tyfloatsize
| tytypelist
| tyfieldlist
| tybinary_operation
| tyunary_operation
| tyN
| tyoption : typ -> typ
| typrop
| tympred
| tysum : typ -> typ -> typ
| typrod : typ -> typ -> typ
| tyunit
(*| tylistspec : type -> ident -> typ*)
| tyOracleKind
| tystatement
| tyret_assert
| tyexitkind
| typtree : typ -> typ
| tygfield
| tyfunspec
| tyefield
| tytype_id_env
| tyllrr
(*| tyother : positive -> typ*)
.

Fixpoint typD (t : typ) (*(m : PositiveMap.t Type)*): Type :=
    match t with
        | tyArr a b => typD a  -> typD b 
        | tytycontext => tycontext
        | tyc_expr => expr
        | tyc_type => type
        | tyenviron => environ
        | tyval => val
        | tyshare => share
        | tyident => ident
        | tylist t => list (typD t )
        | tyint => int
        | tyZ => Z
        | tynat => nat
        | typositive => positive
        | tybool => bool
        | tycomparison => comparison
        | tytc_assert => tc_assert
        | tyint64 => int64
        | tyfloat => float
        | tyfloat32 => float32
        | tyattr => attr
        | tysignedness => signedness
        | tyintsize => intsize
        | tyfloatsize  => floatsize
        | tytypelist => typelist
        | tyfieldlist => fieldlist
        | tybinary_operation => Cop.binary_operation
        | tyunary_operation => Cop.unary_operation
        | tyN => N
        | tyoption t => option (typD t )
        | typrop => Prop
        | tympred => mpred
        | tysum t1 t2 => sum (typD  t1 ) (typD  t2 )
        | typrod t1 t2 => prod (typD  t1 ) (typD  t2 )
        | tyunit => unit
        (*| tylistspec t i => listspec t i *)
        | tyOracleKind => OracleKind
        | tystatement => statement
        | tyret_assert => ret_assert
(*        | tyother p => PositiveMap.find p m *)
        | tyexitkind => exitkind
        | typtree t => PTree.t (typD t)
        | tygfield => gfield
        | tyfunspec => funspec
        | tyefield => efield
        | tytype_id_env => type_id_env
        | tyllrr => LLRR
    end.
