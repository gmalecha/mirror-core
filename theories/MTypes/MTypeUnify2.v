Require Import MirrorCore.MTypes.ModularTypes2.
Require Import MirrorCore.Util.PositivePolyMap.

Section parametric.
  Variable tsym : nat -> Type.
  Variable TSym_tsym : TSym tsym.

  Let Sub := pmap { n : nat & mtyp tsym n}.
  Definition add : forall n, positive -> mtyp tsym n -> Sub -> option Sub.
  refine
    (fun n a b c => Some (pmap_insert a c (@existT _ _ n b))).
  Defined.

  (** This is asymmetric, the first argument is the "special one" **)
  Fixpoint mtype_unify {n} (a b : mtyp tsym n) (s : Sub) {struct a}
  : option Sub.
  refine
    (match a in mtyp _ n return mtyp tsym n -> option Sub with
     | tyArr da ca => fun b =>
       match b in mtyp _ n'
             return (mtyp tsym n' -> Sub -> option Sub) ->
                    (mtyp tsym n' -> Sub -> option Sub) ->
                    option Sub
       with
       | tyArr db cb => fun rec1 rec2 =>
         match rec1 db s with
         | Some s' => rec2 cb s'
         | _ => None
         end
       | _ => fun _ _ => None
       end (fun b => mtype_unify _ da b) (fun b => mtype_unify _ ca b)
     | @tyApp _ n da ca => fun b =>
       match b in mtyp _ n'
             return (mtyp tsym (S n') -> Sub -> option Sub) ->
                    (mtyp tsym 0 -> Sub -> option Sub) ->
                    option Sub
       with
       | tyApp db cb => fun rec1 rec2 =>
         match rec1 db s with
         | Some s' => rec2 cb s'
         | _ => None
         end
       | _ => fun _ _ => None
       end (fun b => mtype_unify _ da b) (fun b => mtype_unify _ ca b)
     | @tyInj _ n sy => fun b =>
       match b in mtyp _ n' return tsym n' -> option Sub with
       | tyInj _ sy' => fun sy =>
         match symbol_dec sy sy' with
         | left _ => Some s
         | _ => None
         end
       | _ => fun _ => None
       end sy
     | tyProp => fun b =>
       match b with
       | tyProp => Some s
       | _ => None
       end
    | @tyVar _ n v => fun b => add n v b s
    end b).
  Defined.

End parametric.
