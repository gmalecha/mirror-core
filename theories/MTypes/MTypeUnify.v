Require Import MirrorCore.MTypes.ModularTypes.
Require Import ExtLib.Data.Map.FMapPositive.

Section parametric.
  Variable tsym : nat -> Type.

  Let S := FMapPositive.pmap (mtyp tsym).
  Let add : positive -> mtyp tsym -> S -> option S := (fun a b c => Some (FMapPositive.pmap_insert a b c)).

  (** This is asymmetric, the first argument is the "special one" **)
  Fixpoint mtype_unify (a b : mtyp tsym) (s : pmap (mtyp tsym)) {struct a}
  : option S :=
    match a with
    | tyArr da ca =>
      match b with
      | tyArr db cb =>
        match mtype_unify da db s with
        | Some s' => mtype_unify ca cb s'
        | _ => None
        end
      | tyVar v => add v a s
      | _ => None
      end
    | tyBase0 _ =>
      match b with
      | tyBase0 _ => Some s
      | tyVar v => add v a s
      | _ => None
      end
    | tyBase1 _ ta =>
      match b with
      | tyBase1 _ tb => mtype_unify ta tb s
      | tyVar v => add v a s
      | _ => None
      end
    | tyBase2 _ ta ta' =>
      match b with
      | tyBase2 _ tb tb' =>
        match mtype_unify ta tb s with
        | Some s' => mtype_unify ta' tb' s'
        | _ => None
        end
      | tyVar v => add v a s
      | _ => None
      end
    | tyApp _ va =>
      match b with
      | tyApp _ vb =>
        (fix go n n' (va : Vector.vector _ n) (vb : Vector.vector _ n') (s : S)
         : option S :=
           match va , vb with
           | Vector.Vnil _ , Vector.Vnil _ => Some s
           | Vector.Vcons a va , Vector.Vcons b vb =>
             match mtype_unify a b s with
             | Some s' => go _ _ va vb s'
             | _ => None
             end
           | _ , _ => None
           end) _ _ va vb s
      | tyVar v => add v a s
      | _ => None
      end
    | tyProp => match b with
                | tyProp => Some s
                | tyVar v => add v a s
                | _ => None
                end
    | tyVar v => add v b s
    end.

End parametric.
