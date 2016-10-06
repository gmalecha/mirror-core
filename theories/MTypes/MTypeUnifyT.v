Require Import MirrorCore.MTypes.ModularTypesT.
Require Import MirrorCore.Util.PositivePolyMap.


Module Type TypeLangUnify.
  Declare Module RT : TypeLang.
  Import RT.

  Section with_symbols.
    Variable symbol : kind -> Type.

    Parameter type_unify : forall k, type symbol k -> type symbol k ->
                           pmap { k : kind & type symbol k } ->
                           option (pmap { k : kind & type symbol k }).
  End with_symbols.
End TypeLangUnify.

Module TypeLangUnify_mtyp <: TypeLangUnify with Module RT := TypeLang_mtyp.
  Module RT := TypeLang_mtyp.
  Import RT.

  Section with_symbols.
    Variable tsym : kind -> Type.

    Definition Sub := pmap { k : kind & type tsym k }.
    Definition add {n} (a :  positive) (b : type tsym n) (c : Sub)
    : option Sub := Some (pmap_insert a c (@existT _ _ n b)).

    Fixpoint type_unify {k} (a b : type tsym k) (s : Sub) {struct a}
    : option Sub :=
      match a with
      | @tyArr _ da ca =>
        match b with
        | @tyArr _ db cb =>
          match type_unify da db s with
          | Some s' => type_unify ca cb s'
          | _ => None
          end
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase0 _ _ =>
        match b with
        | @tyBase0 _ _ => Some s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase1 _ _ ta =>
        match b with
        | @tyBase1 _ _ tb => type_unify ta tb s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyBase2 _ _ ta ta' =>
        match b with
        | @tyBase2 _ _ tb tb' =>
          match type_unify ta tb s with
          | Some s' => type_unify ta' tb' s'
          | _ => None
          end
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyApp _ _ _ va =>
        match b with
        | @tyApp _ _ _ vb =>
          (fix go n n' (va : Vector.vector _ n) (vb : Vector.vector _ n') (s : Sub)
           : option Sub :=
             match va , vb with
             | Vector.Vnil _ , Vector.Vnil _ => Some s
             | Vector.Vcons a va , Vector.Vcons b vb =>
               match type_unify a b s with
               | Some s' => go _ _ va vb s'
               | _ => None
               end
             | _ , _ => None
             end) _ _ va vb s
        | @tyVar' _ _ v => add v a s
        | _ => None
        end
      | @tyProp _ => match b with
                 | @tyProp _ => Some s
                 | @tyVar' _ _ v => add v a s
                 | _ => None
                 end
      | @tyVar' _ _ v =>
        match b with
        | @tyVar' _ _ v' => Some s
        | _ => add v b s
        end
      end.

  End with_symbols.

End TypeLangUnify_mtyp.

Module TypeLangUnify_mtypF <: TypeLangUnify with Module RT := TypeLang_mtypF.
  Module RT := TypeLang_mtypF.
  Import RT.

  Section with_symbols.
    Variable tsym : kind -> Type.

    Definition Sub := pmap { k : kind & type tsym k }.
    Definition add {n} (a :  positive) (b : type tsym n) (c : Sub)
    : option Sub := Some (pmap_insert a c (@existT _ _ n b)).

    (** This is asymmetric, the first argument is the "special one" **)
    Fixpoint type_unify {n} (a b : mtyp tsym n)
             (s : Sub) {struct a}
    : option Sub :=
      match a in mtyp _ n return mtyp tsym n -> option _ with
      | tyArr da ca => fun b =>
        match b in mtyp _ n'
              return (mtyp tsym n' -> _ -> option _) ->
                     (mtyp tsym n' -> _ -> option _) ->
                     option _
        with
        | tyArr db cb => fun rec1 rec2 =>
                          match rec1 db s with
                          | Some s' => rec2 cb s'
                          | _ => None
                          end
        | _ => fun _ _ => None
        end (fun b => type_unify da b) (fun b => type_unify ca b)
      | @tyApp _ d c da ca => fun b =>
        match b in mtyp _ n'
              return (mtyp tsym (Karr d n') -> Sub -> option Sub) ->
                     (mtyp tsym d -> Sub -> option Sub) ->
                     option _
        with
        | @tyApp _ d' _ db cb =>
          match kind_eq_dec d' d with
          | left pf => match pf with
                      | eq_refl =>
                        fun rec1 rec2 =>
                          match rec1 db s with
                          | Some s' => rec2 cb s'
                          | _ => None
                          end
                      end
          | right _ => fun _ _ => None
          end
        | _ => fun _ _ => None
        end (fun b => type_unify da b) (fun b => type_unify ca b)
      | @tyInj _ n sy => fun b =>
        match b in mtyp _ n' return tsym n' -> option Sub with
        | tyInj _ sy' => fun sy =>
                          Some s
        | _ => fun _ => None
        end sy
      | tyProp => fun b =>
                   match b with
                   | tyProp => Some s
                   | _ => None
                   end
      | @tyVar' _ n v => fun b => add v b s
      end b.

  End with_symbols.

End TypeLangUnify_mtypF.
