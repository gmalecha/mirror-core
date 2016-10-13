Require Import MirrorCore.CTypes.CoreTypes.
Require Import ExtLib.Data.Map.FMapPositive.

Section parametric.
  Variable tsym : nat -> Type.
  Variable TSym_tsym : TSym tsym.

  Let FM := FMapPositive.pmap (ctyp tsym).
  Let add : positive -> ctyp tsym -> FM -> option FM := (fun a b c => Some (FMapPositive.pmap_insert a b c)).

  (** This is asymmetric, the first argument is the "special one" **)
  (* n tracks how many variables are left to instantiate, so we
     can terminate early. *)
  Fixpoint ctype_unify (n : nat) (a b : ctyp tsym) (s : FM) {struct a}
    : option (FM * nat) :=
    match n with
    | 0 => Some (s, 0)
    | S npred =>
      match a with
      | tyArr da ca =>
        match b with
        | tyArr db cb =>
          match ctype_unify n da db s with
          | Some (s', S k) => ctype_unify (S k) ca cb s'
          | Some (s', 0) => Some (s', 0)
          | _ => None
          end
        | tyVar v =>
          match add v a s with
          | Some s' => Some (s', npred)
          | _ => None
          end
        | _ => None
        end
      | tyBase0 _ =>
        match b with
        | tyBase0 _ => Some (s, n)
        | tyVar v =>
          match add v a s with
          | Some s' => Some (s', npred)
          | _ => None
          end
        | _ => None
        end
      | tyBase1 _ ta =>
        match b with
        | tyBase1 _ tb => ctype_unify n ta tb s
        | tyVar v =>
          match add v a s with
          | Some s' => Some (s', npred)
          | _ => None
          end
        | _ => None
        end
      | tyBase2 _ ta ta' =>
        match b with
        | tyBase2 _ tb tb' =>
          match ctype_unify n ta tb s with
          | Some (s', S k) => ctype_unify (S k) ta' tb' s'
          | Some (s', 0) => Some (s', 0)
          | _ => None
          end
        | tyVar v =>
          match add v a s with
          | Some s' => Some (s', npred)
          | _ => None
          end
        | _ => None
        end
      | tyApp _ va =>
        match b with
        | tyApp _ vb =>
          (* n is the number of variables to instantiate.
             vl, vl' are vector lengths *)
          (fix go n vl vl' (va : Vector.vector _ vl) (vb : Vector.vector _ vl') (s : FM)
           : option (FM * nat) :=
             match va , vb with
             | Vector.Vnil _ , Vector.Vnil _ => Some (s, n)
             | Vector.Vcons a va , Vector.Vcons b vb =>
               match ctype_unify n a b s with
               | Some (s', S k) => go (S k) _ _ va vb s'
               | Some (s', 0) => Some (s', 0)
               | _ => None
               end
             | _ , _ => None
             end) n _ _ va vb s
        | tyVar v =>
          match add v a s with
          | Some s' => Some (s', npred)
          | _ => None
          end
        | _ => None
        end
      | tyProp => match b with
                 | tyProp => Some (s, n)
                 | tyVar v =>
                   match add v a s with
                   | Some s' => Some (s', npred)
                   | _ => None
                   end
                 | _ => None
                 end
      | tyVar v =>
        match add v b s with
        | Some s' => Some (s', npred)
        | _ => None
        end
      end
    end.

  (* slower version we use when we don't know how many variables
     we are trying to instantiate *)
  Fixpoint ctype_unify_slow (a b : ctyp tsym) (s : pmap (ctyp tsym)) {struct a}
  : option FM :=
    match a with
    | tyArr da ca =>
      match b with
      | tyArr db cb =>
        match ctype_unify_slow da db s with
        | Some s' => ctype_unify_slow ca cb s'
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
      | tyBase1 _ tb => ctype_unify_slow ta tb s
      | tyVar v => add v a s
      | _ => None
      end
    | tyBase2 _ ta ta' =>
      match b with
      | tyBase2 _ tb tb' =>
        match ctype_unify_slow ta tb s with
        | Some s' => ctype_unify_slow ta' tb' s'
        | _ => None
        end
      | tyVar v => add v a s
      | _ => None
      end
    | tyApp _ va =>
      match b with
      | tyApp _ vb =>
        (fix go n n' (va : Vector.vector _ n) (vb : Vector.vector _ n') (s : FM)
         : option FM :=
           match va , vb with
           | Vector.Vnil _ , Vector.Vnil _ => Some s
           | Vector.Vcons a va , Vector.Vcons b vb =>
             match ctype_unify_slow a b s with
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
  (* in the future we may want to wrap it more *)
(*  Definition ctype_unify' (n : nat) (a b : ctyp tsym) (s : FM) 
    : option FM :=
    match ctype_unify' n a b s with
    | Some (s', _) => Some s'
    | _ => None
    end. *)

End parametric.
