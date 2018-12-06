Require Import MirrorCore.Types.ModularTypesT.

Section sum.
  Variable kind : Set.
  Variable kindD : kind -> Type@{Ukind}.
  Variable T U : kind -> Set.
  Inductive tsym_sum (n : kind) : Set :=
  | TSym_left : T n -> tsym_sum n
  | TSym_right : U n -> tsym_sum n.

  Variable TSym_T : TSym kindD T.
  Variable TSym_U : TSym kindD U.

  Instance TSym_sum : TSym kindD tsym_sum :=
  { symbolD := fun n x =>
                 match x in tsym_sum _ return kindD n with
                 | TSym_left _ x => TSym_T.(@symbolD _ _ _) _ x
                 | TSym_right _ x => TSym_U.(@symbolD _ _ _) _ x
                 end
  ; symbol_dec := fun n x y =>
                    match x as x , y as y
                          return {x = y} + {x <> y}
                    with
                    | TSym_left _ x , TSym_left _ y =>
                      match TSym_T.(@symbol_dec _ _ _) _ x y with
                      | left pf => left match pf with eq_refl => eq_refl end
                      | right pf => right (fun _ => _)
                      end
                    | TSym_right _ x , TSym_right _ y =>
                      match TSym_U.(@symbol_dec _ _ _) _ x y with
                      | left pf => left match pf with eq_refl => eq_refl end
                      | right pf => right (fun _ => _)
                      end
                    | TSym_right _ x , TSym_left _ y =>
                      right (fun _ => _)
                    | TSym_left _ x , TSym_right _ y =>
                      right (fun _ => _)
                    end
  }.
  all: congruence.
  Defined.
End sum.