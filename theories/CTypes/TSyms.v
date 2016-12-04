Require Import MirrorCore.CTypes.CoreTypes.

Section sum.
  Variable T U : nat -> Set.
  Inductive tsym_sum (n : nat) : Set :=
  | TSym_left : T n -> tsym_sum n
  | TSym_right : U n -> tsym_sum n.

  Variable TSym_T : TSym T.
  Variable TSym_U : TSym U.
 
  Instance TSym_sum : TSym tsym_sum :=
  { symbolD := fun n x =>
                 match x in tsym_sum _ return type_for_arity n with
                 | TSym_left _ x => TSym_T.(@symbolD _) _ x
                 | TSym_right _ x => TSym_U.(@symbolD _) _ x
                 end
  ; symbol_dec := fun n x y =>
                    match x as x , y as y
                          return {x = y} + {x <> y}
                    with
                    | TSym_left _ x , TSym_left _ y =>
                      match TSym_T.(@symbol_dec _) _ x y with
                      | left pf => left match pf with eq_refl => eq_refl end
                      | right pf => right (fun _ => _)
                      end
                    | TSym_right _ x , TSym_right _ y =>
                      match TSym_U.(@symbol_dec _) _ x y with
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
