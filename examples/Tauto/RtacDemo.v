Require Import McExamples.Tauto.Tauto.

Module Demo.
  Ltac prep := unfold
    mkBigTerm, mkTerm, mkForalls, mkForalls_aux, mkImpls, mkAnds.

  Ltac run := the_tac.
  Ltac cleanup := idtac.
  
  Definition goal := fun n => ILogic.lentails ILogic.ltrue (mkBigTerm 2 n).
End Demo.