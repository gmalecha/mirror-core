Require Import McExamples.PolyRewrite.Monads.Monad.
Require Import McExamples.PolyRewrite.Monads.LtacDemo.

Declare Module M : Monad.Monad.
Declare Module F : Frob M.

Module Automation := LtacDemo.TheMonad M F.
Goal Automation.Demo.goal NNN .
  Automation.Demo.prep.
  Time Automation.Demo.run.
  Automation.Demo.cleanup.
Time Qed.