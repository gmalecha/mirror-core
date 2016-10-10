Require Import McExamples.PolyRewrite.QuantifierPuller.LtacDemo.

3Declare Module M : Monoid.Monoid.

Module Automation := LtacDemo.

Goal Automation.Demo.goal NNN.
  Automation.Demo.prep.
  Time Automation.ltac_canceler.
Time Qed.