Require Import McExamples.Cancel.LtacDemo.

Declare Module M : Monoid.Monoid.

Module Automation := LtacDemo.Demo M.

Goal Automation.Demo.goal NNN.
  Automation.Demo.prep.
  Time Automation.ltac_canceler.
Time Qed.