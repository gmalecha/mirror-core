Require Import McExamples.Cancel.RtacDemo.

Declare Module M : Monoid.Monoid.

Module Automation := RtacDemo.MonoidCancel M.

Goal Automation.Demo.goal NNN.
  Automation.Demo.prep.
  Time Automation.rtac_canceler.
Time Qed.
