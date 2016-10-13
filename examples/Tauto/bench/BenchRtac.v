Require Import McExamples.Tauto.RtacDemo.

Module Automation := RtacDemo.

Goal Automation.Demo.goal NNN.
  unfold Automation.Demo.goal.
  Automation.Demo.prep.
  Time Automation.Demo.run.
Time Qed.
