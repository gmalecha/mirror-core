Require Import McExamples.Tauto.LtacDemo.

Module Automation := LtacDemo.

Goal Automation.Demo.goal NNN.
  unfold Automation.Demo.goal.
  Automation.Demo.prep.
  Time Automation.Demo.run.
Time Qed.