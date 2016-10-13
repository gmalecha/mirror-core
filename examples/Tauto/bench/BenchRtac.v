Require Import McExamples.Tauto.DemoRtac.

Module Automation := RtacDemo.

Goal Automation.Demo.goal NNN.
  Automation.Demo.prep.
  Time Automation.Demo.run.
  Automation.Demo.cleanup.
Time Qed.
