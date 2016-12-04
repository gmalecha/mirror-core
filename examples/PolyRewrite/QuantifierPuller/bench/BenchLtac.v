Require Import McExamples.PolyRewrite.QuantifierPuller.LtacDemo.

Module Automation := LtacDemo.

Goal Automation.Demo.goal NNN.
  Automation.Demo.prep.
  Time (timeout 240 Automation.Demo.run).
  Automation.Demo.cleanup.
Time Qed.