Require Import McExamples.PolyRewrite.QuantifierPuller.LtacDemo.

Module Automation := LtacDemo.

Goal Automation.Demo.goal 3 (*NNN*).
  Automation.Demo.prep.
  Time Automation.Demo.run.
  Automation.Demo.cleanup.
Time Qed.