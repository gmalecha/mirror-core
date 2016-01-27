Require Import McExamples.Cancel.LtacDemo.

Goal Lang.goal NNN.
  Lang.prep.
  Time ltac_canceler.
Time Qed.