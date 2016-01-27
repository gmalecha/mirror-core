Require Import McExamples.Cancel.RtacDemo.

Goal Lang.goal NNN.
  Lang.prep.
  Time rtac_canceler.
Time Qed.
