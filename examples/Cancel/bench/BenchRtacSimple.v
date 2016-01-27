Require Import McExamples.Cancel.RtacDemo2.

Goal Lang.goal NNN.
  Lang.prep.
  Time rtac_canceler.
Time Qed.
