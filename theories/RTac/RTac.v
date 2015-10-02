Require Export MirrorCore.RTac.Core.
Require Export MirrorCore.RTac.CoreK.

Require Export MirrorCore.RTac.Idtac.
Require Export MirrorCore.RTac.Fail.
Require Export MirrorCore.RTac.First.
Require Export MirrorCore.RTac.Solve.
Require Export MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.Repeat.
Require Export MirrorCore.RTac.Rec.
Require Export MirrorCore.RTac.Assumption.
Require Export MirrorCore.RTac.Intro.
Require Export MirrorCore.RTac.Apply.
Require Export MirrorCore.RTac.EApply.
Require Export MirrorCore.RTac.Simplify.
Require Export MirrorCore.RTac.Instantiate.

Require Export MirrorCore.RTac.RunOnGoals.
Require Export MirrorCore.RTac.RunOnGoals_list.
Require Export MirrorCore.RTac.runTacK.
Require Export MirrorCore.RTac.ThenK.
Require Export MirrorCore.RTac.IdtacK.
Require Export MirrorCore.RTac.Minify.
Require Export MirrorCore.RTac.AtGoal.

Require Export MirrorCore.RTac.Interface.

Ltac one_of lems :=
  match lems with
    | (?X,?Y) => first [ one_of X | one_of Y ]
    | _ => exact lems
  end.


Ltac rtac_derive_soundness' tac tacK lems :=
  let lems := (auto ; lems) in
  let rec rtac :=
      try first [ simple eapply IDTAC_sound
                | simple eapply FAIL_sound
                | simple eapply FIRST_sound ; Forall_rtac
                | simple eapply SOLVE_sound ; rtac
                | simple eapply THEN_sound ;
                  [ rtac
                  | rtacK ]
                | simple eapply TRY_sound ; rtac
                | simple eapply REPEAT_sound ; rtac
                | simple eapply REC_sound ; intros; rtac
                | simple eapply AT_GOAL_sound ; [ intros ; rtac ]
                | simple eapply APPLY_sound ; [ lems ]
                | simple eapply EAPPLY_sound ; [ lems ]
                | solve [ eauto with typeclass_instances ]
                | tac rtac rtacK lems
                ]
  with rtacK :=
      try first [ simple eapply runOnGoals_sound ; rtac
                | simple eapply runOnGoals_list_sound ; Forall_rtac
                | simple eapply ON_ALL_sound ; rtac
                | simple eapply ON_EACH_sound ; Forall_rtac
                | simple eapply MINIFY_sound
                | simple eapply THENK_sound ; [ try rtacK | try rtacK ]
                | solve [ eauto with typeclass_instances ]
                | tacK rtac rtacK lems
                | eapply runOnGoals_sound ; rtac
                ]
  with Forall_rtac :=
      repeat first [ eapply Forall_nil
                   | eapply Forall_cons ;
                     [ rtac
                     | Forall_rtac ]
                   | solve [ eauto ] ]
  in
  match goal with
    | |- rtac_sound _ => rtac
    | |- rtacK_sound _ => rtacK
    | |- Forall rtac_sound _ => Forall_rtac
  end.

Ltac rtac_derive_soundness_default :=
  rtac_derive_soundness' ltac:(fun rtac _ _ =>
                                 match goal with
                                   | |- rtac_sound match ?X with _ => _ end =>
                                     destruct X; rtac
                                 end)
                         ltac:(fun _ _ _ => fail)
                         ltac:(eauto with typeclass_instances).

Tactic Notation "'rtac' 'derive' 'soundness'" := rtac_derive_soundness_default.
