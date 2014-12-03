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
Require Export MirrorCore.RTac.ThenK.
Require Export MirrorCore.RTac.Minify.
(*Require Export MirrorCore.RTac.RunSTac.*)
Require Export MirrorCore.RTac.AtGoal.

Ltac rtac_derive_soundness :=
  repeat first [ eapply IDTAC_sound
               | eapply FAIL_sound
               | eapply FIRST_sound ; Forall_rtac_derive_soundness
               | eapply SOLVE_sound ; rtac_derive_soundness
               | eapply THEN_sound ;
                 [ rtac_derive_soundness
                 | rtacK_derive_soundness ]
               | eapply TRY_sound ; rtac_derive_soundness
               | eapply REPEAT_sound ; rtac_derive_soundness
               | eapply AT_GOAL_sound ; [ intros ; rtac_derive_soundness ]
               | eapply APPLY_sound ; [ simpl ] (* TODO(gmalecha): Needs to change *)
               | eapply EAPPLY_sound ; [ simpl ]  (* TODO(gmalecha): Needs to change *)
               ]
with rtacK_derive_soundness :=
  first [ eauto
        | eapply runOnGoals_sound ; rtac_derive_soundness
        ]
with Forall_rtac_derive_soundness :=
  repeat first [ eauto
               | eapply Forall_nil
               | eapply Forall_cons ;
                 [ rtac_derive_soundness
                 | Forall_rtac_derive_soundness ] ].

Ltac rtac_derive_soundness_wrapper :=
  match goal with
    | |- rtacK_sound _ _ _ => rtacK_derive_soundness
    | |- rtac_sound _ _ _ => rtac_derive_soundness
  end.

Tactic Notation "'derive' 'soundness'" := rtac_derive_soundness_wrapper.