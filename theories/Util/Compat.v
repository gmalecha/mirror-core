Require ExtLib.Data.Option.
Require Import ExtLib.Data.Eq.

Ltac autorewrite_with_eq_rw_in H :=
  repeat progress (autorewrite with eq_rw in H ;
                   repeat match type of H with
                            | context [ match ?X return option _ with
                                          | eq_refl => _
                                        end ] =>
                              rewrite (Option.eq_option_eq X) in H
                            | context [ match ?X return _ -> _ with
                                          | eq_refl => _
                                        end ] =>
                              rewrite (eq_Arr_eq X) in H
                          end).

Ltac autorewrite_with_eq_rw :=
  repeat progress (autorewrite with eq_rw ;
                   repeat match goal with
                            | |- context [ match ?X return option _ with
                                             | eq_refl => _
                                           end ] =>
                              rewrite (Option.eq_option_eq X)
                            | |- context [ match ?X return _ -> _ with
                                             | eq_refl => _
                                           end ] =>
                              rewrite (eq_Arr_eq X)
                          end).
