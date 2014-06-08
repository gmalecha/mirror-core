(** These should not be necessary... **)
Add ML Path "../../src".
Add ML Path "../src".

Require Import ExtLib.Structures.Monad.
Require Import MirrorCore.Examples.Monad2.MonadReify.

Section with_monad.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.

  Definition test1 : m nat := ret 0.
  Definition test2 : m nat := bind (ret 1) ret.
  Definition test3 : m nat := bind (bind test2 (fun x => ret (x + 1))) ret.
  Definition test4 : m nat := bind (ret 1) (fun x => ret x).

  Goal test4 = ret 1.
    unfold test4.
    Time (reduce_monads m).
    reflexivity.
  Qed.

  Goal (bind (ret (fun x => ret x)) (fun f => f 0)) = ret 0.
    reduce_monads m.
    reflexivity.
  Qed.

  Goal (bind (ret 1) (fun x =>
                        bind (ret (fun x => x + 0))
                             (fun f =>
                                ret (f x)))) = ret 1.
    reduce_monads m.
    reflexivity.
  Qed.

End with_monad.