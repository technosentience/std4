/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.MLList.IO
import Std.Data.List.Basic

/-!
# Parallelization in Lean's tactic monads.

`MetaM.runGreedily` will run a list of `MetaM α` in parallel, returning
* a cancellation hook and
* an `MLList MetaM α` that returns the results (and the relevant `MetaM` state)
  in the order that they finish.

After calling the cancellation hook the behaviour of the monadic lazy list should not be relied on.
It may continue returning values, or fail.
Recommended usage is to take a prefix of the list
(e.g. with `MLList.takeUpToFirst` followed by `MLList.force`, or `MLList.takeAsList`)
and then call the cancellation hook to request cancellation of later unwanted tasks.

(Similarly also for `CoreM`, `TermElabM`, and `TacticM`.)

## Implementation notes:
We have not thoroughly tested this approach to parallelization,
and remain concerned that in some applications tasks may get stuck waiting for each other.
This is currently used to implement parallelization for the `hint` tactic.
We recommend using this elsewhere only with caution,
and particular caution combining it with other code that manipulates tasks!

Thomas Murrills has a suggestion to significantly refactor this code,
reducing duplication using `MonadControl`, but it will require a core change.
See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60StateRefT'.60.20.60MonadControl.60.20instance.3F
-/

set_option autoImplicit true

namespace IO

/--
Given a list of values in `IO α`, executes them all in parallel as tasks, and returns
* a cancellation hook and
* a monadic lazy list which returns the values in the order they complete.

Note that the cancellation hook merely requests cooperative cancellation:
the tasks must call `IO.checkCanceled` themselves.
The tactic framework does so automatically,
at the same time it checks for exceeding `maxHeartbeats`.

After calling the cancellation hook the behaviour of the monadic lazy list should not be relied on.
It may continue returning values, or fail.
Recommended usage is to take a prefix of the list
(e.g. with `MLList.takeUpToFirst` followed by `MLList.force`, or `MLList.takeAsList`)
and then call the cancellation hook to request cancellation of later unwanted tasks.
-/
def runGreedily (tasks : List (IO α)) : BaseIO (BaseIO Unit × MLList IO α) := do
  let t ← tasks.mapM IO.asTask
  return (t.forM cancel, MLList.ofTaskListM t fun
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{e}"))

/--
Variant of `IO.runGreedily` without a cancellation hook.
-/
def runGreedily' (tasks : List (IO α)) : MLList IO α :=
  .squash fun _ => (·.2) <$> runGreedily tasks

end IO

namespace Lean

/--
Given a backtrackable monad with exception.  This restores the state and extracts
a value from a paused computation.  It throws the exception if present.
-/
def resumeSavedState [Functor m] [MonadBacktrack s m] [MonadExcept ε m] : Except ε (α × s) → m α
| .ok (a, s) => Functor.mapConst a (restoreState s)
| .error e => throw e

namespace Core.CoreM

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asEIO (t : CoreM α) : CoreM (EIO Exception α) := do
  pure <| (t.run' (← read) (← get))

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning a value with the result.
-/
def asTask (t : CoreM α) : CoreM (Task (Except Exception (α × Core.State))) := do
  (← (Prod.mk <$> t <*> get).asEIO).asTask

/--
Given a list of monadic values in `CoreM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (CoreM α)) : CoreM (BaseIO Unit × MLList CoreM α) := do
  let tasks := ← jobs.mapM asTask
  return (tasks.forM IO.cancel, MLList.ofTaskListM tasks fun
    | .ok (a, s) => set s *> pure a
    | .error e => throw e)

/--
Variant of `CoreM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (CoreM α)) : MLList CoreM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Use the current context and state to return an Core action that runs the computation.
-/
def asCore (act : MetaM α) : MetaM (CoreM α) := (act.run' · ·) <$> read <*> get

/--
Use the current context and state to return an EIO action that runs the computation.
-/
def asEIO (m : MetaM α) : MetaM (EIO Exception α) := m.asCore >>= (·.asEIO)

/--
Given a Meta computation create a task that runs it and returns the result.
-/
def asTask (m : MetaM α) : MetaM (Task (Except Exception (α × Meta.SavedState))) := do
  let act := Prod.mk <$> m <*> saveState
  act.asEIO >>= (·.asTask)


/--
Given a list of monadic values in `MetaM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (MetaM α)) : MetaM (BaseIO Unit × MLList MetaM α) := do
  let tasks ← jobs.mapM asTask
  return (tasks.forM IO.cancel, MLList.ofTaskListM tasks resumeSavedState)

/--
Variant of `MetaM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (MetaM α)) : MLList MetaM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs


end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Use the current context and state to return an @MetaM@ action that runs the computation.
-/
def asMeta (act : TermElabM α) : TermElabM (MetaM α) := (act.run' · ·) <$> read <*> get

/--
Use the current context and state to return an EIO action that runs the computation.
-/
def asEIO (act : TermElabM α) : TermElabM (EIO Exception α) := act.asMeta >>= (·.asEIO)

/--
Given a Meta computation create a task that runs it and returns the result.
-/
def asTask (m : TermElabM α) : TermElabM (Task (Except Exception (α × Term.SavedState))) := do
  let act := Prod.mk <$> m <*> saveState
  act.asEIO >>= (·.asTask)

/--
Given a list of monadic values in `TermElabM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (TermElabM α)) : TermElabM (BaseIO Unit × MLList TermElabM α) := do
  let tasks ← jobs.mapM asTask
  return (tasks.forM IO.cancel, MLList.ofTaskListM tasks resumeSavedState)

/--
Variant of `TermElabM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (TermElabM α)) : MLList TermElabM α :=
  .squash fun _ => (·.2) <$> runGreedily jobs

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Use the current context and state to return an @MetaM@ action that runs the computation.
-/
def asTermElab (act : TacticM α) : TacticM (TermElabM α) := do
  pure <| (act.run (←read)).run' (←get)

/--
Use the current context and state to return an EIO action that runs the computation.
-/
def asEIO (act : TacticM α) : TacticM (EIO Exception α) := act.asTermElab >>= (·.asEIO)

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (m : TacticM α) : TacticM (Task (Except Exception (α × Tactic.SavedState))) := do
  let act := Prod.mk <$> m <*> saveState
  act.asEIO >>= (·.asTask)

/--
Given a list of monadic values in `TacticM`, runs them all as tasks,
and returns
* a cancellation hook and
* the monadic lazy list which returns the values in the order they complete.

See the doc-string for `IO.runGreedily` for details about the cancellation hook behaviour.
-/
def runGreedily (jobs : List (TacticM α)) : TacticM (BaseIO Unit × MLList TacticM α) := do
  let tasks ← jobs.mapM asTask
  return (tasks.forM IO.cancel, MLList.ofTaskListM tasks resumeSavedState)

/--
Variant of `TacticM.runGreedily` without a cancellation hook.
-/
def runGreedily' (jobs : List (TacticM α)) : MLList TacticM α :=
  .squash fun _ => Prod.snd <$> runGreedily jobs

end Lean.Elab.Tactic.TacticM
