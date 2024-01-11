/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Lean.System.IO
import Std.Data.MLList.Basic

/-!
# IO operations using monadic lazy lists.
-/

namespace MLList

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskList (tasks : List (Task α)) : MLList BaseIO α :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      some <$> IO.waitAny' t h
    else
      pure none

/--
Give a list of tasks, return the monadic lazy list which
returns the values as they become available.
-/
def ofTaskListM [Monad m] [MonadLiftT BaseIO m] (tasks : List (Task α)) (f : α → m β) : MLList m β :=
  fix?' (init := tasks) fun t => do
    if h : 0 < t.length then
      let (a, t) ← _root_.liftM <| IO.waitAny' t h
      pure (.some (← f a, t))
    else
      pure none
