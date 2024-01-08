import Lean
import Std.Lean.Name
import Std.Tactic.PrintPrefix
import Std.Data.List

open Lean
open Meta

def List.sum [Add α] [OfNat α 0] (l : List α) : α := l.foldl (·+·) (init := 0)

--@[si]

@[simp] theorem String.length_data (s:String) : s.data.length = s.length := by rfl

def checkSimp (viewOp : Name) (viewArgIdx : Nat) (ctorOp : Name) : MetaM Unit := do
  let thms ← getSimpTheorems
  let ctx : Simp.Context := { simpTheorems := #[thms] }
  withReducible $ do

  let ctorExpr ← mkConstWithFreshMVarLevels ctorOp
  let (ctorArgs, _, _ctorType) ← forallMetaTelescope (← inferType ctorExpr)
  withNewMCtxDepth do
    try
--      IO.println s!"Hello {ctorOp}"
      let viewExpr ← mkConstWithFreshMVarLevels viewOp
      let (viewArgs, _, viewType) ← forallMetaTelescope (← inferType viewExpr)
      let ctorTerm := mkAppN ctorExpr ctorArgs
      let viewArgTerm := viewArgs[viewArgIdx]!
      let eq ← isDefEq viewArgTerm ctorTerm
      if eq then
        let t := mkAppN viewExpr viewArgs
        let (_, used) ← simp t ctx
        if used.isEmpty then
          let .sort lvl ← inferType viewType
            | failure
          let rhs ← mkFreshExprMVar (.some viewType)
          let eq := mkAppN (mkConst ``Eq [lvl]) #[viewType, t, rhs]
          let t ← mkForallFVars ctorArgs eq
          --let t ← ctorArgs.foldrM (init := t) fun a b => do
          --  let m := a.mvarId!
          --  pure <| mkLambda m.name BinderInfo.default (←m.getType) b
          IO.println <| f!"Failed to simplify {←ppExpr t}".pretty
    catch _ =>
      IO.println s!"Exception with {viewOp} and {ctorOp}"

def checkMissingLemmas (viewOp : Name) (viewArgIdx : Nat) : CoreM Unit := do
  let env ← getEnv
  let .some _ := env.constants.find? viewOp
    | throwError m!"Could not find {viewOp}"
  for md in env.header.moduleData do
    for c in md.constants do
      let .defnInfo d := c
        | continue
      let blacklist : List Name := [`Lean, `Std.Tactic]
      if blacklist.any (fun nm => nm.isPrefixOf d.name) then
        continue
      if d.name.isInternalDetail then
        continue
      let ((), _) ← (checkSimp viewOp viewArgIdx d.name).run

elab "#findMissingLemmas" : command => do
  Elab.Command.liftCoreM <| checkMissingLemmas ``List.length 1

set_option maxHeartbeats 100000
set_option pp.structureProjections false
#findMissingLemmas
