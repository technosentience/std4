/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Leonardo de Moura
-/

/-!
This module reintroduces the algebraic class in
@Mathlib.Init.Algebra.Classes@.  It is described in detail on [Github
wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1)
with pros and cons relevant to Lean 3.

These classes index properties by the operation rather than the type as
in Haskell.
-/

namespace Std

/-- A symmetric operation. -/
class IsSymmOp {α : Type u} {β : Sort v} (op : α → α → β) : Prop where
  /-- Symmetric operation -/
  symm_op : ∀ a b, op a b = op b a

/-- A commutative binary operation. -/
class IsCommutative {α : Type u} (op : α → α → α) : Prop where
  /-- Commutativity -/
  comm : ∀ a b, op a b = op b a

instance {α : Type _} {op : α → α → α} [IsCommutative op] : Lean.IsCommutative op where
  comm := IsCommutative.comm

instance (priority := 100) isSymmOp_of_isCommutative {α : Type u} (op : α → α → α)
    [IsCommutative op] : IsSymmOp op where symm_op := IsCommutative.comm

/-- An associative binary operation. -/
class IsAssociative {α : Type u} (op : α → α → α) : Prop where
  /-- Associativity -/
  assoc : ∀ a b c, op (op a b) c = op a (op b c)

instance {α : Type _} (op : α → α → α)  [IsAssociative op] : Lean.IsAssociative op where
  assoc := IsAssociative.assoc

/--
A binary operation with an associated identity element that can be inferred
through class inference.

This intentionally does not have associated lemmas.  For lemmas, see @IsLeftId@,
@IsRightId@ and @IsId .
 -/
class HasId {α : Type u} (op : α → α → α) (o : outParam α) : Prop

/-- A binary operation with a left identity. -/
class IsLeftId (op : α → α → α) (o : outParam α) extends HasId op o : Prop where
  /-- Left identify -/
  left_id : ∀ a, op o a = a

/-- A binary operation with a right identity. -/
class IsRightId (op : α → α → α) (o : outParam α) extends HasId op o : Prop where
  /-- Right identify -/
  right_id : ∀ a, op a o = a

/-- A binary operation with a left and right identity. -/
class IsId {α : Type u} (op : α → α → α) (o : outParam α) extends
    IsLeftId op o, IsRightId op o : Prop

instance {op} [IsId op o] : Lean.IsNeutral op o where
  left_neutral := IsLeftId.left_id
  right_neutral := IsRightId.right_id

/--
This class provides `IsId` on a commutative operation.
-/
class IsCommId {α : Type u} (op : α → α → α) [hc : IsCommutative op] (o : outParam α) extends
    IsId op o where
  left_id a := Eq.trans (hc.comm o a) (right_id a)
  right_id a := Eq.trans (hc.comm a o) (left_id a)
