import AFTD.Prelude

/-!
# GateType

Topic: circuits   Node: c03ada0d1bdf

The standard Boolean gate types in circuit complexity: conjunction (AND), disjunction (OR), and negation (NOT).
-/

/-- The standard Boolean gate types: AND, OR, and NOT. -/
inductive GateType where
  | and
  | or
  | not
deriving DecidableEq, Repr
