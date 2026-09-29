import AFTD.Prelude

/-!
# CnfLit

Topic: np_completeness   Node: 98a4cc058c1d

A CNF literal over a variable type V is either a positive variable or a negated variable.
-/

/-- A literal over variable type `V`, either a positive or negative occurrence of a variable. -/
inductive CnfLit (V : Type*) | pos (v : V) : CnfLit V
  | neg (v : V) : CnfLit V
