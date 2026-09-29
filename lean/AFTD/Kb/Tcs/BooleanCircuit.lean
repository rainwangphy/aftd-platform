import AFTD.Prelude

/-!
# BooleanCircuit

Topic: circuits   Node: 4eba99cc507c

A Boolean circuit with n inputs over the standard De Morgan basis, with constructors for input variables indexed by Fin n, Boolean constants, negation (NOT), conjunction (AND), and disjunction (OR).
-/

/-- A Boolean circuit on n inputs over the standard De Morgan basis (AND, OR, NOT). -/
inductive BooleanCircuit (n : Nat) where
  | var (i : Fin n) : BooleanCircuit n
  | const (b : Bool) : BooleanCircuit n
  | not (c : BooleanCircuit n) : BooleanCircuit n
  | and (c₁ c₂ : BooleanCircuit n) : BooleanCircuit n
  | or (c₁ c₂ : BooleanCircuit n) : BooleanCircuit n
