import AFTD.Prelude

/-!
# CircuitGate

Topic: circuits   Node: 83138cfe9f60

A gate in a straight-line program representation of a Boolean circuit on n inputs, which can be an input variable indexed by Fin n, a Boolean constant, a NOT gate referencing a previous gate index, or an AND or OR gate referencing two previous gate indices.
-/

/-- A gate in a straight-line program with n inputs. -/
inductive CircuitGate (n : Nat) where
  | var (i : Fin n)
  | const (b : Bool)
  | not (src : Nat)
  | and (src1 src2 : Nat)
  | or (src1 src2 : Nat)
deriving DecidableEq, Repr
