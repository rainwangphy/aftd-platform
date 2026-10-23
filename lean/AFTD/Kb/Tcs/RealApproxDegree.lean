import AFTD.Prelude
import AFTD.Kb.Tcs.HasRealApproximation

/-!
# realApproxDegree

Topic: circuits   Node: 70dd921cd20c

Provenance: formalization of a published result. Source: arXiv:2610.19174 Definition 3.1, Listing A.1

For a Boolean function f : (Fin n → Bool) → Bool and real error ε, realApproxDegree f ε is the infimum of all degrees d : ℕ such that HasRealApproximation f d ε holds.
-/

/-- The real approximate degree of a Boolean function f with error ε. -/
noncomputable def realApproxDegree {n : ℕ} (f : (Fin n → Bool) → Bool) (ε : ℝ) : ℕ := sInf { d : ℕ | HasRealApproximation f d ε }
