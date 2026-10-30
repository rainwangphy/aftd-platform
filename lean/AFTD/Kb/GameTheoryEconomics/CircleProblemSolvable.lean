import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CircleLocalView
import AFTD.Kb.GameTheoryEconomics.CircleProtocolSolves

/-!
# CircleProblemSolvable

Topic: combinatorial_games   Node: 9bc8bcc61e64

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

Given natural numbers S and n and a hypothesis hS : 3 ≤ S, CircleProblemSolvable S n hS asserts that there exists a protocol p : CircleLocalView (Fin S) → Fin n satisfying CircleProtocolSolves S hS p.
-/

/-- Solvability of the circle anonymous-slip puzzle with n symbols without seat labels. -/
def CircleProblemSolvable (S n : ℕ) (hS : 3 ≤ S) : Prop := ∃ p : CircleLocalView (Fin S) → Fin n, CircleProtocolSolves S hS p
