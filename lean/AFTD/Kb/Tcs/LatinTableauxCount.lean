import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTableaux

/-!
# latin_tableaux_count

Topic: combinatorics   Node: 32786505df74

Provenance: formalization of a published result. Source: arXiv:2610.29291, Section 4

The number of Latin tableaux of shape $\mu$ and type $\mu'$, denoted $LT(\mu)$, is the cardinality of the finset of Latin tableaux of shape $\mu$.
-/

/-- The number of Latin tableaux of shape μ and type μ', denoted LT(μ). -/
def latin_tableaux_count (μ : YoungDiagram) : ℕ := (latin_tableaux μ).card
