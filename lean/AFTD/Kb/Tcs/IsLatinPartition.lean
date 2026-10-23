import AFTD.Prelude
import AFTD.Kb.Tcs.IsLatinTableau

/-!
# is_latin_partition

Topic: combinatorics   Node: 839c8ad5b388

Provenance: formalization of a published result. Source: arXiv:2610.29291 Definition 2.5

A partition $\lambda$ is Latin if there exists a Latin tableau of shape $\lambda$ and type $\lambda'$.
-/

/-- A Young diagram is Latin if it admits a Latin tableau of shape μ and type conjugate of μ. -/
def is_latin_partition (μ : YoungDiagram) : Prop := ∃ T : ℕ → ℕ → ℕ, is_latin_tableau μ T
