import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicRamseyProperty

/-!
# cyclic_ramsey_number

Topic: graphs   Node: 8b0989ecc3a2

Provenance: formalization of a published result. Source: arXiv:2611.08375, Sec. 1

The cyclic Ramsey number R_cyc(H₁, H₂) is the smallest positive integer N such that every 2-edge-colouring of the complete cyclically ordered graph on N vertices contains a monochromatic cyclic copy of H₁ or H₂.
-/

/-- The cyclic Ramsey number of two cyclically ordered graphs. -/
noncomputable def cyclic_ramsey_number {m n : ℕ} (H₁ : SimpleGraph (Fin m)) (H₂ : SimpleGraph (Fin n)) : ℕ := sInf {N : ℕ | 0 < N ∧ cyclic_ramsey_property H₁ H₂ N}
