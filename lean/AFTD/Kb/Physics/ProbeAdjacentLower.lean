import AFTD.Prelude

/-!
# probe_adjacent_lower

Topic: quantum_mechanics   Node: 9b039f28b0cd

Provenance: formalization of a published result. Source: arXiv:2610.35433

For a finite probe set F : Finset ℕ and a rank j : ℕ, the lower adjacent probed rank probe_adjacent_lower F j is the maximum of the finite set {0} ∪ {k ∈ F : k < j}.
-/

/-- Lower adjacent probed rank for an unprobed rank j, defined as max({0} ∪ {k ∈ F : k < j}). -/
def probe_adjacent_lower (F : Finset ℕ) (j : ℕ) : ℕ := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
