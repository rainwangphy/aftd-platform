import AFTD.Prelude
import AFTD.Kb.Tcs.PairCodegree

/-!
# min_pair_codegree

Topic: combinatorics   Node: 6c41319b2a8d

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

The minimum pair-codegree δ₂(H) of a 3-uniform hypergraph H on Fin n is the minimum of the pair-codegree over all pairs of distinct vertices in Fin n (or 0 if n < 2).
-/

/-- The minimum pair-codegree δ₂(H) of a 3-graph H on Fin n over all pairs of distinct vertices. -/
noncomputable def min_pair_codegree (n : ℕ) (H : Finset (Finset (Fin n))) : ℕ := if h : 2 ≤ n then
    let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)
    have hp : pairs.Nonempty := by
      rcases n with _ | _ | n'
      · omega
      · omega
      · exact ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩, by simp [pairs]⟩
    pairs.inf' hp (fun p => pair_codegree H p.1 p.2)
  else 0
