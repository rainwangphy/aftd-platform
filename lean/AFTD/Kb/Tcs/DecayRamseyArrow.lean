import AFTD.Prelude

/-!
# decay_ramsey_arrow

Topic: combinatorics   Node: aa9ae16eecee

Provenance: formalization of a published result. Source: arXiv:2610.20577, Section 1

For a sequence a : ℕ+ → ℝ and integer k, decay_ramsey_arrow a k holds if for all sufficiently large n, every edge-colouring of K_n where each colour i has at most a i * choose(n, 2) edges contains a monochromatic clique K_k.
-/

/-- The arrow relation a → K_k: every a-bounded edge-colouring of large complete graphs contains a monochromatic K_k. -/
def decay_ramsey_arrow (a : ℕ+ → ℝ) (k : ℕ) : Prop := ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
    (∀ i : ℕ+, ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card ≤ a i * (n.choose 2 : ℝ)) →
    ∃ (s : Finset (Fin n)) (i : ℕ+), s.card = k ∧
      ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → (h : u ≠ v) →
        c ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = i
