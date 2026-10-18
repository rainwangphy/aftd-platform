import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.Tcs.Op258Forces

/-!
# op_258_forces_iff

Topic: combinatorics   Node: 99b0dcb96fed

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

For every decay profile a and k, "a forces a monochromatic K_k" holds if and only if the raw statement "for all sufficiently large n, every a-bounded colouring of K_n has a k-element vertex set all of whose edges share a colour" holds.
-/

/-- The forcing predicate unfolds definitionally to the raw statement used in the target, so the two are interchangeable. -/
theorem op_258_forces_iff (a : ℕ+ → ℝ) (k : ℕ) :
    op_258_forces a k ↔ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
      (∀ i : ℕ+, ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card ≤ a i * (n.choose 2 : ℝ)) →
      ∃ (s : Finset (Fin n)) (i : ℕ+), s.card = k ∧
        ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → (h : u ≠ v) →
          c ⟨s(u, v), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = i := Iff.rfl
