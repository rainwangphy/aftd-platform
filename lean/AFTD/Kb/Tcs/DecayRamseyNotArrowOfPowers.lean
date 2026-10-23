import AFTD.Prelude
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.Tcs.DecayRamseyArrow
import AFTD.Kb.Tcs.Op258Bounded

/-!
# decay_ramsey_not_arrow_of_powers

Topic: combinatorics   Node: c689f5fb16f4

Provenance: helper lemma. arXiv:2610.20577, Lemma 5.1

If m ≥ 2 and for every integer ℓ ≥ 1 the complete graph K_{m^ℓ} admits an a-bounded edge-colouring with no monochromatic K_k, then the sequence a does not force K_k (that is, ¬ (a → K_k)).
-/

/-- If K_{m^ℓ} admits an a-bounded K_k-free colouring for all ℓ ≥ 1 where m ≥ 2, then a does not force K_k. -/
theorem decay_ramsey_not_arrow_of_powers (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (a : ℕ+ → ℝ)
    (h_pow : ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ c : (SimpleGraph.completeGraph (Fin (m ^ ℓ))).edgeSet → ℕ+,
      op_258_bounded a (m ^ ℓ) c ∧ ¬ op_258_has_mono_clique (m ^ ℓ) c k) :
    ¬ decay_ramsey_arrow a k := by
  intro ⟨n₀, hn₀⟩
  have hℓ : 1 ≤ n₀ + 1 := Nat.le_add_left 1 n₀
  obtain ⟨c, hc_bounded, hc_not_mono⟩ := h_pow (n₀ + 1) hℓ
  have hm1 : 1 < m := hm
  have h_le : n₀ ≤ m ^ (n₀ + 1) := by
    have := Nat.lt_pow_self hm1 (n := n₀ + 1)
    omega
  exact hc_not_mono (hn₀ (m ^ (n₀ + 1)) h_le c hc_bounded)
