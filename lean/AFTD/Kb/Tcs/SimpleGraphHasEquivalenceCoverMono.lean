import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover

/-!
# simple_graph_has_equivalence_cover_mono

Topic: combinatorics   Node: 6aabcf3b38fc

Provenance: helper lemma. Sanity lemma for equivalence covers, arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs).

If G is covered by s equivalence subgraphs, it is covered by any larger number t of them (pad with the edgeless equivalence subgraph).
-/

theorem simple_graph_has_equivalence_cover_mono {V : Type*} (G : SimpleGraph V) {s t : ℕ}
    (hst : s ≤ t) (h : simple_graph_has_equivalence_cover G s) :
    simple_graph_has_equivalence_cover G t := by
  obtain ⟨c, hc, hcov⟩ := h
  refine ⟨fun i => if hi : (i : ℕ) < s then c ⟨i, hi⟩ else id, fun i u v huv h => ?_,
    fun u v huv => ?_⟩
  · by_cases hi : (i : ℕ) < s
    · simp only [hi, dif_pos] at h; exact hc _ u v huv h
    · simp only [hi, dif_neg, not_false_eq_true, id] at h; exact absurd h huv
  · obtain ⟨j, hj⟩ := hcov u v huv
    exact ⟨⟨j, by omega⟩, by simp [j.2, hj]⟩
