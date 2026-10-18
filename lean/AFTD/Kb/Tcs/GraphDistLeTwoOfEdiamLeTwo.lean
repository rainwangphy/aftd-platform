import AFTD.Prelude

/-!
# graph_dist_le_two_of_ediam_le_two

Topic: graphs   Node: 05214708d647

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If the extended diameter of a graph is at most 2, then every (natural-valued) distance is at most 2.
-/

/-- Diameter at most 2 gives all distances at most 2. -/
theorem graph_dist_le_two_of_ediam_le_two {V : Type*} (G : SimpleGraph V)
    (hdiam : G.ediam ≤ 2) (u v : V) : G.dist u v ≤ 2 := by
  have htop : G.ediam ≠ ⊤ := by
    intro h; rw [h] at hdiam; simp at hdiam
  have h2 : G.diam ≤ 2 := by
    have := ENat.toNat_le_toNat hdiam (by simp : (2 : ℕ∞) ≠ ⊤)
    simpa [SimpleGraph.diam] using this
  have := SimpleGraph.dist_le_diam htop (u := u) (v := v)
  omega
