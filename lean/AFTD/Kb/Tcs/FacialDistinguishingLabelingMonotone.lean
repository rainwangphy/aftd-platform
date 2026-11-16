import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasFacialDistinguishingLabeling
import AFTD.Kb.Tcs.SimpleGraphFaceSum

/-!
# facial_distinguishing_labeling_monotone

Topic: combinatorics   Node: f60b26c517c5

Provenance: original. Related work: arXiv:2611.18384 Sec. 2.1

For any simple graph G on Fin n with decidable adjacency, dart permutation σ, and natural numbers k ≤ k', if G admits an adjacent-facial-sum-distinguishing proper vertex labeling with bound k, then G admits an adjacent-facial-sum-distinguishing proper vertex labeling with bound k'.
-/

/-- Monotonicity of adjacent-facial-sum-distinguishing labelings with respect to the label bound k. -/
theorem facial_distinguishing_labeling_monotone {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) {k k' : ℕ} (h : k ≤ k')
    (h_label : simple_graph_has_facial_distinguishing_labeling G σ k) :
    simple_graph_has_facial_distinguishing_labeling G σ k' := by
  obtain ⟨c, hproper, hsum⟩ := h_label
  refine ⟨fun v => Fin.castLE (Nat.succ_le_succ h) (c v), ?_, ?_⟩
  · intro u v huv
    have := hproper u v huv
    simpa using this
  · intro d
    have key : (fun v => ((fun v => Fin.castLE (Nat.succ_le_succ h) (c v)) v : ℕ)) =
        (fun v => (c v : ℕ)) := by
      funext v
      simp
    rw [key]
    exact hsum d
