import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Optimization.AbelSummationByParts
import AFTD.Kb.Optimization.SubmodularBasePolytope
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# observable_upper_bound_base_polytope

Topic: submodular   Node: 12071d0d86b6

Provenance: formalization of a published result. Source: arXiv:2610.35433 Corollary 1 proof

For any vector a whose values are sorted non-decreasingly by permutation π, and any point z in the base polytope of C, the inner product ∑ i, a i * z i is bounded by a(π(0)) + ∑_{k=0}^{n-2} (a(π(k+1)) - a(π(k))) * C(S_{k+1}).
-/

/-- Upper bound on the expectation of an observable over the base polytope of a submodular capacity. -/
theorem observable_upper_bound_base_polytope {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (hπ_mono : Monotone (a ∘ π))
    (C : Finset (Fin n) → ℝ) (z : Fin n → ℝ) (hz : z ∈ submodular_base_polytope C) :
    ∑ i, a i * z i ≤ a (π ⟨0, hn⟩) + ∑ k : Fin (n - 1),
      (a (π ⟨k.val + 1, by omega⟩) - a (π ⟨k.val, by omega⟩)) *
        C ((Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding) := by
  have hz_sum : ∑ i, z i = 1 := hz.2
  have hz_le : ∀ S, ∑ i ∈ S, z i ≤ C S := hz.1
  rw [abel_summation_by_parts hn a π z hz_sum]
  gcongr with k
  · have hle_fin : (⟨k.val, by omega⟩ : Fin n) ≤ ⟨k.val + 1, by omega⟩ := by
      simp only [Fin.le_iff_val_le_val]
      omega
    have hmono := hπ_mono hle_fin
    dsimp [Function.comp] at hmono
    linarith
  · exact hz_le _
