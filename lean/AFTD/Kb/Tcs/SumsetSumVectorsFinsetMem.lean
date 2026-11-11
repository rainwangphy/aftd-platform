import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetSumVectors
import AFTD.Kb.Tcs.SumsetSumVectorsFinset
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# sumset_sum_vectors_finset_mem

Topic: combinatorics   Node: 50051431b2e4

Provenance: helper lemma. arXiv:2611.07303, Section 1

For any natural numbers h and k and any vector x : Fin k → ℤ, x belongs to sumset_sum_vectors_finset h k if and only if x belongs to sumset_sum_vectors h k.
-/

/-- Equivalence between sumset_sum_vectors_finset and sumset_sum_vectors. -/
theorem sumset_sum_vectors_finset_mem (h k : ℕ) (x : Fin k → ℤ) :
    x ∈ sumset_sum_vectors_finset h k ↔ x ∈ sumset_sum_vectors h k := by
  simp only [sumset_sum_vectors_finset, sumset_sum_vectors, Finset.mem_filter,
    Set.mem_ofPred_eq, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hx, hsum⟩
    refine ⟨fun i => ?_, hsum⟩
    obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp (hx i)
    rw [← hnx]
    exact Nat.cast_nonneg n
  · rintro ⟨hx, hsum⟩
    refine ⟨fun i => ?_, hsum⟩
    rw [Finset.mem_image]
    refine ⟨(x i).toNat, ?_, Int.toNat_of_nonneg (hx i)⟩
    rw [Finset.mem_range]
    have hle : x i ≤ (h : ℤ) := by
      rw [← hsum]
      exact Finset.single_le_sum (f := x) (fun j _ => hx j) (Finset.mem_univ i)
    have h1 : ((x i).toNat : ℤ) = x i := Int.toNat_of_nonneg (hx i)
    omega
