import AFTD.Prelude

/-!
# partition_family_A_57_evaluation

Topic: combinatorics   Node: bdcbc5bbec09

Provenance: formalization of a published result. Source: arXiv:2610.01747 Proposition 6.1

Evaluating the partition cardinality formula with the partition numbers p(54)=386155, p(53)=329931, p(52)=281589, p(51)=239943, p(50)=204226, p(49)=173525, and p(48)=147273 gives 527254, which strictly exceeds 526823 = p(56).
-/

/-- Proposition 6.1 (arXiv:2610.01747): Evaluation of the size formula at n = 57 gives 527254, strictly exceeding p(56) = 526823. -/
theorem partition_family_A_57_evaluation :
    (386155 : ℤ) + 329931 + 281589 - 239943 - 204226 - 173525 + 147273 = 527254 ∧
    527254 > 526823 := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
