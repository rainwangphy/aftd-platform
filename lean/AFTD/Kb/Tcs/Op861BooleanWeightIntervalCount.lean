import AFTD.Prelude

/-!
# op861_boolean_weight_interval_count

Topic: graphs   Node: 2bb46a41687e

Provenance: helper lemma. Finite binomial interval estimate for op861_dense_triangle_orientation_sqrt_cover.

For natural numbers n, a, and b with a at most b, the number of subsets of an n-element set whose cardinalities lie between a and b inclusive is at most (b−a+1) times the largest binomial coefficient n choose floor(n/2).
-/

theorem op861_boolean_weight_interval_count (n a b : ℕ) (hab : a ≤ b) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => a ≤ S.card ∧ S.card ≤ b)).card ≤
      (b-a+1) * n.choose (n/2) := by
  classical
  have hsub : ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => a ≤ S.card ∧ S.card ≤ b))
      ⊆ (Finset.Icc a b).biUnion (fun s => (Finset.univ : Finset (Fin n)).powersetCard s) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨S.card, hS, rfl⟩
  calc _ ≤ ((Finset.Icc a b).biUnion (fun s => (Finset.univ : Finset (Fin n)).powersetCard s)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Finset.Icc a b, ((Finset.univ : Finset (Fin n)).powersetCard s).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Finset.Icc a b, n.choose (n / 2) := by
        apply Finset.sum_le_sum
        intro s _
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        exact Nat.choose_le_middle s n
    _ = (b - a + 1) * n.choose (n / 2) := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        congr 1
        omega
