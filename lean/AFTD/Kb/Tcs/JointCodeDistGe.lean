import AFTD.Prelude
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing

/-!
# joint_code_dist_ge

Topic: information   Node: 07ed2bc2a00b

Provenance: helper lemma. arXiv:2611.18156, Proposition III.5

If C ⊆ Fin n → Fin q is a (c, c') joint error-correcting and detecting code, then any two distinct codewords x₁, x₂ ∈ C have Hamming distance at least 2 * c + c' + 1.
-/

lemma joint_code_dist_ge_helper {n q : ℕ} (x₁ x₂ : Fin n → Fin q)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, x₁ i ≠ x₂ i) :
    let y : Fin n → Fin q := fun i => if i ∈ S then x₂ i else x₁ i
    hammingDist x₁ y = S.card ∧
    hammingDist x₂ y = hammingDist x₁ x₂ - S.card := by
  intro y
  have h1 : (Finset.univ.filter (fun i => x₁ i ≠ y i)) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [y]
    split_ifs with hi
    · simp [hi, hS i hi]
    · simp [hi]
  have hd : hammingDist x₁ y = S.card := by
    unfold hammingDist
    rw [h1]
  refine ⟨hd, ?_⟩
  have h2 : (Finset.univ.filter (fun i => x₂ i ≠ y i)) =
      (Finset.univ.filter (fun i => x₁ i ≠ x₂ i)) \ S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    dsimp [y]
    split_ifs with hi
    · simp [hi]
    · simp [hi, ne_comm]
  unfold hammingDist
  rw [h2]
  have h_sub : S ⊆ Finset.univ.filter (fun i => x₁ i ≠ x₂ i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS i hi
  exact Finset.card_sdiff_of_subset h_sub

/-- Distinct codewords in a (c, c') joint error-correcting and detecting code have Hamming distance at least 2c + c' + 1. -/
lemma joint_code_dist_ge {n q c c' : ℕ} (C : Finset (Fin n → Fin q))
    (hC : is_joint_error_correcting_detecting c c' C)
    {x₁ x₂ : Fin n → Fin q} (hx₁ : x₁ ∈ C) (hx₂ : x₂ ∈ C) (hne : x₁ ≠ x₂) :
    2 * c + c' + 1 ≤ hammingDist x₁ x₂ := by
  by_contra! h_lt
  let D := Finset.univ.filter (fun i => x₁ i ≠ x₂ i)
  have hD : D.card = hammingDist x₁ x₂ := rfl
  by_cases h_le2 : hammingDist x₁ x₂ ≤ 2 * c
  · obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq (by omega : hammingDist x₁ x₂ / 2 ≤ D.card)
    have hS : ∀ i ∈ S, x₁ i ≠ x₂ i := fun i hi => (Finset.mem_filter.mp (hSD hi)).2
    have ⟨hy1, hy2⟩ := joint_code_dist_ge_helper x₁ x₂ S hS
    have h_disj := hC.1 x₁ hx₁ x₂ hx₂ hne
    rw [Finset.disjoint_left] at h_disj
    apply h_disj (a := fun i => if i ∈ S then x₂ i else x₁ i)
    · simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hy1, hScard]
      omega
    · simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hy2, hScard]
      omega
  · obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq (by omega : c ≤ D.card)
    have hS : ∀ i ∈ S, x₁ i ≠ x₂ i := fun i hi => (Finset.mem_filter.mp (hSD hi)).2
    have ⟨hy1, hy2⟩ := joint_code_dist_ge_helper x₁ x₂ S hS
    have h_disj := hC.2 x₁ hx₁ x₂ hx₂
    rw [Finset.disjoint_left] at h_disj
    apply h_disj (a := fun i => if i ∈ S then x₂ i else x₁ i)
    · simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hy1, hScard]
    · simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hy2, hScard]
      constructor <;> omega
