import AFTD.Prelude

/-!
# condorcet_balanced_top_implies_six_le_candidates

Topic: social_choice   Node: 3d1d55d9b75a

Provenance: helper lemma. step towards condorcet_dimension_le_three

If every three-candidate set contains the top choice of at most half of the voters (and there is at least one voter and at least four candidates), then the election has at least six candidates: the balanced regime is impossible below six candidates.
-/

/-- The balanced case of the Condorcet-dimension problem cannot occur with at most five candidates. -/
theorem condorcet_balanced_top_implies_six_le_candidates (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hn : 0 < n) (hm : 4 ≤ m)
    (hbal : ∀ S : Finset (Fin m), S.card = 3 →
      2 * (Finset.univ.filter fun v => (P v).symm ⟨0, by omega⟩ ∈ S).card ≤ n) :
    6 ≤ m := by
  let top : Fin n → Fin m := fun v => (P v).symm ⟨0, by omega⟩
  let cnt : Finset (Fin m) → ℕ := fun S => (Finset.univ.filter fun v => top v ∈ S).card
  let T : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard 3
  have hfiber (v : Fin n) : (T.filter fun S => top v ∈ S).card = (m - 1).choose 2 := by
    have h := Finset.card_filter_powersetCard_subset ({top v} : Finset (Fin m)) (Finset.univ : Finset (Fin m)) 3 (by simp) (by simp)
    simpa [T, Finset.singleton_subset_iff] using h
  have hsum : ∑ S ∈ T, cnt S = n * ((m - 1).choose 2) := by
    calc
      ∑ S ∈ T, cnt S
          = ∑ S ∈ T, ∑ v ∈ (Finset.univ : Finset (Fin n)), if top v ∈ S then 1 else 0 := by
              simp only [cnt, Finset.card_filter]
      _ = ∑ v ∈ (Finset.univ : Finset (Fin n)), ∑ S ∈ T, if top v ∈ S then 1 else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ v ∈ (Finset.univ : Finset (Fin n)), (T.filter fun S => top v ∈ S).card := by
              simp only [Finset.sum_boole]
              rfl
      _ = ∑ v ∈ (Finset.univ : Finset (Fin n)), (m - 1).choose 2 := by
              simp [hfiber]
      _ = n * ((m - 1).choose 2) := by
              simp
  have hle : 2 * ∑ S ∈ T, cnt S ≤ n * T.card := by
    calc
      2 * ∑ S ∈ T, cnt S = ∑ S ∈ T, 2 * cnt S := by
        rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ T, n := by
        apply Finset.sum_le_sum
        intro S hS
        have hScard : S.card = 3 := by simpa [T] using hS
        exact hbal S hScard
      _ = T.card * n := by simp
      _ = n * T.card := by rw [Nat.mul_comm]
  have hcardT : T.card = m.choose 3 := by
    simp [T, Finset.card_powersetCard]
  have hineq : 2 * (n * ((m - 1).choose 2)) ≤ n * m.choose 3 := by
    calc
      2 * (n * ((m - 1).choose 2)) = 2 * ∑ S ∈ T, cnt S := by rw [hsum]
      _ ≤ n * T.card := hle
      _ = n * m.choose 3 := by rw [hcardT]
  have hchoose : 2 * ((m - 1).choose 2) ≤ m.choose 3 := by
    apply Nat.le_of_mul_le_mul_left _ hn
    calc
      n * (2 * ((m - 1).choose 2)) = 2 * (n * ((m - 1).choose 2)) := by ring
      _ ≤ n * m.choose 3 := hineq
  by_contra h6
  have hmlt : m < 6 := by omega
  interval_cases m <;> norm_num [Nat.choose] at hchoose
