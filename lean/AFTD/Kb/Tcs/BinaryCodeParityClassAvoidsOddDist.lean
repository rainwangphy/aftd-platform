import AFTD.Prelude

/-!
# binary_code_parity_class_avoids_odd_dist

Topic: combinatorics   Node: 82f042538035

Provenance: helper lemma. arXiv:2611.04523, Proposition 3.1

For any natural numbers n and odd d, and any parity ε : Fin 2, any two words x, y : Fin n → Fin 2 whose sum of coordinates in Fin 2 equals ε have Hamming distance different from d.
-/

lemma binary_code_parity_class_avoids_odd_dist_sub_eq_ite (a b : Fin 2) :
    a - b = if a ≠ b then (1 : Fin 2) else 0 := by
  revert a b
  decide

lemma binary_code_parity_class_avoids_odd_dist_nsmul_one (d : ℕ) (hodd : Odd d) :
    d • (1 : Fin 2) = 1 := by
  rcases hodd with ⟨k, rfl⟩
  rw [add_smul, mul_comm, mul_smul]
  have h2 : (2 : ℕ) • (1 : Fin 2) = 0 := by decide
  rw [h2, smul_zero, zero_add, one_smul]

/-- Any two binary words of the same coordinate-sum parity avoid any odd Hamming distance. -/
theorem binary_code_parity_class_avoids_odd_dist (n d : ℕ) (hodd : Odd d) (ε : Fin 2) : ∀ x y : Fin n → Fin 2, (∑ i, x i) = ε → (∑ i, y i) = ε → hammingDist x y ≠ d := by
  intro x y hx hy hdist
  have h_sum : hammingDist x y • (1 : Fin 2) = 0 := by
    have h (i : Fin n) : x i - y i = if x i ≠ y i then (1 : Fin 2) else 0 :=
      binary_code_parity_class_avoids_odd_dist_sub_eq_ite (x i) (y i)
    have h1 : hammingDist x y • (1 : Fin 2) = ∑ i, (x i - y i) := by
      simp_rw [h]
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      rfl
    rw [h1, Finset.sum_sub_distrib, hx, hy, sub_self]
  have h_d : d • (1 : Fin 2) = 0 := by
    rwa [← hdist]
  have h_odd : d • (1 : Fin 2) = 1 :=
    binary_code_parity_class_avoids_odd_dist_nsmul_one d hodd
  rw [h_d] at h_odd
  revert h_odd
  decide
