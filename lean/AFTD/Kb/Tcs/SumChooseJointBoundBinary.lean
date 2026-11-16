import AFTD.Prelude

/-!
# sum_choose_joint_bound_binary

Topic: information   Node: c1494458ae07

Provenance: helper lemma. arXiv:2611.18156 Equation (17)

For all natural numbers n, c, c' such that 2 * c + c' + 1 = n, 2 * (∑ i ∈ Finset.range (c + 1), Nat.choose n i) + ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j = 2 ^ n.
-/

/-- Binomial coefficient sum equality for binary joint perfect codes when 2c + c' + 1 = n. -/
lemma sum_choose_joint_bound_binary (n c c' : ℕ) (h_dim : 2 * c + c' + 1 = n) :
    2 * (∑ i ∈ Finset.range (c + 1), Nat.choose n i) +
      ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j = 2 ^ n := by
  let f : ℕ → ℕ := fun i => Nat.choose n i
  have hIcc : Finset.Icc (c + 1) (c + c') = Finset.Ico (c + 1) (c + c' + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hmid : (∑ j ∈ Finset.Icc (c + 1) (c + c'), f j) =
      ∑ j ∈ Finset.Ico (c + 1) (c + c' + 1), f j := by
    rw [hIcc]
  have h3 : (∑ i ∈ Finset.Ico (c + c' + 1) (n + 1), f i) =
      ∑ i ∈ Finset.range (c + 1), f i := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 - (c + c' + 1) = c + 1 := by omega
    rw [hlen]
    rw [← Finset.sum_range_reflect f (c + 1)]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_range] at hx
    simp only [f]
    have hsum : n = (c + c' + 1 + x) + (c - x) := by omega
    rw [Nat.choose_symm_of_eq_add hsum]
    rfl
  have h1 : (∑ i ∈ Finset.range (c + 1), f i) +
      ∑ i ∈ Finset.Ico (c + 1) (c + c' + 1), f i =
      ∑ i ∈ Finset.range (c + c' + 1), f i := by
    simpa using (Finset.sum_range_add_sum_Ico f (m := c + 1) (n := c + c' + 1) (by omega))
  have h2 : (∑ i ∈ Finset.range (c + c' + 1), f i) +
      ∑ i ∈ Finset.Ico (c + c' + 1) (n + 1), f i =
      ∑ i ∈ Finset.range (n + 1), f i := by
    simpa using (Finset.sum_range_add_sum_Ico f (m := c + c' + 1) (n := n + 1) (by omega))
  have htotal : (∑ i ∈ Finset.range (n + 1), f i) = 2 ^ n := by
    simpa [f] using Nat.sum_range_choose n
  calc
    2 * (∑ i ∈ Finset.range (c + 1), Nat.choose n i) +
        ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j
        = 2 * (∑ i ∈ Finset.range (c + 1), f i) +
            ∑ j ∈ Finset.Ico (c + 1) (c + c' + 1), f j := by
          simp [f, hmid]
    _ = (∑ i ∈ Finset.range (c + 1), f i) +
          ∑ i ∈ Finset.Ico (c + 1) (c + c' + 1), f i +
          ∑ i ∈ Finset.range (c + 1), f i := by ring
    _ = (∑ i ∈ Finset.range (c + c' + 1), f i) +
          ∑ i ∈ Finset.range (c + 1), f i := by rw [h1]
    _ = (∑ i ∈ Finset.range (c + c' + 1), f i) +
          ∑ i ∈ Finset.Ico (c + c' + 1) (n + 1), f i := by rw [h3]
    _ = ∑ i ∈ Finset.range (n + 1), f i := h2
    _ = 2 ^ n := htotal
