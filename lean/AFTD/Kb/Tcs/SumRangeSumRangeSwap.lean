import AFTD.Prelude

/-!
# sum_range_sum_range_swap

Topic: combinatorics   Node: fe4e939b7827

Provenance: helper lemma. arXiv:2611.06860 "Largest Sperner families with bounded VC-dimension", Lemma 2.5

For any positive integer $d$ and functions $f, g : ℕ → ℕ$, the summation identity $\sum_{s=0}^{d-1} f(s) \sum_{j=0}^{d-s} g(j) = \sum_{j=0}^d g(j) \sum_{s=0}^{\min(d-j, d-1)} f(s)$ holds.
-/

/-- Interchange the order of summation in a triangular double sum over finite ranges. -/
theorem sum_range_sum_range_swap (d : ℕ) (hd : 1 ≤ d) (f g : ℕ → ℕ) :
    ∑ s ∈ Finset.range d, f s * (∑ j ∈ Finset.range (d - s + 1), g j) =
      ∑ j ∈ Finset.range (d + 1), g j * (∑ s ∈ Finset.range (min (d - j) (d - 1) + 1), f s) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (d + 1)) (s' := fun j => Finset.range (min (d - j) (d - 1) + 1))]
  · simp_rw [mul_comm]
  · intro s j
    simp only [Finset.mem_range, Nat.lt_succ_iff, le_min_iff]
    omega
