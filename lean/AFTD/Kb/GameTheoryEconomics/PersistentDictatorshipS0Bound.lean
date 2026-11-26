import AFTD.Prelude

/-!
# persistent_dictatorship_s0_bound

Topic: social_choice   Node: 74414f4a666a

Provenance: helper lemma. arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V and candidate type C, any family of pseudometrics d on V ⊕ C indexed by V, and any candidate map y_star : V → C, (|V| - 1) times the sum over i in V of d_i(i, y_star i) is at most the sum over all i and j ≠ i of voter distance d_i(i, j) plus the sum over all i and j ≠ i of d_i(j, y_star i).
-/

/-- Bound on (n - 1) * S0 by voter distances plus cross distances. -/
lemma persistent_dictatorship_s0_bound
    {V C : Type*} [Fintype V] [DecidableEq V]
    (d : V → PseudoMetricSpace (V ⊕ C))
    (y_star : V → C) :
    ((Fintype.card V : ℝ) - 1) * (∑ i : V, (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))) ≤
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inl j : V ⊕ C))) +
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star i)))) := by
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    have h1 : (Finset.univ.erase i).card = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    rw [h1]
    have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Nat.cast_sub hpos]
    norm_num
  have hf : ((Fintype.card V : ℝ) - 1) * (letI := d i; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star i)))
      = ∑ j ∈ Finset.univ.erase i, @dist (V ⊕ C) ((d i).toDist) (Sum.inl i) (Sum.inr (y_star i)) := by
    rw [← hcard, Finset.sum_const, nsmul_eq_mul]
  rw [hf]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun j _ => ?_)
  exact @dist_triangle (V ⊕ C) (d i) (Sum.inl i) (Sum.inl j) (Sum.inr (y_star i))
