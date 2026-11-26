import AFTD.Prelude

/-!
# persistent_dictatorship_voter_distances_bound

Topic: social_choice   Node: 0241a5e1dcfc

Provenance: helper lemma. arXiv:2611.30683 Theorem 3.10 -- Stay or Switch? Metric Distortion with Online Candidate Arrivals

For any finite voter type V with at least 3 voters, any candidate type C, any family of pseudometrics d on V ⊕ C indexed by V such that the distance between any two voters u and v is identical under all d i, and any candidate map y_star : V → C, the sum over all i in V and j ≠ i of the distance under d i between j and i is at most twice the sum over all i in V and j ≠ i of the distance under d i between j and y_star i.
-/

private lemma persistent_dictatorship_voter_distances_bound_inner_count
    {V : Type*} [Fintype V] [DecidableEq V] (y k : V) (c : ℝ) :
    (∑ x : V, if y ≠ x ∧ k ≠ x ∧ k ≠ y then c else 0) =
      if k ≠ y then ((Fintype.card V : ℝ) - 2) * c else 0 := by
  by_cases h : k = y
  · simp [h]
  · have hcard2 : 2 ≤ Fintype.card V := by
      have : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨k, y, h⟩
      omega
    have hcard : ((Finset.univ.erase y).erase k).card = Fintype.card V - 2 := by
      rw [Finset.card_erase_of_mem]
      · rw [Finset.card_erase_of_mem]
        · rfl
        · simp
      · simp [h]
    rw [if_pos h]
    rw [show (∑ x : V, if y ≠ x ∧ k ≠ x ∧ k ≠ y then c else 0) =
        ∑ x ∈ (Finset.univ.erase y).erase k, c by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp [h, eq_comm, and_comm]]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [show (((Finset.univ.erase y).erase k).card : ℝ) = (Fintype.card V : ℝ) - 2 by
      rw [hcard, Nat.cast_sub hcard2]
      norm_num]

private lemma persistent_dictatorship_voter_distances_bound_triple_sum
    {V : Type*} [Fintype V] [DecidableEq V] (f : V → V → ℝ) :
    (∑ i : V, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f j k)
    = ((Fintype.card V : ℝ) - 2) * (∑ j : V, ∑ k ∈ Finset.univ.erase j, f j k) := by
  have hk : ∀ (i j : V), (∑ k ∈ (Finset.univ.erase i).erase j, f j k) =
      ∑ k : V, if k ≠ i ∧ k ≠ j then f j k else 0 := by
    intro i j
    rw [← Finset.sum_filter]
    congr 1
    ext k; simp [and_comm]
  have hj : ∀ (i : V), (∑ j ∈ Finset.univ.erase i,
      (∑ k : V, if k ≠ i ∧ k ≠ j then f j k else 0)) =
      ∑ j : V, if j ≠ i then (∑ k : V, if k ≠ i ∧ k ≠ j then f j k else 0) else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp_rw [hk, hj]
  rw [Finset.sum_comm]
  have hpush : ∀ (y x : V),
      (if y ≠ x then (∑ k : V, if k ≠ x ∧ k ≠ y then f y k else 0) else 0)
      = ∑ k : V, if y ≠ x ∧ k ≠ x ∧ k ≠ y then f y k else 0 := by
    intro y x
    by_cases h : y = x
    · simp [h]
    · simp [h]
  simp_rw [hpush]
  rw [show (∑ y : V, ∑ x : V, ∑ k : V,
        if y ≠ x ∧ k ≠ x ∧ k ≠ y then f y k else 0)
      = ∑ y : V, ∑ k : V, ∑ x : V,
        if y ≠ x ∧ k ≠ x ∧ k ≠ y then f y k else 0 by
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_comm]]
  simp_rw [persistent_dictatorship_voter_distances_bound_inner_count]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  congr 1
  ext y
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

private lemma persistent_dictatorship_voter_distances_bound_triple_sum_outer
    {V : Type*} [Fintype V] [DecidableEq V] (f : V → V → ℝ) :
    (∑ i : V, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f i k)
    = ((Fintype.card V : ℝ) - 2) * (∑ i : V, ∑ k ∈ Finset.univ.erase i, f i k) := by
  have hk : ∀ (i j : V), (∑ k ∈ (Finset.univ.erase i).erase j, f i k) =
      ∑ k : V, if k ≠ i ∧ k ≠ j then f i k else 0 := by
    intro i j
    rw [← Finset.sum_filter]
    congr 1
    ext k; simp [and_comm]
  have hj : ∀ (i : V), (∑ j ∈ Finset.univ.erase i,
      (∑ k : V, if k ≠ i ∧ k ≠ j then f i k else 0)) =
      ∑ j : V, if j ≠ i then (∑ k : V, if k ≠ i ∧ k ≠ j then f i k else 0) else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp_rw [hk, hj]
  have hpush : ∀ (i j : V),
      (if j ≠ i then (∑ k : V, if k ≠ i ∧ k ≠ j then f i k else 0) else 0)
      = ∑ k : V, if j ≠ i ∧ k ≠ i ∧ k ≠ j then f i k else 0 := by
    intro i j
    by_cases h : j = i
    · simp [h]
    · simp [h]
  simp_rw [hpush]
  rw [show (∑ i : V, ∑ j : V, ∑ k : V,
        if j ≠ i ∧ k ≠ i ∧ k ≠ j then f i k else 0)
      = ∑ i : V, ∑ k : V, ∑ j : V,
        if j ≠ i ∧ k ≠ i ∧ k ≠ j then f i k else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]]
  have hinner : ∀ (i k : V),
      (∑ j : V, if j ≠ i ∧ k ≠ i ∧ k ≠ j then f i k else 0)
      = if k ≠ i then ((Fintype.card V : ℝ) - 2) * f i k else 0 := by
    intro i k
    by_cases h : k = i
    · simp [h]
    · have hcard2 : 2 ≤ Fintype.card V := by
        have : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨k, i, h⟩
        omega
      have hcard : ((Finset.univ.erase i).erase k).card = Fintype.card V - 2 := by
        rw [Finset.card_erase_of_mem]
        · rw [Finset.card_erase_of_mem]
          · rfl
          · simp
        · simp [h]
      rw [if_pos h]
      rw [show (∑ j : V, if j ≠ i ∧ k ≠ i ∧ k ≠ j then f i k else 0) =
          ∑ j ∈ (Finset.univ.erase i).erase k, f i k by
        rw [← Finset.sum_filter]
        congr 1
        ext j
        simp [h, eq_comm, and_comm]]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [show (((Finset.univ.erase i).erase k).card : ℝ) = (Fintype.card V : ℝ) - 2 by
        rw [hcard, Nat.cast_sub hcard2]
        norm_num]
  simp_rw [hinner]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  congr 1
  ext i
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

private lemma persistent_dictatorship_voter_distances_bound_erase_sum_comm
    {V : Type*} [Fintype V] [DecidableEq V] (g : V → V → ℝ) :
    (∑ j : V, ∑ k ∈ Finset.univ.erase j, g j k) =
      ∑ k : V, ∑ j ∈ Finset.univ.erase k, g j k := by
  have h : ∀ j : V, (∑ k ∈ Finset.univ.erase j, g j k) =
      ∑ k : V, if k ≠ j then g j k else 0 := by
    intro j
    rw [← Finset.sum_filter]
    congr 1
    ext k; simp
  simp_rw [h]
  rw [Finset.sum_comm]
  congr 1
  ext k
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [eq_comm]

/-- Sum of voter-voter distances bounded by twice the cross-distance sum when n >= 3. -/
lemma persistent_dictatorship_voter_distances_bound
    {V C : Type*} [Fintype V] [DecidableEq V]
    (hn : 3 ≤ Fintype.card V)
    (d : V → PseudoMetricSpace (V ⊕ C))
    (h_voter : ∀ (i i' : V) (u v : V),
      (letI := d i; dist (Sum.inl u : V ⊕ C) (Sum.inl v : V ⊕ C)) =
      (letI := d i'; dist (Sum.inl u : V ⊕ C) (Sum.inl v : V ⊕ C)))
    (y_star : V → C) :
    (∑ i : V, ∑ j ∈ Finset.univ.erase i,
      (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C))) ≤
    2 * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
      (letI := d i; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star i)))) := by
  let D : V → V ⊕ C → V ⊕ C → ℝ := fun i x y => (letI := d i; dist x y)
  change (∑ i : V, ∑ j ∈ Finset.univ.erase i, D i (Sum.inl j) (Sum.inl i)) ≤
    2 * (∑ i : V, ∑ j ∈ Finset.univ.erase i, D i (Sum.inl j) (Sum.inr (y_star i)))
  have hD : ∀ (i i' : V) (u v : V),
      D i (Sum.inl u) (Sum.inl v) = D i' (Sum.inl u) (Sum.inl v) := by
    intro i i' u v
    exact h_voter i i' u v
  let c : ℝ := (Fintype.card V : ℝ) - 2
  have hcpos : 0 < c := by
    dsimp [c]
    have h3 : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hstep : ∀ (i j : V), j ∈ Finset.univ.erase i →
      c * D i (Sum.inl j) (Sum.inl i) ≤
      ∑ k ∈ (Finset.univ.erase i).erase j,
        (D k (Sum.inl j) (Sum.inr (y_star k)) +
         D k (Sum.inl i) (Sum.inr (y_star k))) := by
    intro i j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hcard2 : 2 ≤ Fintype.card V := by omega
    have hcard : ((Finset.univ.erase i).erase j).card = Fintype.card V - 2 := by
      rw [Finset.card_erase_of_mem]
      · rw [Finset.card_erase_of_mem]
        · rfl
        · simp
      · simp [hji]
    have hKcard : (((Finset.univ.erase i).erase j).card : ℝ) = c := by
      dsimp [c]
      rw [hcard, Nat.cast_sub hcard2]
      norm_num
    calc
      c * D i (Sum.inl j) (Sum.inl i)
          = (((Finset.univ.erase i).erase j).card : ℝ) *
              D i (Sum.inl j) (Sum.inl i) := by rw [hKcard]
      _ = ∑ k ∈ (Finset.univ.erase i).erase j,
              D i (Sum.inl j) (Sum.inl i) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ (Finset.univ.erase i).erase j,
              (D k (Sum.inl j) (Sum.inr (y_star k)) +
               D k (Sum.inl i) (Sum.inr (y_star k))) := by
        apply Finset.sum_le_sum
        intro k hk
        have htri : D i (Sum.inl j) (Sum.inl i) ≤
            D k (Sum.inl j) (Sum.inr (y_star k)) +
            D k (Sum.inl i) (Sum.inr (y_star k)) := by
          rw [hD i k j i]
          change (letI := d k; dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)) ≤
            (letI := d k; dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star k))) +
            (letI := d k; dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star k)))
          letI := d k
          calc
            dist (Sum.inl j : V ⊕ C) (Sum.inl i : V ⊕ C)
                ≤ dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star k)) +
                  dist (Sum.inr (y_star k)) (Sum.inl i : V ⊕ C) := dist_triangle _ _ _
            _ = dist (Sum.inl j : V ⊕ C) (Sum.inr (y_star k)) +
                  dist (Sum.inl i : V ⊕ C) (Sum.inr (y_star k)) := by
              rw [dist_comm (Sum.inr (y_star k)) (Sum.inl i)]
        exact htri
  have hsum_ineq :
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        c * D i (Sum.inl j) (Sum.inl i)) ≤
      ∑ i : V, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j,
          (D k (Sum.inl j) (Sum.inr (y_star k)) +
           D k (Sum.inl i) (Sum.inr (y_star k))) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hstep i j hj
  have hleft :
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        c * D i (Sum.inl j) (Sum.inl i)) =
      c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inl i)) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  have hR1 :
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j,
          D k (Sum.inl j) (Sum.inr (y_star k))) =
      c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inr (y_star i))) := by
    dsimp [c]
    rw [persistent_dictatorship_voter_distances_bound_triple_sum
      (fun j k => D k (Sum.inl j) (Sum.inr (y_star k)))]
    congr 1
    rw [persistent_dictatorship_voter_distances_bound_erase_sum_comm
      (fun j k => D k (Sum.inl j) (Sum.inr (y_star k)))]
  have hR2 :
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j,
          D k (Sum.inl i) (Sum.inr (y_star k))) =
      c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inr (y_star i))) := by
    dsimp [c]
    rw [persistent_dictatorship_voter_distances_bound_triple_sum_outer
      (fun i k => D k (Sum.inl i) (Sum.inr (y_star k)))]
    congr 1
    rw [persistent_dictatorship_voter_distances_bound_erase_sum_comm
      (fun i k => D k (Sum.inl i) (Sum.inr (y_star k)))]
  have hright :
      (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j,
          (D k (Sum.inl j) (Sum.inr (y_star k)) +
           D k (Sum.inl i) (Sum.inr (y_star k)))) =
      2 * (c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inr (y_star i)))) := by
    simp_rw [Finset.sum_add_distrib]
    rw [hR1, hR2]
    ring
  have hmain : c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inl i)) ≤
      2 * (c * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inr (y_star i)))) := by
    rw [← hleft, ← hright]
    exact hsum_ineq
  have : (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inl i)) ≤
      2 * (∑ i : V, ∑ j ∈ Finset.univ.erase i,
        D i (Sum.inl j) (Sum.inr (y_star i))) := by
    nlinarith [hcpos, hmain]
  exact this
