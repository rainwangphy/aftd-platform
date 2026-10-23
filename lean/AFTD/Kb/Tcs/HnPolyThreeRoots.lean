import AFTD.Prelude
import AFTD.Kb.Tcs.HnPoly

/-!
# hn_poly_three_roots

Topic: graphs   Node: b5e2488a6dfc

Provenance: helper lemma. arXiv:2610.18636 Theorem 4

For every integer n ≥ 2, the cubic polynomial hn_poly n has three real roots l1 > l2 > l3 satisfying 1/2 < l1 < 2n, 0 < l2 < 1/2, and -n < l3 < 0, such that hn_poly n = (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) * (Polynomial.X - Polynomial.C l3).
-/

lemma hn_poly_three_roots_aux_zero (p : Polynomial ℝ) (hdeg : p.natDegree ≤ 2)
    (l1 l2 l3 : ℝ) (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3)
    (hr1 : p.IsRoot l1) (hr2 : p.IsRoot l2) (hr3 : p.IsRoot l3) : p = 0 := by
  by_contra hp
  have hcard := p.card_roots'
  have h1 : l1 ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp).mpr hr1
  have h2 : l2 ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp).mpr hr2
  have h3 : l3 ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp).mpr hr3
  let s : Finset ℝ := {l1, l2, l3}
  have hs : s ⊆ p.roots.toFinset := by
    intro x hx
    aesop
  have hscard : s.card = 3 := by
    simp [s, h12, h13, h23]
  have hle := Finset.card_le_card hs
  have hle2 := p.roots.toFinset_card_le
  omega

/-- The polynomial q_n has three real roots in (1/2, 2n), (0, 1/2), and (-n, 0). -/
theorem hn_poly_three_roots (n : ℕ) (hle : 2 ≤ n) :
    ∃ l1 l2 l3 : ℝ,
      1 / 2 < l1 ∧ l1 < 2 * (n : ℝ) ∧
      0 < l2 ∧ l2 < 1 / 2 ∧
      -(n : ℝ) < l3 ∧ l3 < 0 ∧
      l2 < l1 ∧ l3 < l2 ∧
      hn_poly n = (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) * (Polynomial.X - Polynomial.C l3) := by
  have hn : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  -- Root l3 in (-n, 0)
  have hab3 : -(n : ℝ) ≤ 0 := by linarith
  have hcont3 : ContinuousOn (fun x : ℝ => (hn_poly n).eval x) (Set.Icc (-(n : ℝ)) 0) :=
    (hn_poly n).continuous.continuousOn
  have hneg3 : (hn_poly n).eval (-(n : ℝ)) < 0 := by
    have heval : (hn_poly n).eval (-(n : ℝ)) = -2 * (n : ℝ) := by
      unfold hn_poly
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    linarith
  have hpos3 : 0 < (hn_poly n).eval 0 := by
    have heval : (hn_poly n).eval 0 = (n : ℝ) ^ 2 - (n : ℝ) := by
      unfold hn_poly
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    nlinarith
  have h0_3 : (0 : ℝ) ∈ Set.Ioo ((hn_poly n).eval (-(n : ℝ))) ((hn_poly n).eval 0) := ⟨hneg3, hpos3⟩
  rcases intermediate_value_Ioo hab3 hcont3 h0_3 with ⟨l3, hl3_mem, hl3_eval⟩

  -- Root l2 in (0, 1/2)
  have hab2 : (0 : ℝ) ≤ 1 / 2 := by linarith
  have hcont2 : ContinuousOn (fun x : ℝ => (hn_poly n).eval x) (Set.Icc 0 (1 / 2)) :=
    (hn_poly n).continuous.continuousOn
  have hneg2 : (hn_poly n).eval (1 / 2) < 0 := by
    have heval : (hn_poly n).eval (1 / 2) = 5 / 8 - 3 * (n : ℝ) / 4 := by
      unfold hn_poly
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    linarith
  have h0_2 : (0 : ℝ) ∈ Set.Ioo ((hn_poly n).eval (1 / 2)) ((hn_poly n).eval 0) := ⟨hneg2, hpos3⟩
  rcases intermediate_value_Ioo' hab2 hcont2 h0_2 with ⟨l2, hl2_mem, hl2_eval⟩

  -- Root l1 in (1/2, 2n)
  have hab1 : (1 : ℝ) / 2 ≤ 2 * (n : ℝ) := by linarith
  have hcont1 : ContinuousOn (fun x : ℝ => (hn_poly n).eval x) (Set.Icc (1 / 2) (2 * (n : ℝ))) :=
    (hn_poly n).continuous.continuousOn
  have hpos1 : 0 < (hn_poly n).eval (2 * (n : ℝ)) := by
    have heval : (hn_poly n).eval (2 * (n : ℝ)) = 3 * (n : ℝ) ^ 2 + (n : ℝ) := by
      unfold hn_poly
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    nlinarith
  have h0_1 : (0 : ℝ) ∈ Set.Ioo ((hn_poly n).eval (1 / 2)) ((hn_poly n).eval (2 * (n : ℝ))) := ⟨hneg2, hpos1⟩
  rcases intermediate_value_Ioo hab1 hcont1 h0_1 with ⟨l1, hl1_mem, hl1_eval⟩

  have h21 : l2 < l1 := by linarith [hl2_mem.2, hl1_mem.1]
  have h32 : l3 < l2 := by linarith [hl3_mem.2, hl2_mem.1]
  have h31 : l3 < l1 := by linarith

  refine ⟨l1, l2, l3, hl1_mem.1, hl1_mem.2, hl2_mem.1, hl2_mem.2, hl3_mem.1, hl3_mem.2, h21, h32, ?_⟩

  set Q := (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) * (Polynomial.X - Polynomial.C l3)
  have hdeg : (hn_poly n - Q).natDegree ≤ 2 := by
    have hQ : Q = Polynomial.X ^ 3 - Polynomial.C (l1 + l2 + l3) * Polynomial.X ^ 2 +
        Polynomial.C (l1 * l2 + l1 * l3 + l2 * l3) * Polynomial.X -
        Polynomial.C (l1 * l2 * l3) := by
      simp only [Q, map_add, map_mul]
      ring
    rw [hQ]
    unfold hn_poly
    ring_nf
    compute_degree!

  have hr1 : (hn_poly n - Q).IsRoot l1 := by
    simp [Polynomial.IsRoot.def, hl1_eval, Q]
  have hr2 : (hn_poly n - Q).IsRoot l2 := by
    simp [Polynomial.IsRoot.def, hl2_eval, Q]
  have hr3 : (hn_poly n - Q).IsRoot l3 := by
    simp [Polynomial.IsRoot.def, hl3_eval, Q]

  have hdiff : hn_poly n - Q = 0 :=
    hn_poly_three_roots_aux_zero (hn_poly n - Q) hdeg l1 l2 l3 (by linarith) (by linarith) (by linarith) hr1 hr2 hr3
  exact sub_eq_zero.mp hdiff
