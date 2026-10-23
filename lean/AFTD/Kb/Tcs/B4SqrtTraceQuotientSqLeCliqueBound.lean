import AFTD.Prelude
import AFTD.Kb.Tcs.B4Graph
import AFTD.Kb.Tcs.B4QuotientMatrix
import AFTD.Kb.Tcs.B4QuotientTraceSq
import AFTD.Kb.Tcs.B4CliqueNum

/-!
# b4_sqrt_trace_quotient_sq_le_clique_bound

Topic: graphs   Node: c0a0c4c7b756

Provenance: formalization of a published result. Source: arXiv:2610.21388, Theorem 3.5

For any n : Fin 4 → ℕ with 1 ≤ n i for all i : Fin 4 and ¬ (n 0 = 1 ∧ n 1 = 1 ∧ n 2 = 1 ∧ n 3 = 1), Real.sqrt ((b4_quotient_matrix n ^ 2).trace) ≤ (∑ i, (n i : ℝ)) * (1 - 1 / ((b4_graph n).cliqueNum : ℝ)).
-/

lemma b4_sqrt_trace_quotient_sq_le_clique_bound_regimeR (a b c d : ℕ) (ha:1≤a)(hb:1≤b)(hc:1≤c)(hd:1≤d)
    (hda : a ≤ d) (hbc : c ≤ b) (hne : ¬(a=1∧b=1∧c=1∧d=1)) :
    ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ))^2 * (((b:ℝ)+(d:ℝ))-1)^2
      - (((a:ℝ)+(b:ℝ))^2 + ((c:ℝ)+(d:ℝ))^2 + 2*(b:ℝ)*(d:ℝ)
          - 2*((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) + 4) * ((b:ℝ)+(d:ℝ))^2 ≥ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, a = u+1 := ⟨a-1, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, c = v+1 := ⟨c-1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = (v+1)+y := ⟨b-(v+1), by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x, d = (u+1)+x := ⟨d-(u+1), by omega⟩
  have hz : 1 ≤ u + v + x + y := by by_contra h; push_neg at h; apply hne; omega
  rcases Nat.eq_zero_or_pos u with hu0 | hu1
  · rcases Nat.eq_zero_or_pos v with hv0 | hv1
    · rcases Nat.eq_zero_or_pos x with hx0 | hx1
      · obtain ⟨y', rfl⟩ : ∃ y', y = y'+1 := ⟨y-1, by omega⟩
        push_cast; ring_nf; positivity
      · obtain ⟨x', rfl⟩ : ∃ x', x = x'+1 := ⟨x-1, by omega⟩
        push_cast; ring_nf; positivity
    · obtain ⟨v', rfl⟩ : ∃ v', v = v'+1 := ⟨v-1, by omega⟩
      push_cast; ring_nf; positivity
  · obtain ⟨u', rfl⟩ : ∃ u', u = u'+1 := ⟨u-1, by omega⟩
    push_cast; ring_nf; positivity

lemma b4_sqrt_trace_quotient_sq_le_clique_bound_regimeP (a b c d : ℕ) (ha:1≤a)(hb:1≤b)(hc:1≤c)(hd:1≤d)
    (had : d ≤ a) (hPQ : c+d ≤ a+b) (hne : ¬(a=1∧b=1∧c=1∧d=1)) :
    ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ))^2 * (((a:ℝ)+(b:ℝ))-1)^2
      - (((a:ℝ)+(b:ℝ))^2 + ((c:ℝ)+(d:ℝ))^2 + 2*(b:ℝ)*(d:ℝ)
          - 2*((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) + 4) * ((a:ℝ)+(b:ℝ))^2 ≥ 0 := by
  rcases le_total b c with hbcle | hcble
  · obtain ⟨u, rfl⟩ : ∃ u, d = u+1 := ⟨d-1, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, b = v+1 := ⟨b-1, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, c = (v+1)+t := ⟨c-(v+1), by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, a = ((u+1)+t)+q := ⟨a-((u+1)+t), by omega⟩
    have hz : 1 ≤ u+v+t+q := by by_contra h; push_neg at h; apply hne; omega
    rcases Nat.eq_zero_or_pos u with hu0 | hu1
    · rcases Nat.eq_zero_or_pos v with hv0 | hv1
      · rcases Nat.eq_zero_or_pos q with hq0 | hq1
        · obtain ⟨t', rfl⟩ : ∃ t', t = t'+1 := ⟨t-1, by omega⟩
          push_cast; ring_nf; positivity
        · obtain ⟨q', rfl⟩ : ∃ q', q = q'+1 := ⟨q-1, by omega⟩
          push_cast; ring_nf; positivity
      · obtain ⟨v', rfl⟩ : ∃ v', v = v'+1 := ⟨v-1, by omega⟩
        push_cast; ring_nf; positivity
    · obtain ⟨u', rfl⟩ : ∃ u', u = u'+1 := ⟨u-1, by omega⟩
      push_cast; ring_nf; positivity
  · obtain ⟨u, rfl⟩ : ∃ u, d = u+1 := ⟨d-1, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, a = (u+1)+p := ⟨a-(u+1), by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, c = m+1 := ⟨c-1, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, b = (m+1)+r := ⟨b-(m+1), by omega⟩
    have hz : 1 ≤ u+p+m+r := by by_contra h; push_neg at h; apply hne; omega
    rcases Nat.eq_zero_or_pos u with hu0 | hu1
    · rcases Nat.eq_zero_or_pos p with hp0 | hp1
      · rcases Nat.eq_zero_or_pos m with hm0 | hm1
        · obtain ⟨r', rfl⟩ : ∃ r', r = r'+1 := ⟨r-1, by omega⟩
          push_cast; ring_nf; positivity
        · obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
          push_cast; ring_nf; positivity
      · obtain ⟨p', rfl⟩ : ∃ p', p = p'+1 := ⟨p-1, by omega⟩
        push_cast; ring_nf; positivity
    · obtain ⟨u', rfl⟩ : ∃ u', u = u'+1 := ⟨u-1, by omega⟩
      push_cast; ring_nf; positivity

lemma b4_sqrt_trace_quotient_sq_le_clique_bound_regimeQ (a b c d : ℕ) (ha:1≤a)(hb:1≤b)(hc:1≤c)(hd:1≤d)
    (hbc : b ≤ c) (hQP : a+b ≤ c+d) (hne : ¬(a=1∧b=1∧c=1∧d=1)) :
    ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ))^2 * (((c:ℝ)+(d:ℝ))-1)^2
      - (((a:ℝ)+(b:ℝ))^2 + ((c:ℝ)+(d:ℝ))^2 + 2*(b:ℝ)*(d:ℝ)
          - 2*((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) + 4) * ((c:ℝ)+(d:ℝ))^2 ≥ 0 := by
  have h := b4_sqrt_trace_quotient_sq_le_clique_bound_regimeP c d a b hc hd ha hb (by omega) (by omega) (by
    rintro ⟨hc1,hd1,ha1,hb1⟩; exact hne ⟨ha1,hb1,hc1,hd1⟩)
  convert h using 2 <;> ring

lemma b4_sqrt_trace_quotient_sq_le_clique_bound_key (a b c d : ℕ) (ha:1≤a)(hb:1≤b)(hc:1≤c)(hd:1≤d)
    (hne : ¬(a=1∧b=1∧c=1∧d=1)) :
    Real.sqrt (((a:ℝ)+(b:ℝ))^2 + ((c:ℝ)+(d:ℝ))^2 + 2*(b:ℝ)*(d:ℝ)
        - 2*((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) + 4)
      ≤ ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) *
          (1 - 1/((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)) := by
  have hD : ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ))^2 *
        (((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)-1)^2
      - (((a:ℝ)+(b:ℝ))^2 + ((c:ℝ)+(d:ℝ))^2 + 2*(b:ℝ)*(d:ℝ)
          - 2*((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) + 4) *
          (((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ))^2 ≥ 0 := by
    by_cases hRtop : a+b ≤ b+d ∧ c+d ≤ b+d
    · have hOm : max (max (a+b) (b+d)) (c+d) = b+d := by
        rw [max_eq_right hRtop.1, max_eq_left hRtop.2]
      have hωeq : ((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ) = (b:ℝ)+(d:ℝ) := by
        rw [hOm]; push_cast; ring
      rw [hωeq]
      exact b4_sqrt_trace_quotient_sq_le_clique_bound_regimeR a b c d ha hb hc hd (by omega) (by omega) hne
    · have hRle : b+d ≤ max (a+b) (c+d) := by
        rcases (not_and_or.mp hRtop) with h | h
        · exact le_trans (by omega) (le_max_left _ _)
        · exact le_trans (by omega) (le_max_right _ _)
      have hOm2 : max (max (a+b) (b+d)) (c+d) = max (a+b) (c+d) := by
        apply le_antisymm
        · exact max_le (max_le (le_max_left _ _) hRle) (le_max_right _ _)
        · exact max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
      rw [hOm2]
      rcases le_total (c+d) (a+b) with hPQ | hQP
      · have hOmP : max (a+b) (c+d) = a+b := max_eq_left hPQ
        have hωeq : ((max (a+b) (c+d) : ℕ) : ℝ) = (a:ℝ)+(b:ℝ) := by
          rw [hOmP]; push_cast; ring
        rw [hωeq]
        have hdad : d ≤ a := by rw [hOmP] at hRle; omega
        exact b4_sqrt_trace_quotient_sq_le_clique_bound_regimeP a b c d ha hb hc hd hdad hPQ hne
      · have hOmQ : max (a+b) (c+d) = c+d := max_eq_right hQP
        have hωeq : ((max (a+b) (c+d) : ℕ) : ℝ) = (c:ℝ)+(d:ℝ) := by
          rw [hOmQ]; push_cast; ring
        rw [hωeq]
        have hbc : b ≤ c := by rw [hOmQ] at hRle; omega
        exact b4_sqrt_trace_quotient_sq_le_clique_bound_regimeQ a b c d ha hb hc hd hbc hQP hne
  have hωpos : (0:ℝ) < ((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ) := by
    have hM2 : 2 ≤ max (max (a+b) (b+d)) (c+d) :=
      le_trans (by omega : 2 ≤ c+d) (le_max_right _ _)
    exact_mod_cast (by omega : (0:ℕ) < max (max (a+b) (b+d)) (c+d))
  have hω1 : (1:ℝ) ≤ ((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ) := by
    have hM2 : 2 ≤ max (max (a+b) (b+d)) (c+d) :=
      le_trans (by omega : 2 ≤ c+d) (le_max_right _ _)
    exact_mod_cast (by omega : (1:ℕ) ≤ max (max (a+b) (b+d)) (c+d))
  have hNnn : (0:ℝ) ≤ (a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ) := by positivity
  have hRHSnn : (0:ℝ) ≤ ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) *
      (1 - 1/((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)) := by
    apply mul_nonneg hNnn
    have h1 : (1:ℝ)/((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hωpos]; exact hω1
    linarith
  rw [Real.sqrt_le_left hRHSnn]
  have hωne : ((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ) ≠ 0 := ne_of_gt hωpos
  have hpow : (((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ)) *
        (1 - 1/((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)))^2
      = ((a:ℝ)+(b:ℝ)+(c:ℝ)+(d:ℝ))^2 *
          (((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)-1)^2
        / (((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ))^2 := by
    field_simp
  rw [hpow]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((max (max (a+b) (b+d)) (c+d) : ℕ) : ℝ)^2)]
  nlinarith [hD]

/-- Strengthened spectral clique bound for the graph family B_4(n_1, n_2, n_3, n_4). -/
theorem b4_sqrt_trace_quotient_sq_le_clique_bound (n : Fin 4 → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (hne : ¬ (n 0 = 1 ∧ n 1 = 1 ∧ n 2 = 1 ∧ n 3 = 1)) :
    Real.sqrt ((b4_quotient_matrix n ^ 2).trace)
      ≤ (∑ i, (n i : ℝ)) * (1 - 1 / ((b4_graph n).cliqueNum : ℝ)) := by
  rw [b4_quotient_trace_sq, b4_cliqueNum, Fin.sum_univ_four]
  exact b4_sqrt_trace_quotient_sq_le_clique_bound_key (n 0) (n 1) (n 2) (n 3)
    (hpos 0) (hpos 1) (hpos 2) (hpos 3) hne
