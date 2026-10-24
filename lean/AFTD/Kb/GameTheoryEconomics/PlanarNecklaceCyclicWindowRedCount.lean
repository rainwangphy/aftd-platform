import AFTD.Prelude

/-!
# planar_necklace_cyclic_window_red_count

Topic: fair_division   Node: 4d0f16baf2a8

Provenance: helper lemma. step towards planar_necklace_three_agents_three_cuts

Let w : ℕ → Fin 2 be N-periodic (w (i + N) = w i) with N = 3k, k > 0, and suppose that among the N positions exactly 3a are red (w i = 0). Then some window of k consecutive positions contains exactly a red positions.
-/

lemma planar_necklace_cyclic_window_red_count_walk_aux
    (f : ℕ → ℕ)
    (hup : ∀ i, f (i+1) ≤ f i + 1)
    (hdown : ∀ i, f i ≤ f (i+1) + 1) :
    ∀ d u v a, v = u + d →
      ((f u ≤ a ∧ a ≤ f v) ∨ (f v ≤ a ∧ a ≤ f u)) →
      ∃ i, u ≤ i ∧ i ≤ v ∧ f i = a := by
  intro d
  induction d with
  | zero =>
      intro u v a hv hstrad
      have hv' : v = u := by omega
      subst v
      simp only [Nat.add_zero] at hstrad
      exact ⟨u, le_rfl, le_rfl, by omega⟩
  | succ d ih =>
      intro u v a hv hstrad
      rcases hstrad with ⟨hle, hge⟩ | ⟨hle, hge⟩
      · by_cases hfa : f u = a
        · exact ⟨u, le_rfl, by omega, hfa⟩
        · have hlt : f u < a := lt_of_le_of_ne hle hfa
          have hnext_le : f (u+1) ≤ a := by
            have := hup u
            omega
          by_cases hnext : f (u+1) = a
          · exact ⟨u+1, by omega, by omega, hnext⟩
          · have hnext_lt : f (u+1) < a := lt_of_le_of_ne hnext_le hnext
            obtain ⟨i, hi1, hi2, hia⟩ := ih (u+1) v a (by omega) (Or.inl ⟨le_of_lt hnext_lt, hge⟩)
            exact ⟨i, by omega, hi2, hia⟩
      · by_cases hfa : f u = a
        · exact ⟨u, le_rfl, by omega, hfa⟩
        · have hgt : a < f u := lt_of_le_of_ne hge (Ne.symm hfa)
          have hnext_ge : a ≤ f (u+1) := by
            have := hdown u
            omega
          by_cases hnext : f (u+1) = a
          · exact ⟨u+1, by omega, by omega, hnext⟩
          · have hnext_gt : a < f (u+1) := lt_of_le_of_ne hnext_ge (Ne.symm hnext)
            obtain ⟨i, hi1, hi2, hia⟩ := ih (u+1) v a (by omega) (Or.inr ⟨hle, le_of_lt hnext_gt⟩)
            exact ⟨i, by omega, hi2, hia⟩

lemma planar_necklace_cyclic_window_red_count_walk
    (f : ℕ → ℕ)
    (hup : ∀ i, f (i+1) ≤ f i + 1)
    (hdown : ∀ i, f i ≤ f (i+1) + 1)
    (u v a : ℕ) (huv : u ≤ v)
    (hstrad : (f u ≤ a ∧ a ≤ f v) ∨ (f v ≤ a ∧ a ≤ f u)) :
    ∃ i, u ≤ i ∧ i ≤ v ∧ f i = a :=
  planar_necklace_cyclic_window_red_count_walk_aux f hup hdown (v-u) u v a (by omega) hstrad

/-- Discrete circular-window lemma: a cyclic 2-coloured necklace with 3a red of 3k beads has a window of k consecutive beads with exactly a red beads. -/
theorem planar_necklace_cyclic_window_red_count
    (k N a : ℕ) (hk : 0 < k) (hN : N = 3 * k) (w : ℕ → Fin 2)
    (hperiod : ∀ i, w (i + N) = w i)
    (hred : ((Finset.range N).filter (fun i => w i = 0)).card = 3 * a) :
    ∃ i : ℕ, ((Finset.range k).filter (fun j => w (i + j) = 0)).card = a := by
  let c : ℕ → ℕ := fun j => if w j = 0 then 1 else 0
  let R : ℕ → ℕ := fun i => ∑ j ∈ Finset.range k, c (i+j)
  let f : ℕ → ℕ := fun n => ∑ j ∈ Finset.range n, c j
  have hper : w (0 + N) = w 0 := hperiod 0
  have hf_add : ∀ i, f (i+k) = f i + R i := by
    intro i
    dsimp [f, R]
    rw [Finset.sum_range_add]
  have hf_succ : ∀ n, f (n+1) = f n + c n := by
    intro n
    dsimp [f]
    rw [Finset.sum_range_succ]
  have hc01 : ∀ n, c n = 0 ∨ c n = 1 := by
    intro n
    dsimp [c]
    split_ifs <;> simp
  have hRstep_up : ∀ i, R (i+1) ≤ R i + 1 := by
    intro i
    have h1 := hf_add (i+1)
    have h2 := hf_add i
    have h3 : f (i+1+k) = f (i+k+1) := congrArg f (by omega)
    have h4 := hf_succ (i+k)
    have h5 := hf_succ i
    have h6 : c (i+k) ≤ 1 := by rcases hc01 (i+k) with h | h <;> omega
    rw [h3] at h1
    omega
  have hRstep_down : ∀ i, R i ≤ R (i+1) + 1 := by
    intro i
    have h1 := hf_add (i+1)
    have h2 := hf_add i
    have h3 : f (i+1+k) = f (i+k+1) := congrArg f (by omega)
    have h4 := hf_succ (i+k)
    have h5 := hf_succ i
    have h6 : c i ≤ 1 := by rcases hc01 i with h | h <;> omega
    rw [h3] at h1
    omega
  have hsum : R 0 + R k + R (2*k) = 3*a := by
    have h0 : f k = R 0 := by
      simpa [f] using hf_add 0
    have hk2 : f (2*k) = f k + R k := by
      have h := hf_add k
      rw [show k+k = 2*k by omega] at h
      exact h
    have h2k3 : f (3*k) = f (2*k) + R (2*k) := by
      have h := hf_add (2*k)
      rw [show 2*k+k = 3*k by omega] at h
      exact h
    have hfN : f N = 3*a := by
      dsimp [f]
      rw [Finset.card_filter] at hred
      exact hred
    rw [hN] at hfN
    omega
  have hlow : R 0 ≤ a ∨ R k ≤ a ∨ R (2*k) ≤ a := by
    by_contra h
    simp only [not_or, not_le] at h
    omega
  have hhigh : a ≤ R 0 ∨ a ≤ R k ∨ a ≤ R (2*k) := by
    by_contra h
    simp only [not_or, not_le] at h
    omega
  have hstrad : ∃ u v, u ≤ v ∧ ((R u ≤ a ∧ a ≤ R v) ∨ (R v ≤ a ∧ a ≤ R u)) := by
    rcases hlow with h0 | hkR | h2
    · rcases hhigh with g0 | gk | g2
      · exact ⟨0, 0, le_rfl, Or.inl ⟨h0, g0⟩⟩
      · exact ⟨0, k, by omega, Or.inl ⟨h0, gk⟩⟩
      · exact ⟨0, 2*k, by omega, Or.inl ⟨h0, g2⟩⟩
    · rcases hhigh with g0 | gk | g2
      · exact ⟨0, k, by omega, Or.inr ⟨hkR, g0⟩⟩
      · exact ⟨k, k, le_rfl, Or.inl ⟨hkR, gk⟩⟩
      · exact ⟨k, 2*k, by omega, Or.inl ⟨hkR, g2⟩⟩
    · rcases hhigh with g0 | gk | g2
      · exact ⟨0, 2*k, by omega, Or.inr ⟨h2, g0⟩⟩
      · exact ⟨k, 2*k, by omega, Or.inr ⟨h2, gk⟩⟩
      · exact ⟨2*k, 2*k, le_rfl, Or.inl ⟨h2, g2⟩⟩
  obtain ⟨u, v, huv, hstr⟩ := hstrad
  obtain ⟨i, hiu, hiv, hia⟩ :=
    planar_necklace_cyclic_window_red_count_walk R hRstep_up hRstep_down u v a huv hstr
  refine ⟨i, ?_⟩
  have hRfilter : ((Finset.range k).filter (fun j => w (i+j) = 0)).card = R i := by
    dsimp [R, c]
    rw [Finset.card_filter]
  rw [hRfilter, hia]
