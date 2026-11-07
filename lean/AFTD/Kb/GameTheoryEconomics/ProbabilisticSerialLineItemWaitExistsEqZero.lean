import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineItemWait
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseLength

/-!
# probabilistic_serial_line_item_wait_exists_eq_zero

Topic: social_choice   Node: c26c98e9a2c1

Provenance: helper lemma. Reduction step for OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

For n >= 1 items, some item has waiting cost 0 in the probabilistic serial procedure: an item still unfinished at the start of the last phase in which some item is unfinished is never counted.
-/

theorem ps_wait_zero_phase_fst_le_and_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hs : ∀ j, 0 ≤ s.1 j) (j : Fin n) :
    0 ≤ (probabilistic_serial_phase n pref s).1 j ∧ (probabilistic_serial_phase n pref s).1 j ≤ s.1 j := by
  classical
  unfold probabilistic_serial_phase
  simp only
  set S := Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card) with hS
  split_ifs with h
  · set c : Fin n → ℕ := fun j => (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card with hc
    have ht0 : 0 ≤ S.inf' h (fun j => s.1 j / (c j : ℝ)) := by
      rw [Finset.le_inf'_iff]
      intro k _
      exact div_nonneg (hs k) (Nat.cast_nonneg _)
    have hcn : (0 : ℝ) ≤ (c j : ℝ) := Nat.cast_nonneg _
    constructor
    · by_cases hj : j ∈ S
      · have hle := Finset.inf'_le (fun j => s.1 j / (c j : ℝ)) hj
        have hpos : (0 : ℝ) < c j := by
          have := (Finset.mem_filter.mp hj).2
          exact_mod_cast this
        have := (le_div_iff₀ hpos).mp hle
        show 0 ≤ s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ)
        linarith
      · have h0 : c j = 0 := by
          by_contra hne
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩)
        show 0 ≤ s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ)
        rw [h0]; simp [hs j]
    · show s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ) ≤ s.1 j
      nlinarith
  · simp [hs j]

theorem probabilistic_serial_line_item_wait_exists_eq_zero {n : ℕ} (hn : 1 ≤ n) (b : Fin n → ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) :
    ∃ j, probabilistic_serial_line_item_wait b pref j = 0 := by
  classical
  have hnn : ∀ k, ∀ j, 0 ≤ (probabilistic_serial_phase_state n pref k).1 j := by
    intro k
    induction k with
    | zero => intro j; simp [probabilistic_serial_phase_state]
    | succ k ih =>
      intro j
      have := (ps_wait_zero_phase_fst_le_and_nonneg n pref _ ih j).1
      simpa [probabilistic_serial_phase_state, Function.iterate_succ_apply'] using this
  have hstep : ∀ k j, (probabilistic_serial_phase_state n pref (k + 1)).1 j ≤
      (probabilistic_serial_phase_state n pref k).1 j := by
    intro k j
    have := (ps_wait_zero_phase_fst_le_and_nonneg n pref _ (hnn k) j).2
    simpa [probabilistic_serial_phase_state, Function.iterate_succ_apply'] using this
  have hmono : ∀ k m, k ≤ m → ∀ j, (probabilistic_serial_phase_state n pref m).1 j ≤
      (probabilistic_serial_phase_state n pref k).1 j := by
    intro k m hkm j
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact (hstep m j).trans ih
  let P : ℕ → Prop := fun k =>
    (Finset.univ.filter (fun j' => 0 < (probabilistic_serial_phase_state n pref k).1 j')).Nonempty
  have hP0 : P 0 := ⟨⟨0, hn⟩, by simp [probabilistic_serial_phase_state]⟩
  set K := Nat.findGreatest P (n - 1) with hK
  have hPK : P K := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  obtain ⟨j, hj⟩ := hPK
  have hjpos : 0 < (probabilistic_serial_phase_state n pref K).1 j := (Finset.mem_filter.mp hj).2
  refine ⟨j, ?_⟩
  unfold probabilistic_serial_line_item_wait
  apply Finset.sum_eq_zero
  intro k hk
  rw [dif_neg]
  rintro ⟨h1, h2⟩
  rcases le_or_gt k K with hkK | hkK
  · have := hmono k K hkK j
    linarith
  · have hkn : k ≤ n - 1 := by
      have := Finset.mem_range.mp hk; omega
    exact Nat.findGreatest_is_greatest hkK hkn h2
