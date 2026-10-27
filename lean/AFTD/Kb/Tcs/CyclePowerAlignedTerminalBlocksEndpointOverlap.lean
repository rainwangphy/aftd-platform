import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerTerminalBlocks
import AFTD.Kb.Tcs.CyclePowerAlignedEndBlocksEndpointOverlap
import AFTD.Kb.Tcs.CyclePowerEndBlocks

/-!
# cycle_power_aligned_terminal_blocks_endpoint_overlap

Topic: combinatorics   Node: 31dd851e013e

Provenance: helper lemma. Uniform conditional colour-rigidity extension for OP-205 / RT-1, related to arXiv:2610.15635 Section 3. This remains a lemma to prove, not a classification of covers or a research advance.

For the uniform nested block family with a three-quarter terminal class, every other class through the old endpoint intersects the class translated by 4R, in either global terminal orientation.
-/

theorem cycle_power_aligned_terminal_blocks_endpoint_overlap
    (R a b p q c : ℤ) (side : Bool) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hA : a ≤ R) (hB : b ≤ R) (hDa : 2 * a ∣ 4 * R) (hDb : 2 * b ∣ 4 * R)
    (hchain : a = b ∨ 2 * a ∣ b ∨ 2 * b ∣ a)
    (hp : a ∣ p + c) (hpo : a < R → 2 * a ∣ p + c - a)
    (hq : b ∣ q + c) (hqo : b < R → 2 * b ∣ q + c - b)
    (hact : cycle_power_terminal_blocks R b q (p + 4 * R - 1) side) (hqp : q ≠ p) :
    ∃ u, cycle_power_terminal_blocks R b q u side ∧
      cycle_power_terminal_blocks R a (p + 4 * R) u side := by
  by_cases haR : a < R
  · by_cases hbR : b < R
    · have ha_ne : a ≠ R := by omega
      have hb_ne : b ≠ R := by omega
      unfold cycle_power_terminal_blocks at hact ⊢
      rw [if_neg hb_ne] at hact
      have h1 : 2 * a ≤ 4 * R := by omega
      have h2 : 2 * b ≤ 4 * R := by omega
      have hpo' : 2 * a < 4 * R → 2 * a ∣ p + c - a := fun _ => hpo haR
      have hqo' : 2 * b < 4 * R → 2 * b ∣ q + c - b := fun _ => hqo hbR
      obtain ⟨u, hu1, hu2⟩ := cycle_power_aligned_end_blocks_endpoint_overlap
        (4 * R) a b p q c ha hb h1 h2 hDa hDb hchain hp hpo' hq hqo' hact hqp
      refine ⟨u, ?_⟩
      rw [if_neg hb_ne, if_neg ha_ne]
      exact ⟨hu1, hu2⟩
    · have hb : b = R := by omega
      have ha_ne : a ≠ R := by omega
      have h2aR : 2 * a ∣ R := by
        rcases hchain with heq | h1 | h2
        · omega
        · rwa [hb] at h1
        · have : 2 * b ≤ a := Int.le_of_dvd ha h2
          omega
      have hqR : R ∣ q + c := by rwa [hb] at hq
      have hpo' := hpo haR
      have hda_of_hdp : 2 * a ∣ p + c → False := by
        intro hdp
        have h1 : 2 * a ∣ (p + c) - (p + c - a) := dvd_sub hdp hpo'
        have heq : (p + c) - (p + c - a) = a := by ring
        rw [heq] at h1
        have : 2 * a ≤ a := Int.le_of_dvd ha h1
        omega
      have hno_end : ¬ (q = p + 2 * R ∨ q = p + 3 * R) := by
        intro hq_eq
        have hdq : 2 * a ∣ q + c := dvd_trans h2aR hqR
        rcases hq_eq with hq2 | hq3
        · apply hda_of_hdp
          have heq : p + c = (q + c) - 2 * R := by omega
          rw [heq]
          exact dvd_sub hdq (dvd_mul_of_dvd_right h2aR 2)
        · apply hda_of_hdp
          have heq : p + c = (q + c) - 3 * R := by omega
          rw [heq]
          exact dvd_sub hdq (dvd_mul_of_dvd_right h2aR 3)
      refine ⟨p + 4 * R, ?_, ?_⟩
      · unfold cycle_power_terminal_blocks at hact ⊢
        rw [if_pos hb] at hact ⊢
        cases side
        · rcases hact with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have : p + 4 * R < q + R := by
              by_contra!
              have : q = p + 3 * R := by omega
              exact hno_end (Or.inr this)
            exact Or.inl ⟨by omega, by omega⟩
          · have : p < q := by
              by_contra!
              have : p = q := by omega
              exact hqp this.symm
            exact Or.inr ⟨by omega, by omega⟩
        · rcases hact with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have : p + 4 * R < q + 2 * R := by
              by_contra!
              have : q = p + 2 * R := by omega
              exact hno_end (Or.inl this)
            exact Or.inl ⟨by omega, by omega⟩
          · have : p < q := by
              by_contra!
              have : p = q := by omega
              exact hqp this.symm
            exact Or.inr ⟨by omega, by omega⟩
      · unfold cycle_power_terminal_blocks cycle_power_end_blocks
        rw [if_neg ha_ne]
        exact Or.inl ⟨by omega, by omega⟩
  · have ha : a = R := by omega
    by_cases hbR : b < R
    · have hb_ne : b ≠ R := by omega
      have h2bR : 2 * b ∣ R := by
        rcases hchain with heq | h1 | h2
        · omega
        · have : 2 * a ≤ b := Int.le_of_dvd hb h1
          omega
        · rwa [ha] at h2
      have hpR : R ∣ p + c := by rwa [ha] at hp
      have h2bp : 2 * b ∣ p + c := dvd_trans h2bR hpR
      have hqo' := hqo hbR
      unfold cycle_power_terminal_blocks at hact ⊢
      rw [if_neg hb_ne] at hact
      simp only [if_neg hb_ne, if_pos ha]
      unfold cycle_power_end_blocks at hact ⊢
      rcases hact with hfirst | hlast
      · have hz : 2 * b ∣ q - p - 4 * R + b := by
          have hh : 2 * b ∣ ((q + c - b) - (p + c)) - (4 * R) + (2 * b) := by
            refine dvd_add (dvd_sub (dvd_sub hqo' h2bp) ?_) (dvd_refl _)
            exact dvd_mul_of_dvd_right h2bR 4
          have heq : ((q + c - b) - (p + c)) - (4 * R) + (2 * b) = q - p - 4 * R + b := by ring
          rwa [heq] at hh
        have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
          (by omega : 0 ≤ q - p - 4 * R + b)
          (by omega : q - p - 4 * R + b < 2 * b) hz
        have hqeq : q = p + 4 * R - b := by omega
        refine ⟨q + 4 * R - 1, Or.inr ⟨by omega, by omega⟩, ?_⟩
        cases side
        · right
          constructor <;> omega
        · right
          constructor <;> omega
      · have hpq : p < q := by omega
        refine ⟨p + 4 * R, Or.inr ⟨by omega, by omega⟩, ?_⟩
        cases side
        · left
          constructor <;> omega
        · left
          constructor <;> omega
    · have hb : b = R := by omega
      have hd : R ∣ q - p := by
        have hpR : R ∣ p + c := by rwa [ha] at hp
        have hqR : R ∣ q + c := by rwa [hb] at hq
        have hh : R ∣ (q + c) - (p + c) := dvd_sub hqR hpR
        have heq : (q + c) - (p + c) = q - p := by ring
        rwa [heq] at hh
      unfold cycle_power_terminal_blocks at hact ⊢
      simp only [if_pos ha, if_pos hb] at hact ⊢
      cases side
      · rcases hact with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hz : R ∣ q - p - 3 * R := by
            have hh : R ∣ (q - p) - 3 * R := dvd_sub hd (dvd_mul_of_dvd_right (dvd_refl R) 3)
            exact hh
          have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
            (by omega : 0 ≤ q - p - 3 * R)
            (by omega : q - p - 3 * R < R) hz
          have hqeq : q = p + 3 * R := by omega
          refine ⟨p + 6 * R, ?_, ?_⟩
          · right
            constructor <;> omega
          · right
            constructor <;> omega
        · have hpq : p < q := by omega
          refine ⟨p + 4 * R, ?_, ?_⟩
          · right
            constructor <;> omega
          · left
            constructor <;> omega
      · rcases hact with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hz : R ∣ q - p - 2 * R := by
            have hh : R ∣ (q - p) - 2 * R := dvd_sub hd (dvd_mul_of_dvd_right (dvd_refl R) 2)
            exact hh
          have hge : 0 ≤ q - p - 2 * R := by omega
          have hlt : q - p - 2 * R < 2 * R := by omega
          by_cases hcase : q - p - 2 * R < R
          · have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hge hcase hz
            have hqeq : q = p + 2 * R := by omega
            refine ⟨p + 5 * R, ?_, ?_⟩
            · right
              constructor <;> omega
            · left
              constructor <;> omega
          · have hz2 : R ∣ q - p - 3 * R := by
              have hh : R ∣ (q - p - 2 * R) - R := dvd_sub hz (dvd_refl R)
              have heq : (q - p - 2 * R) - R = q - p - 3 * R := by ring
              rwa [heq] at hh
            have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt
              (by omega : 0 ≤ q - p - 3 * R)
              (by omega : q - p - 3 * R < R) hz2
            have hqeq : q = p + 3 * R := by omega
            refine ⟨p + 4 * R, ?_, ?_⟩
            · left
              constructor <;> omega
            · left
              constructor <;> omega
        · have hpq : p < q := by omega
          refine ⟨p + 4 * R, ?_, ?_⟩
          · right
            constructor <;> omega
          · left
            constructor <;> omega
