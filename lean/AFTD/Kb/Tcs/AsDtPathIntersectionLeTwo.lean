import AFTD.Prelude
import AFTD.Kb.Tcs.IsASPath
import AFTD.Kb.Tcs.AsTrace
import AFTD.Kb.Tcs.DtTrace
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.RotCW
import AFTD.Kb.Tcs.Chessboard
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# as_dt_path_intersection_le_two

Topic: combinatorics   Node: dc24fd16ceca

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Section 1

For any natural number n and any coordinate functions a1 and a2 satisfying IsASPath, the intersection of asTrace n a1 and dtTrace n a2 has cardinality at most two.
-/

lemma as_dt_path_intersection_le_two_isASPath_mono {a : ℤ → ℤ} (h : IsASPath a) {t1 t2 : ℤ} (hle : t1 ≤ t2) : a t1 ≤ a t2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t2 = t1 + k := ⟨(t2 - t1).toNat, by omega⟩
  clear hle
  induction' k with k ih
  · simp
  · have hstep : 0 ≤ a (t1 + (k : ℤ) + 1) - a (t1 + (k : ℤ)) := (h (t1 + k)).1
    have h1 : a (t1 + (k : ℤ)) ≤ a (t1 + (k + 1 : ℕ)) := by
      have : (t1 + (k + 1 : ℕ) : ℤ) = t1 + (k : ℤ) + 1 := by push_cast; ring
      rw [this]
      linarith
    have h2 : a t1 ≤ a (t1 + (k : ℤ)) := ih
    linarith

lemma as_dt_path_intersection_le_two_isASPath_sub_mono {a : ℤ → ℤ} (h : IsASPath a) {t1 t2 : ℤ} (hle : t1 ≤ t2) :
    t1 - a t1 ≤ t2 - a t2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t2 = t1 + k := ⟨(t2 - t1).toNat, by omega⟩
  clear hle
  induction' k with k ih
  · simp
  · have hstep : a (t1 + (k : ℤ) + 1) - a (t1 + (k : ℤ)) ≤ 1 := (h (t1 + k)).2.1
    have h1 : t1 + (k : ℤ) - a (t1 + (k : ℤ)) ≤ t1 + (k + 1 : ℕ) - a (t1 + (k + 1 : ℕ)) := by
      have : (t1 + (k + 1 : ℕ) : ℤ) = t1 + (k : ℤ) + 1 := by push_cast; ring
      rw [this]
      linarith
    linarith

lemma as_dt_path_intersection_le_two_isASPath_step_two {a : ℤ → ℤ} (h : IsASPath a) {t1 t2 : ℤ} (h2 : t1 + 2 ≤ t2) : a t1 + 1 ≤ a t2 := by
  have hstep : a t1 + 1 ≤ a (t1 + 2) := (h t1).2.2
  have hmono : a (t1 + 2) ≤ a t2 := as_dt_path_intersection_le_two_isASPath_mono h h2
  linarith

lemma as_dt_path_intersection_le_two_asTrace_order {n : ℕ} {a : ℤ → ℤ} (ha : IsASPath a) (p q : ℕ × ℕ)
    (hp : p ∈ asTrace n a) (hq : q ∈ asTrace n a) :
    (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2) := by
  simp only [asTrace, Finset.mem_filter] at hp hq
  have ap := hp.2; have aq := hq.2
  have h_cases : (↑p.1 + ↑p.2 : ℤ) ≤ ↑q.1 + ↑q.2 ∨ (↑q.1 + ↑q.2 : ℤ) ≤ ↑p.1 + ↑p.2 := by omega
  rcases h_cases with hle | hle
  · left
    have h1 := as_dt_path_intersection_le_two_isASPath_mono ha hle
    have h2 := as_dt_path_intersection_le_two_isASPath_sub_mono ha hle
    constructor <;> omega
  · right
    have h1 := as_dt_path_intersection_le_two_isASPath_mono ha hle
    have h2 := as_dt_path_intersection_le_two_isASPath_sub_mono ha hle
    constructor <;> omega

lemma as_dt_path_intersection_le_two_dtTrace_order {n : ℕ} {a : ℤ → ℤ} (ha : IsASPath a) (p q : ℕ × ℕ)
    (hp : p ∈ dtTrace n a) (hq : q ∈ dtTrace n a) :
    (p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∨ (q.1 ≤ p.1 ∧ p.2 ≤ q.2) := by
  simp only [dtTrace, Finset.mem_image] at hp hq
  obtain ⟨p0, hp0, rfl⟩ := hp
  obtain ⟨q0, hq0, rfl⟩ := hq
  have hp0_cb : p0 ∈ chessboard n := (Finset.mem_filter.mp hp0).1
  have hq0_cb : q0 ∈ chessboard n := (Finset.mem_filter.mp hq0).1
  simp only [chessboard, Finset.mem_product, Finset.mem_range] at hp0_cb hq0_cb
  rcases p0 with ⟨px, py⟩
  rcases q0 with ⟨qx, qy⟩
  simp only [rotCW]
  have h := as_dt_path_intersection_le_two_asTrace_order ha (px, py) (qx, qy) hp0 hq0
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor <;> omega
  · right; constructor <;> omega

lemma as_dt_path_intersection_le_two_col_or_row_of_pairwise (p q r : ℕ × ℕ)
    (hpq : p.1 = q.1 ∨ p.2 = q.2)
    (hpr : p.1 = r.1 ∨ p.2 = r.2)
    (hqr : q.1 = r.1 ∨ q.2 = r.2)
    (dpq : p ≠ q) (dpr : p ≠ r) (dqr : q ≠ r) :
    (p.1 = q.1 ∧ q.1 = r.1) ∨ (p.2 = q.2 ∧ q.2 = r.2) := by
  rcases hpq with h1 | h1
  · rcases hpr with h2 | h2
    · rcases hqr with h3 | h3
      · left; exact ⟨h1, h3⟩
      · exfalso; exact dqr (Prod.ext (by omega) h3)
    · rcases hqr with h3 | h3
      · exfalso; exact dpr (Prod.ext (by omega) h2)
      · exfalso; exact dpq (Prod.ext h1 (by omega))
  · rcases hpr with h2 | h2
    · rcases hqr with h3 | h3
      · exfalso; exact dpq (Prod.ext (by omega) h1)
      · exfalso; exact dpr (Prod.ext h2 (by omega))
    · rcases hqr with h3 | h3
      · exfalso; exact dqr (Prod.ext h3 (by omega))
      · right; exact ⟨h1, h3⟩

lemma as_dt_path_intersection_le_two_not_three_same_fst {n : ℕ} {a : ℤ → ℤ} (ha : IsASPath a) (p q r : ℕ × ℕ)
    (hp : p ∈ asTrace n a) (hq : q ∈ asTrace n a) (hr : r ∈ asTrace n a)
    (dpq : p ≠ q) (dpr : p ≠ r) (dqr : q ≠ r)
    (h1 : p.1 = q.1) (h2 : q.1 = r.1) : False := by
  simp only [asTrace, Finset.mem_filter] at hp hq hr
  have ap := hp.2; have aq := hq.2; have ar := hr.2
  have h_cases : (p.2 < q.2 ∧ q.2 < r.2) ∨ (p.2 < r.2 ∧ r.2 < q.2) ∨
                 (q.2 < p.2 ∧ p.2 < r.2) ∨ (q.2 < r.2 ∧ r.2 < p.2) ∨
                 (r.2 < p.2 ∧ p.2 < q.2) ∨ (r.2 < q.2 ∧ q.2 < p.2) := by
    have dy1 : p.2 ≠ q.2 := fun h => dpq (Prod.ext h1 h)
    have dy2 : p.2 ≠ r.2 := fun h => dpr (Prod.ext (by omega) h)
    have dy3 : q.2 ≠ r.2 := fun h => dqr (Prod.ext h2 h)
    omega
  rcases h_cases with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have hle : (↑p.1 + ↑p.2 : ℤ) + 2 ≤ ↑r.1 + ↑r.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega
  · have hle : (↑p.1 + ↑p.2 : ℤ) + 2 ≤ ↑q.1 + ↑q.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega
  · have hle : (↑q.1 + ↑q.2 : ℤ) + 2 ≤ ↑r.1 + ↑r.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega
  · have hle : (↑q.1 + ↑q.2 : ℤ) + 2 ≤ ↑p.1 + ↑p.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega
  · have hle : (↑r.1 + ↑r.2 : ℤ) + 2 ≤ ↑q.1 + ↑q.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega
  · have hle : (↑r.1 + ↑r.2 : ℤ) + 2 ≤ ↑p.1 + ↑p.2 := by omega
    have hstep := as_dt_path_intersection_le_two_isASPath_step_two ha hle
    omega

lemma as_dt_path_intersection_le_two_not_three_same_snd_dt {n : ℕ} {a : ℤ → ℤ} (ha : IsASPath a) (p q r : ℕ × ℕ)
    (hp : p ∈ dtTrace n a) (hq : q ∈ dtTrace n a) (hr : r ∈ dtTrace n a)
    (dpq : p ≠ q) (dpr : p ≠ r) (dqr : q ≠ r)
    (h1 : p.2 = q.2) (h2 : q.2 = r.2) : False := by
  simp only [dtTrace, Finset.mem_image] at hp hq hr
  obtain ⟨p0, hp0, rfl⟩ := hp
  obtain ⟨q0, hq0, rfl⟩ := hq
  obtain ⟨r0, hr0, rfl⟩ := hr
  have hp0_cb : p0 ∈ chessboard n := (Finset.mem_filter.mp hp0).1
  have hq0_cb : q0 ∈ chessboard n := (Finset.mem_filter.mp hq0).1
  have hr0_cb : r0 ∈ chessboard n := (Finset.mem_filter.mp hr0).1
  simp only [chessboard, Finset.mem_product, Finset.mem_range] at hp0_cb hq0_cb hr0_cb
  rcases p0 with ⟨px, py⟩
  rcases q0 with ⟨qx, qy⟩
  rcases r0 with ⟨rx, ry⟩
  simp only [rotCW] at h1 h2 dpq dpr dqr
  have heq1 : px = qx := by omega
  have heq2 : qx = rx := by omega
  have d01 : (px, py) ≠ (qx, qy) := by intro h; cases h; exact dpq rfl
  have d02 : (px, py) ≠ (rx, ry) := by intro h; cases h; exact dpr rfl
  have d03 : (qx, qy) ≠ (rx, ry) := by intro h; cases h; exact dqr rfl
  exact as_dt_path_intersection_le_two_not_three_same_fst ha (px, py) (qx, qy) (rx, ry) hp0 hq0 hr0 d01 d02 d03 heq1 heq2

/-- An AS path trace and a DT path trace intersect in at most two cells. -/
theorem as_dt_path_intersection_le_two (n : ℕ) (a1 a2 : ℤ → ℤ) (h1 : IsASPath a1) (h2 : IsASPath a2) : (asTrace n a1 ∩ dtTrace n a2).card ≤ 2 := by
  by_contra hc
  have hpos1 : 0 < (asTrace n a1 ∩ dtTrace n a2).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos1
  have hpos2 : 0 < ((asTrace n a1 ∩ dtTrace n a2).erase p).card := by
    rw [Finset.card_erase_of_mem hp]; omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos2
  have hpos3 : 0 < (((asTrace n a1 ∩ dtTrace n a2).erase p).erase q).card := by
    rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem hp]; omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos3
  have hp_mem : p ∈ asTrace n a1 ∩ dtTrace n a2 := hp
  have hq_mem : q ∈ asTrace n a1 ∩ dtTrace n a2 := (Finset.mem_erase.mp hq).2
  have hr_mem : r ∈ asTrace n a1 ∩ dtTrace n a2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).2
  have dpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
  have dpr : p ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1.symm
  have dqr : q ≠ r := (Finset.mem_erase.mp hr).1.symm
  have hp_as := (Finset.mem_inter.mp hp_mem).1
  have hq_as := (Finset.mem_inter.mp hq_mem).1
  have hr_as := (Finset.mem_inter.mp hr_mem).1
  have hp_dt := (Finset.mem_inter.mp hp_mem).2
  have hq_dt := (Finset.mem_inter.mp hq_mem).2
  have hr_dt := (Finset.mem_inter.mp hr_mem).2
  have hpq : p.1 = q.1 ∨ p.2 = q.2 := by
    have has := as_dt_path_intersection_le_two_asTrace_order h1 p q hp_as hq_as
    have hdt := as_dt_path_intersection_le_two_dtTrace_order h2 p q hp_dt hq_dt
    rcases has with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> rcases hdt with ⟨hC, hD⟩ | ⟨hC, hD⟩
    · right; omega
    · left; omega
    · left; omega
    · right; omega
  have hpr : p.1 = r.1 ∨ p.2 = r.2 := by
    have has := as_dt_path_intersection_le_two_asTrace_order h1 p r hp_as hr_as
    have hdt := as_dt_path_intersection_le_two_dtTrace_order h2 p r hp_dt hr_dt
    rcases has with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> rcases hdt with ⟨hC, hD⟩ | ⟨hC, hD⟩
    · right; omega
    · left; omega
    · left; omega
    · right; omega
  have hqr : q.1 = r.1 ∨ q.2 = r.2 := by
    have has := as_dt_path_intersection_le_two_asTrace_order h1 q r hq_as hr_as
    have hdt := as_dt_path_intersection_le_two_dtTrace_order h2 q r hq_dt hr_dt
    rcases has with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> rcases hdt with ⟨hC, hD⟩ | ⟨hC, hD⟩
    · right; omega
    · left; omega
    · left; omega
    · right; omega
  have hline := as_dt_path_intersection_le_two_col_or_row_of_pairwise p q r hpq hpr hqr dpq dpr dqr
  rcases hline with ⟨hcol1, hcol2⟩ | ⟨hrow1, hrow2⟩
  · exact as_dt_path_intersection_le_two_not_three_same_fst h1 p q r hp_as hq_as hr_as dpq dpr dqr hcol1 hcol2
  · exact as_dt_path_intersection_le_two_not_three_same_snd_dt h2 p q r hp_dt hq_dt hr_dt dpq dpr dqr hrow1 hrow2
