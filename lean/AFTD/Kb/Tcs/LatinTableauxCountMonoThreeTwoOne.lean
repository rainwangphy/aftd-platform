import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTableaux

/-!
# latin_tableaux_count_mono_three_two_one

Topic: combinatorics   Node: 39c104cbbccc

Provenance: helper lemma. arXiv:2610.29291 Conjecture 6.1

The number of Latin tableaux of shape (3, 2, 1) is at most the number of Latin tableaux of shape (3, 3, 1), verifying Conjecture 6.1 for the addition of a box to the middle row of (3, 2, 1).
-/

def latin_tableaux_count_mono_three_two_one_tab321 (hw : [3,2,1].SortedGE)
    (c : (YoungDiagram.ofRowLens [3,2,1] hw).cells) : ℕ :=
  if c.1.1 = 0 then (if c.1.2 = 0 then 3 else if c.1.2 = 1 then 2 else 1)
  else if c.1.1 = 1 then (if c.1.2 = 0 then 2 else 1) else 1

def latin_tableaux_count_mono_three_two_one_tab331 (hw : [3,3,1].SortedGE)
    (c : (YoungDiagram.ofRowLens [3,3,1] hw).cells) : ℕ :=
  if c.1.1 = 0 then (if c.1.2 = 0 then 2 else if c.1.2 = 1 then 1 else 3)
  else if c.1.1 = 1 then (if c.1.2 = 0 then 3 else if c.1.2 = 1 then 2 else 1)
  else 1

theorem latin_tableaux_count_mono_three_two_one_tab321_eq (hw : [3,2,1].SortedGE)
    (T : (YoungDiagram.ofRowLens [3,2,1] hw).cells → ℕ)
    (hT : T ∈ latin_tableaux (YoungDiagram.ofRowLens [3,2,1] hw)) :
    T = latin_tableaux_count_mono_three_two_one_tab321 hw := by
  let c00 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(0,0), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  let c01 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(0,1), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  let c02 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(0,2), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  let c10 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(1,0), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  let c11 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(1,1), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  let c20 : (YoungDiagram.ofRowLens [3,2,1] hw).cells := ⟨(2,0), by rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]; exact ⟨by decide, by decide⟩⟩
  have hbounds := (Finset.mem_filter.mp hT).1
  rw [Fintype.mem_piFinset] at hbounds
  have hrow := (Finset.mem_filter.mp hT).2.1
  have hcol := (Finset.mem_filter.mp hT).2.2
  have hrl0 : (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 0 = 3 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,2,1]) (hw := hw) ⟨0, by decide⟩; simpa using this
  have hrl1 : (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 1 = 2 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,2,1]) (hw := hw) ⟨1, by decide⟩; simpa using this
  have hrl2 : (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 2 = 1 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,2,1]) (hw := hw) ⟨2, by decide⟩; simpa using this
  have h20 : T c20 = 1 := by
    have hle : T c20 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 2 := (Finset.mem_Icc.mp (hbounds c20)).2
    have hge : 1 ≤ T c20 := (Finset.mem_Icc.mp (hbounds c20)).1
    rw [hrl2] at hle; omega
  have h10 : T c10 = 2 := by
    have hle : T c10 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 1 := (Finset.mem_Icc.mp (hbounds c10)).2
    have hge : 1 ≤ T c10 := (Finset.mem_Icc.mp (hbounds c10)).1
    rw [hrl1] at hle
    have hne : T c10 ≠ 1 := by
      intro h
      have hh := hcol c10 c20 (by rfl) (by rw [h, h20])
      simp only [c10, c20] at hh
      omega
    omega
  have h00v : T c00 = 3 := by
    have hle : T c00 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 0 := (Finset.mem_Icc.mp (hbounds c00)).2
    have hge : 1 ≤ T c00 := (Finset.mem_Icc.mp (hbounds c00)).1
    rw [hrl0] at hle
    have hne1 : T c00 ≠ 1 := by
      intro h
      have hh := hcol c00 c20 (by rfl) (by rw [h, h20])
      simp only [c00, c20] at hh
      omega
    have hne2 : T c00 ≠ 2 := by
      intro h
      have hh := hcol c00 c10 (by rfl) (by rw [h, h10])
      simp only [c00, c10] at hh
      omega
    omega
  have h11v : T c11 = 1 := by
    have hle : T c11 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 1 := (Finset.mem_Icc.mp (hbounds c11)).2
    have hge : 1 ≤ T c11 := (Finset.mem_Icc.mp (hbounds c11)).1
    rw [hrl1] at hle
    have hne : T c11 ≠ 2 := by
      intro h
      have hh := hrow c11 c10 (by rfl) (by rw [h, h10])
      simp only [c11, c10] at hh
      omega
    omega
  have h01v : T c01 = 2 := by
    have hle : T c01 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 0 := (Finset.mem_Icc.mp (hbounds c01)).2
    have hge : 1 ≤ T c01 := (Finset.mem_Icc.mp (hbounds c01)).1
    rw [hrl0] at hle
    have hne3 : T c01 ≠ 3 := by
      intro h
      have hh := hrow c01 c00 (by rfl) (by rw [h, h00v])
      simp only [c01, c00] at hh
      omega
    have hne1 : T c01 ≠ 1 := by
      intro h
      have hh := hcol c01 c11 (by rfl) (by rw [h, h11v])
      simp only [c01, c11] at hh
      omega
    omega
  have h02v : T c02 = 1 := by
    have hle : T c02 ≤ (YoungDiagram.ofRowLens [3,2,1] hw).rowLen 0 := (Finset.mem_Icc.mp (hbounds c02)).2
    have hge : 1 ≤ T c02 := (Finset.mem_Icc.mp (hbounds c02)).1
    rw [hrl0] at hle
    have hne3 : T c02 ≠ 3 := by
      intro h
      have hh := hrow c02 c00 (by rfl) (by rw [h, h00v])
      simp only [c02, c00] at hh
      omega
    have hne2 : T c02 ≠ 2 := by
      intro h
      have hh := hrow c02 c01 (by rfl) (by rw [h, h01v])
      simp only [c02, c01] at hh
      omega
    omega
  funext c
  rcases c with ⟨⟨i,j⟩, hc⟩
  have hi : i < 3 := by
    have h := hc; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
  have hj : j < [3,2,1][i] := by
    have h := hc; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
  interval_cases i
  · have hj' : j < 3 := by simpa using hj
    interval_cases j <;> simp [latin_tableaux_count_mono_three_two_one_tab321, c00, c01, c02, h00v, h01v, h02v]
  · have hj' : j < 2 := by simpa using hj
    interval_cases j <;> simp [latin_tableaux_count_mono_three_two_one_tab321, c10, c11, h10, h11v]
  · have hj' : j < 1 := by simpa using hj
    interval_cases j
    simp [latin_tableaux_count_mono_three_two_one_tab321, c20, h20]

theorem latin_tableaux_count_mono_three_two_one_tab331_mem (hw : [3,3,1].SortedGE) :
    latin_tableaux_count_mono_three_two_one_tab331 hw ∈ latin_tableaux (YoungDiagram.ofRowLens [3,3,1] hw) := by
  have hrl0 : (YoungDiagram.ofRowLens [3,3,1] hw).rowLen 0 = 3 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,3,1]) (hw := hw) ⟨0, by decide⟩; simpa using this
  have hrl1 : (YoungDiagram.ofRowLens [3,3,1] hw).rowLen 1 = 3 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,3,1]) (hw := hw) ⟨1, by decide⟩; simpa using this
  have hrl2 : (YoungDiagram.ofRowLens [3,3,1] hw).rowLen 2 = 1 := by
    have := YoungDiagram.rowLen_ofRowLens (w := [3,3,1]) (hw := hw) ⟨2, by decide⟩; simpa using this
  refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro c
    rcases c with ⟨⟨i,j⟩, hc⟩
    have hi : i < 3 := by
      have h := hc; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
    have hj : j < [3,3,1][i] := by
      have h := hc; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
    rw [Finset.mem_Icc]
    interval_cases i
    · have hj' : j < 3 := by simpa using hj
      interval_cases j <;> simp [latin_tableaux_count_mono_three_two_one_tab331, hrl0]
    · have hj' : j < 3 := by simpa using hj
      interval_cases j <;> simp [latin_tableaux_count_mono_three_two_one_tab331, hrl1]
    · have hj' : j < 1 := by simpa using hj
      interval_cases j <;> simp [latin_tableaux_count_mono_three_two_one_tab331, hrl2]
  · intro c₁ c₂ hrow hval
    rcases c₁ with ⟨⟨i₁,j₁⟩, hc₁⟩
    rcases c₂ with ⟨⟨i₂,j₂⟩, hc₂⟩
    have hi₁ : i₁ < 3 := by
      have h := hc₁; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
    have hj₁ : j₁ < [3,3,1][i₁] := by
      have h := hc₁; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
    have hi₂ : i₂ < 3 := by
      have h := hc₂; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
    have hj₂ : j₂ < [3,3,1][i₂] := by
      have h := hc₂; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
    subst hrow
    interval_cases i₁
    · have hj₁' : j₁ < 3 := by simpa using hj₁
      have hj₂' : j₂ < 3 := by simpa using hj₂
      interval_cases j₁ <;> interval_cases j₂ <;> simp_all [latin_tableaux_count_mono_three_two_one_tab331]
    · have hj₁' : j₁ < 3 := by simpa using hj₁
      have hj₂' : j₂ < 3 := by simpa using hj₂
      interval_cases j₁ <;> interval_cases j₂ <;> simp_all [latin_tableaux_count_mono_three_two_one_tab331]
    · have hj₁' : j₁ < 1 := by simpa using hj₁
      have hj₂' : j₂ < 1 := by simpa using hj₂
      interval_cases j₁ <;> interval_cases j₂ <;> simp_all [latin_tableaux_count_mono_three_two_one_tab331]
  · intro c₁ c₂ hcol hval
    rcases c₁ with ⟨⟨i₁,j₁⟩, hc₁⟩
    rcases c₂ with ⟨⟨i₂,j₂⟩, hc₂⟩
    have hi₁ : i₁ < 3 := by
      have h := hc₁; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
    have hj₁ : j₁ < [3,3,1][i₁] := by
      have h := hc₁; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
    have hi₂ : i₂ < 3 := by
      have h := hc₂; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.1
    have hj₂ : j₂ < [3,3,1][i₂] := by
      have h := hc₂; rw [YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens] at h; exact h.2
    subst hcol
    have hb1 : j₁ < 3 := by
      have hle : [3,3,1][i₁] ≤ 3 := by
        interval_cases i₁ <;> simp
      omega
    interval_cases j₁ <;> interval_cases i₁ <;> interval_cases i₂ <;> simp_all [latin_tableaux_count_mono_three_two_one_tab331]

/-- Monotonicity of Latin tableaux count for the transition (3, 2, 1) to (3, 3, 1). -/
theorem latin_tableaux_count_mono_three_two_one :
    (latin_tableaux (YoungDiagram.ofRowLens [3, 2, 1] (by decide))).card ≤
    (latin_tableaux (YoungDiagram.ofRowLens [3, 3, 1] (by decide))).card := by
  have hw321 : [3,2,1].SortedGE := by decide
  have hw331 : [3,3,1].SortedGE := by decide
  have hle : (latin_tableaux (YoungDiagram.ofRowLens [3,2,1] hw321)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro T hT S hS
    rw [latin_tableaux_count_mono_three_two_one_tab321_eq hw321 T hT,
        latin_tableaux_count_mono_three_two_one_tab321_eq hw321 S hS]
  have hpos : 1 ≤ (latin_tableaux (YoungDiagram.ofRowLens [3,3,1] hw331)).card :=
    Finset.card_pos.mpr ⟨latin_tableaux_count_mono_three_two_one_tab331 hw331,
      latin_tableaux_count_mono_three_two_one_tab331_mem hw331⟩
  calc (latin_tableaux (YoungDiagram.ofRowLens [3, 2, 1] (by decide))).card
      = (latin_tableaux (YoungDiagram.ofRowLens [3,2,1] hw321)).card := rfl
    _ ≤ 1 := hle
    _ ≤ (latin_tableaux (YoungDiagram.ofRowLens [3,3,1] hw331)).card := hpos
    _ = (latin_tableaux (YoungDiagram.ofRowLens [3, 3, 1] (by decide))).card := rfl
