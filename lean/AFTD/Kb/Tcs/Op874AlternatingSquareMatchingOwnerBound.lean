import AFTD.Prelude
import AFTD.Kb.Tcs.Op874SelectedFactorEdgeForcesOuterColorsDistinct
import AFTD.Kb.Tcs.CycleMatchingLowColor
import AFTD.Kb.Tcs.CycleFactorHighColor

/-!
# op874_alternating_square_matching_owner_bound

Topic: graphs   Node: 0868ae29a925

Provenance: helper lemma. OP-874 fixed-pair outer-square local counting; experiment 41917.


-/

theorem op874_alternating_square_matching_owner_bound
    (b : Fin 4 → Bool) (edge : Fin 4 → Fin 4) (h : Fin 4 → Fin 3 → Fin 6)
    (hproper : ∀ j, edge (j-1) ≠ edge j)
    (hinj : ∀ j, Function.Injective (h j))
    (havoid : ∀ j p, h j p ≠ cycle_matching_low_color (b j) ∧
      h j p ≠ cycle_factor_high_color (edge (j-1)) ∧ h j p ≠ cycle_factor_high_color (edge j))
    (hstrong : ∀ i, h i 0 ≠ h (i+1) 1 ∧ h i 0 ≠ h (i+1) 2 ∧
      h i 2 ≠ h (i+1) 1 ∧ h i 2 ≠ h (i+1) 2)
    (hpart : ∀ i, (if h i 0 = cycle_matching_low_color (!b i) then 1 else 0 : ℕ) +
      (if h i 1 = cycle_matching_low_color (!b i) then 1 else 0) +
      (if h i 2 = cycle_matching_low_color (!b i) then 1 else 0) = 1)
    (hchord : (if h 0 2 = cycle_matching_low_color (!b 0) then 1 else 0 : ℕ) +
      (if h 2 2 = cycle_matching_low_color (!b 2) then 1 else 0) = 1)
    (hglobal : ∀ i, h i 1 ≠ cycle_matching_low_color (!b i) →
      h (i+1) 0 ≠ cycle_matching_low_color (!b (i+1)) → edge i = 0 ∨ edge i = 1) :
    (if h 0 2 = cycle_matching_low_color (!b 0) then 1 else 0 : ℕ) +
    (if h 1 2 = cycle_matching_low_color (!b 1) then 1 else 0) +
    (if h 2 2 = cycle_matching_low_color (!b 2) then 1 else 0) +
    (if h 3 2 = cycle_matching_low_color (!b 3) then 1 else 0) ≤ 2 := by
  classical
  let s : Fin 4 → Fin 3 → ℕ := fun i j => if h i j = cycle_matching_low_color (!b i) then 1 else 0
  have s0 (i : Fin 4) (j : Fin 3) (hs : s i j=0) : h i j ≠ cycle_matching_low_color (!b i) := by
    intro hh
    have : s i j=1 := by simp [s,hh]
    omega
  have s1 (i : Fin 4) (j : Fin 3) (hs : s i j=1) : h i j = cycle_matching_low_color (!b i) := by
    by_contra hh
    have : s i j=0 := by simp [s,hh]
    omega
  have unselected (i : Fin 4) (ha : s i 1=0) (hb : s (i+1) 0=0) : edge i=0 ∨ edge i=1 :=
    hglobal i (s0 i 1 ha) (s0 (i+1) 0 hb)
  have impossible (i : Fin 4)
      (hsel : h i 1 = cycle_matching_low_color (!b i) ∨
        h (i+1) 0 = cycle_matching_low_color (!b (i+1)))
      (ha : edge (i+1)=0 ∨ edge (i+1)=1)
      (hb : edge (i+2)=0 ∨ edge (i+2)=1)
      (hc : edge (i+3)=0 ∨ edge (i+3)=1) : False := by
    have hdiff := op874_selected_factor_edge_forces_outer_colors_distinct 4 b edge h i hproper hinj havoid (hstrong i) hsel
    have h1 := hproper (i+2)
    have h2 := hproper (i+3)
    have idx1 : (i+2)-1=i+1 := by fin_cases i <;> decide
    have idx2 : (i+3)-1=i+2 := by fin_cases i <;> decide
    have idx3 : i-1=i+3 := by fin_cases i <;> decide
    rw [idx1] at h1
    rw [idx2] at h2
    rw [idx3] at hdiff
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> simp_all
  have p0 : s 0 0+s 0 1+s 0 2=1 := hpart 0
  have p1 : s 1 0+s 1 1+s 1 2=1 := hpart 1
  have p2 : s 2 0+s 2 1+s 2 2=1 := hpart 2
  have p3 : s 3 0+s 3 1+s 3 2=1 := hpart 3
  have chord : s 0 2+s 2 2=1 := hchord
  change s 0 2+s 1 2+s 2 2+s 3 2 ≤ 2
  by_contra hn
  have a1 : s 1 2=1 := by omega
  have a3 : s 3 2=1 := by omega
  have z10 : s 1 0=0 := by omega
  have z11 : s 1 1=0 := by omega
  have z30 : s 3 0=0 := by omega
  have z31 : s 3 1=0 := by omega
  by_cases h02 : s 0 2=0
  · have a2 : s 2 2=1 := by omega
    have z20 : s 2 0=0 := by omega
    have z21 : s 2 1=0 := by omega
    by_cases h00 : s 0 0=1
    · have z01 : s 0 1=0 := by omega
      apply impossible 3 (Or.inr (by simpa using s1 0 0 h00))
      · simpa using unselected 0 z01 z10
      · simpa using unselected 1 z11 z20
      · simpa using unselected 2 z21 z30
    · have a01 : s 0 1=1 := by omega
      have z00 : s 0 0=0 := by omega
      apply impossible 0 (Or.inl (s1 0 1 a01))
      · simpa using unselected 1 z11 z20
      · simpa using unselected 2 z21 z30
      · simpa using unselected 3 z31 z00
  · have a0 : s 0 2=1 := by omega
    have z00 : s 0 0=0 := by omega
    have z01 : s 0 1=0 := by omega
    have z22 : s 2 2=0 := by omega
    by_cases h20 : s 2 0=1
    · have z21 : s 2 1=0 := by omega
      apply impossible 1 (Or.inr (by simpa using s1 2 0 h20))
      · simpa using unselected 2 z21 z30
      · simpa using unselected 3 z31 z00
      · simpa using unselected 0 z01 z10
    · have a21 : s 2 1=1 := by omega
      have z20 : s 2 0=0 := by omega
      apply impossible 2 (Or.inl (s1 2 1 a21))
      · simpa using unselected 3 z31 z00
      · simpa using unselected 0 z01 z10
      · simpa using unselected 1 z11 z20
