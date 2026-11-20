import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionFixedEndpoints
import AFTD.Kb.Tcs.TwoColorPaletteStepIff

/-!
# op874_path_two_palettes_avoid_endpoint

Topic: combinatorics   Node: d7ab63a84931

Provenance: helper lemma. Endpoint refinement for the OP-874 single-defect path-palette reduction.

For a path of two-color palettes, if the color u is absent from some palette, compatible distinct port colors can start with any specified available color and end with the other port different from u.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_path_two_palettes_avoid_endpoint
    {Ω : Type*} [DecidableEq Ω] (P : ℕ → Finset Ω)
    (hcard : ∀ i, (P i).card = 2) (n : ℕ) (x u : Ω)
    (hx : x ∈ P 0) (hmissing : ∃ i ≤ n, u ∉ P i) :
    ∃ f g : ℕ → Ω, f 0 = x ∧ g n ≠ u ∧
      (∀ i ≤ n, f i ∈ P i ∧ g i ∈ P i ∧ f i ≠ g i) ∧
      (∀ i < n, g i ≠ f (i+1)) := by
  classical
  have hequal : ∀ i, (P i).card = (P (i+1)).card := by
    intro i; rw [hcard i, hcard (i+1)]
  have hy : ∃ y ∈ P n, (y = u ∨ u ∉ P n) ∧
      ((∀ i ≤ n, y ∈ P i) → x = y) := by
    by_cases hu : u ∈ P n
    · refine ⟨u, hu, ⟨Or.inl rfl, ?_⟩⟩
      intro hall
      obtain ⟨i, hi, hn⟩ := hmissing
      exact (hn (hall i hi)).elim
    · by_cases hxn : x ∈ P n
      · exact ⟨x, hxn, ⟨Or.inr hu, fun _ => rfl⟩⟩
      · have hnot : ¬ P n ⊆ P 0 := by
          intro hs
          have heq : P n = P 0 := Finset.eq_of_subset_of_card_le hs (by rw [hcard n, hcard 0])
          apply hxn
          rw [heq]
          exact hx
        obtain ⟨y, hyn, hy0⟩ := Finset.not_subset.mp hnot
        exact ⟨y, hyn, ⟨Or.inr hu, fun hall => (hy0 (hall 0 (by omega))).elim⟩⟩
  obtain ⟨y, hyn, hychoice, hycondition⟩ := hy
  obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ :=
    (path_selection_fixed_endpoints P hequal x hx n y hyn).2 hycondition
  have hex : ∀ i : ℕ, ∃ z : Ω, i ≤ n → z ∈ P i ∧ z ≠ f i := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (hcard i)
      by_cases ha : a = f i
      · refine ⟨b, fun _ => ⟨?_, ?_⟩⟩
        · rw [hp]; simp
        · intro hb; exact hab (ha.trans hb.symm)
      · refine ⟨a, fun _ => ⟨?_, ha⟩⟩
        rw [hp]; simp
    · exact ⟨x, fun h => (hi h).elim⟩
  choose g hg using hex
  refine ⟨f, g, hf0, ?_, ?_, ?_⟩
  · intro he
    rcases hychoice with rfl | hu
    · exact (hg n (by omega)).2 (he.trans hfn.symm)
    · exact hu (he ▸ (hg n (by omega)).1)
  · intro i hi
    exact ⟨hfmem i hi, (hg i hi).1, Ne.symm (hg i hi).2⟩
  · intro i hi
    apply (two_color_palette_step_iff (P i) (f i) (g i) (f (i+1))
      (hcard i) (hfmem i (by omega)) (hg i (by omega)).1
      (Ne.symm (hg i (by omega)).2)).2
    exact hfstep i hi
