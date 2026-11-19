import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionOfNoCommonColor
import AFTD.Kb.Tcs.TwoColorPaletteStepIff

/-!
# path_two_color_palettes_of_no_common_color

Topic: graphs   Node: 03e7c39ca0c3

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

A path of two-color palettes with empty total intersection admits distinct local port colors, any prescribed incoming endpoint colors, and distinct exposed colors on consecutive vertices.
-/

theorem path_two_color_palettes_of_no_common_color
    {Ω : Type*} [DecidableEq Ω] (P : ℕ → Finset Ω)
    (hcard : ∀ i, (P i).card = 2) (n : ℕ) (x y : Ω)
    (hx : x ∈ P 0) (hy : y ∈ P n)
    (hcover : ∀ z : Ω, ∃ i ≤ n, z ∉ P i) :
    ∃ f g : ℕ → Ω, f 0 = x ∧ f n = y ∧
      (∀ i ≤ n, f i ∈ P i ∧ g i ∈ P i ∧ f i ≠ g i) ∧
      (∀ i < n, g i ≠ f (i+1)) := by
  classical
  have hequal : ∀ i, (P i).card = (P (i+1)).card := by
    intro i
    rw [hcard i, hcard (i+1)]
  obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ :=
    path_selection_of_no_common_color P hequal n x y hx hy hcover
  have hex : ∀ i : ℕ, ∃ z : Ω, i ≤ n → z ∈ P i ∧ z ≠ f i := by
    intro i
    by_cases hi : i ≤ n
    · obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (hcard i)
      by_cases ha : a = f i
      · refine ⟨b, fun _ => ⟨?_, ?_⟩⟩
        · rw [hp]; simp
        · intro hb
          exact hab (ha.trans hb.symm)
      · refine ⟨a, fun _ => ⟨?_, ha⟩⟩
        rw [hp]; simp
    · exact ⟨x, fun h => (hi h).elim⟩
  choose g hg using hex
  refine ⟨f, g, hf0, hfn, ?_, ?_⟩
  · intro i hi
    exact ⟨hfmem i hi, (hg i hi).1, Ne.symm (hg i hi).2⟩
  · intro i hi
    apply (two_color_palette_step_iff (P i) (f i) (g i) (f (i+1))
      (hcard i) (hfmem i (by omega)) (hg i (by omega)).1
      (Ne.symm (hg i (by omega)).2)).2
    exact hfstep i hi
