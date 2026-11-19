import AFTD.Prelude
import AFTD.Kb.Tcs.PathSelectionFixedEndpoints

/-!
# path_selection_of_no_common_color

Topic: graphs   Node: 511d9e351778

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

For a path of finite equal-size palettes with empty total intersection, arbitrary prescribed endpoint colors extend to a compatible selection.
-/

theorem path_selection_of_no_common_color
    {Ω : Type*} [DecidableEq Ω] (P : ℕ → Finset Ω)
    (hcard : ∀ i, (P i).card = (P (i+1)).card)
    (n : ℕ) (x y : Ω) (hx : x ∈ P 0) (hy : y ∈ P n)
    (hcover : ∀ z : Ω, ∃ i ≤ n, z ∉ P i) :
    ∃ g : ℕ → Ω, g 0 = x ∧ g n = y ∧ (∀ i ≤ n, g i ∈ P i) ∧
      (∀ i < n, g (i+1) ∈ P i → g (i+1) = g i) := by
  apply (path_selection_fixed_endpoints P hcard x hx n y hy).2
  intro hall
  obtain ⟨i, hi, hn⟩ := hcover y
  exact (hn (hall i hi)).elim
