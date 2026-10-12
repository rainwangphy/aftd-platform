import AFTD.Prelude
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# not_is_string_attractor_empty

Topic: combinatorics   Node: 80e436d0f5a4

Provenance: helper lemma. Sanity lemma for is_string_attractor (arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Definition 3.1).

The empty set is not a string attractor of a nonempty word.
-/

theorem not_is_string_attractor_empty {α : Type*} [DecidableEq α] {w : List α} (hw : w ≠ []) :
    ¬ is_string_attractor w ∅ := by
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := h w hw (List.infix_refl w)
  simp at hx
