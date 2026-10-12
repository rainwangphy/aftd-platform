import AFTD.Prelude
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# word_occurrence_coverage_nonempty

Topic: combinatorics   Node: f546e46646fc

Provenance: helper lemma. Sanity lemma for word_occurrence_coverage (arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.1).

The coverage of a nonempty factor of w is nonempty.
-/

theorem word_occurrence_coverage_nonempty {α : Type*} [DecidableEq α] {w x : List α}
    (hx : x ≠ []) (hxw : x <:+: w) : (word_occurrence_coverage w x).Nonempty := by
  obtain ⟨s, t, rfl⟩ := hxw
  refine ⟨s.length + 1, ?_⟩
  have hlen : 0 < x.length := List.length_pos_iff.2 hx
  simp only [word_occurrence_coverage, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
    List.length_append]
  refine ⟨s.length + 1, ⟨⟨by omega, by omega⟩, ?_⟩, le_rfl, by omega⟩
  simp
