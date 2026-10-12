import AFTD.Prelude
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# word_occurrence_coverage_subset

Topic: combinatorics   Node: 5a624477bc14

Provenance: helper lemma. Sanity lemma for word_occurrence_coverage (arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.1).

Every coverage Cov_w(x) is a set of positions of w, i.e. contained in [1, |w|].
-/

theorem word_occurrence_coverage_subset {α : Type*} [DecidableEq α] (w x : List α) :
    word_occurrence_coverage w x ⊆ Finset.Icc 1 w.length := by
  intro q hq
  simp only [word_occurrence_coverage, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_Icc] at hq ⊢
  obtain ⟨p, ⟨⟨hp1, hpw⟩, hocc⟩, hpq, hqx⟩ := hq
  have hlen := congrArg List.length hocc
  rw [List.length_take, List.length_drop] at hlen
  omega
