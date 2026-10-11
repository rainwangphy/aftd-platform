import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetContainsTrace

/-!
# not_finset_contains_trace_empty

Topic: combinatorics   Node: 3df27c6d297d

Provenance: helper lemma. Sanity lemma for finset_contains_trace (arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Sec. 1.1).

The empty set system contains no nonempty set system as a trace.
-/

theorem not_finset_contains_trace_empty {α : Type*} [DecidableEq α] {h : ℕ}
    {𝓗 : Finset (Finset (Fin h))} (h𝓗 : 𝓗.Nonempty) :
    ¬ finset_contains_trace (∅ : Finset (Finset α)) 𝓗 := by
  rintro ⟨φ, hφ⟩
  obtain ⟨e, he⟩ := h𝓗
  obtain ⟨A, hA, -⟩ := hφ e he
  simp at hA
