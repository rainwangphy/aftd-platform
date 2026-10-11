import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetContainsTrace

/-!
# finset_contains_trace_of_subset

Topic: combinatorics   Node: bdedcf5cd4b8

Provenance: helper lemma. Sanity lemma for finset_contains_trace (arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Sec. 1.1).

Containing H as a trace is monotone: if F ⊆ F' and F contains H as a trace, so does F'.
-/

theorem finset_contains_trace_of_subset {α : Type*} [DecidableEq α] {h : ℕ}
    {𝓕 𝓕' : Finset (Finset α)} {𝓗 : Finset (Finset (Fin h))} (hsub : 𝓕 ⊆ 𝓕')
    (hc : finset_contains_trace 𝓕 𝓗) : finset_contains_trace 𝓕' 𝓗 := by
  obtain ⟨φ, hφ⟩ := hc
  refine ⟨φ, fun e he => ?_⟩
  obtain ⟨A, hA, hAe⟩ := hφ e he
  exact ⟨A, hsub hA, hAe⟩
