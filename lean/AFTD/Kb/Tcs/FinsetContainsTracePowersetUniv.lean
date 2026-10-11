import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetContainsTrace

/-!
# finset_contains_trace_powerset_univ

Topic: combinatorics   Node: b4c3f173f8e9

Provenance: helper lemma. Sanity lemma for finset_contains_trace (arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Sec. 1.1).

The full power set of {0,…,h−1} contains every set system on {0,…,h−1} as a trace.
-/

theorem finset_contains_trace_powerset_univ {h : ℕ} (𝓗 : Finset (Finset (Fin h))) :
    finset_contains_trace (Finset.univ : Finset (Fin h)).powerset 𝓗 := by
  refine ⟨Function.Embedding.refl _, fun e _ => ⟨e, by simp, ?_⟩⟩
  simp
