import AFTD.Prelude
import AFTD.Kb.Tcs.Zycle
import AFTD.Kb.Tcs.TripartiteTuranHypergraph
import AFTD.Kb.Tcs.IsHypergraphHom
import AFTD.Kb.Tcs.TripartiteTuranHypergraphThreeUniform
import AFTD.Kb.Tcs.ZycleHomImpliesClosedWalk
import AFTD.Kb.Tcs.TripartiteTuranPairDigraphNoClosedWalk
import AFTD.Kb.Tcs.PairDigraphAdj

/-!
# zycle_not_div_three_no_hom_tripartite_turan

Topic: combinatorics   Node: 497d7ae6a405

Provenance: formalization of a published result. Source: arXiv:2611.16654 Lemma 3.3

Let ℓ ≥ 2 be an integer with 3 ∤ ℓ. For any family of pairwise disjoint finite sets V : ZMod 3 → Finset α, there is no function f : ZMod ℓ × Fin 2 → α that is a hypergraph homomorphism is_hypergraph_hom from the zycle Z_ℓ to the tripartite Turán construction tripartite_turan_hypergraph V.
-/

/-- There is no hypergraph homomorphism from Z_ℓ to T[V₁, V₂, V₃] when 3 does not divide ℓ. -/
theorem zycle_not_div_three_no_hom_tripartite_turan {α : Type*} [DecidableEq α]
    (ℓ : ℕ) [NeZero ℓ] (hℓ_ge : 2 ≤ ℓ) (hℓ_not_dvd : ¬ 3 ∣ ℓ)
    (V : ZMod 3 → Finset α) (hdisj : ∀ i j : ZMod 3, i ≠ j → Disjoint (V i) (V j)) :
    ¬ ∃ f : ZMod ℓ × Fin 2 → α,
      is_hypergraph_hom (zycle ℓ) (tripartite_turan_hypergraph V) f := by
  rintro ⟨f, hf⟩
  have hwalk := zycle_hom_implies_closed_walk ℓ (tripartite_turan_hypergraph V)
    (tripartite_turan_hypergraph_three_uniform V) f hf
  exact tripartite_turan_pair_digraph_no_closed_walk V hdisj ℓ hℓ_not_dvd hwalk
