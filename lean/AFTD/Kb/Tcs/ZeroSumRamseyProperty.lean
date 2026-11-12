import AFTD.Prelude

/-!
# zero_sum_ramsey_property

Topic: combinatorics   Node: ac098ae092ed

Provenance: formalization of a published result. Source: arXiv:2611.14160 Section 1

For a finite graph H and integers m and N, the zero-sum Ramsey property holds if every edge labeling of the complete graph on N vertices with weights in ZMod m contains an injective copy of H whose edge labels sum to zero in ZMod m.
-/

/-- The zero-sum Ramsey property for a graph H modulo m in a complete host graph K_N. -/
def zero_sum_ramsey_property {V : Type*} [Fintype V]
    (H : SimpleGraph V) [Fintype H.edgeSet] (m N : ℕ) : Prop :=
  ∀ w : (SimpleGraph.completeGraph (Fin N)).edgeSet → ZMod m,
    ∃ f : V ↪ Fin N,
      ∑ e : H.edgeSet, w ⟨Sym2.map f e.1, by
        rcases e with ⟨⟨u, v⟩, hadj⟩
        simpa using hadj.ne ∘ (fun h => f.injective h)⟩ = 0
