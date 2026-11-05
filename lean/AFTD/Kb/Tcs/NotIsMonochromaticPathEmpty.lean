import AFTD.Prelude
import AFTD.Kb.Tcs.IsMonochromaticPath
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# not_is_monochromatic_path_empty

Topic: graphs   Node: 2aa5f194fd15

Provenance: helper lemma. arXiv:2611.06362 Section 1

The empty set of vertices is not a monochromatic path in any edge-coloured simple graph G under any edge colouring c : G.edgeSet → C.
-/

/-- The empty set cannot be the vertex set of a monochromatic path. -/
lemma not_is_monochromatic_path_empty {V C : Type*} [DecidableEq V] (G : SimpleGraph V)
    (c : G.edgeSet → C) :
    ¬ is_monochromatic_path G c ∅ := by
  rintro ⟨col, u, v, p, hp, hsp⟩
  have h_mem : u ∈ p.support := p.start_mem_support
  have h : u ∈ (∅ : Finset V) := by
    rw [hsp]
    exact List.mem_toFinset.mpr h_mem
  simp at h
