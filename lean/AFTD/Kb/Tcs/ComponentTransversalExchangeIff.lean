import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# component_transversal_exchange_iff

Topic: communication   Node: 4878bbef21db

Provenance: helper lemma. arXiv:2611.06626 Claim 2.5

Let T be a transversal of the connected components of a simple graph G, meaning that T intersects every connected component of G and contains at most one vertex per component. For any v ∈ T and any vertex v', the swapped set (T \ {v}) ∪ {v'} intersects every connected component of G if and only if v and v' are in the same connected component of G.
-/

/-- Single-edge swap in a component transversal preserves component coverage if and only if the swapped vertices are reachable. -/
theorem component_transversal_exchange_iff {V : Type*} (G : SimpleGraph V) (T : Set V)
    (h_cov : ∀ v : V, ∃ t ∈ T, G.Reachable v t)
    (h_uniq : ∀ ⦃t1 t2⦄, t1 ∈ T → t2 ∈ T → G.Reachable t1 t2 → t1 = t2)
    (v v' : V) (hv : v ∈ T) :
    (∀ u : V, ∃ t ∈ (T \ {v}) ∪ {v'}, G.Reachable u t) ↔ G.Reachable v v' := by
  constructor
  · intro h
    obtain ⟨t, ht, hr⟩ := h v
    rcases ht with ⟨htT, htv⟩ | rfl
    · exfalso
      have heq := h_uniq hv htT hr
      exact htv (Set.mem_singleton_iff.mpr heq.symm)
    · exact hr
  · intro hvv' u
    obtain ⟨t, ht, hr⟩ := h_cov u
    by_cases heq : t = v
    · subst heq
      exact ⟨v', Set.mem_union_right _ (Set.mem_singleton v'), hr.trans hvv'⟩
    · exact ⟨t, Set.mem_union_left _ ⟨ht, heq⟩, hr⟩
