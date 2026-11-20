import AFTD.Prelude
import AFTD.Kb.Tcs.MatchableAnticompleteIntersectionEven

/-!
# matchable_set_even_on_forced_bridge_sides

Topic: graphs   Node: 31347cc3b77f

Provenance: helper lemma. OP-1957 first-cut parity of every later matchable bridge shore.

If a vertex set induces a perfect matching and avoids one endpoint of the unique edge between two graph shores, it meets each shore in an even number of vertices.
-/

theorem matchable_set_even_on_forced_bridge_sides {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A B W : Finset V) (u v : V) (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ) (hu : u ∈ A) (hv : v ∈ B) (hcut : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v) (havoid : u ∉ W ∨ v ∉ W) (hmatch : ∃ P : (G.induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching) : Even (W ∩ A).card ∧ Even (W ∩ B).card := by
  classical
  have hA : ∀ a ∈ W, a ∈ A → ∀ b ∈ W, b ∉ A → ¬ G.Adj a b := by
    intro a ha haA b hb hbA hab
    have hbB : b ∈ B := by
      have hbU : b ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ b
      exact (Finset.mem_union.mp hbU).resolve_left hbA
    obtain ⟨hau,hbv⟩ := hcut a haA b hbB hab
    rcases havoid with hn | hn
    · exact hn (hau ▸ ha)
    · exact hn (hbv ▸ hb)
  have hB : ∀ b ∈ W, b ∈ B → ∀ a ∈ W, a ∉ B → ¬ G.Adj b a := by
    intro b hb hbB a ha haB hba
    have haA : a ∈ A := by
      have haU : a ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ a
      exact (Finset.mem_union.mp haU).resolve_right haB
    obtain ⟨hau,hbv⟩ := hcut a haA b hbB hba.symm
    rcases havoid with hn | hn
    · exact hn (hau ▸ ha)
    · exact hn (hbv ▸ hb)
  exact ⟨matchable_anticomplete_intersection_even G W A hmatch hA,
    matchable_anticomplete_intersection_even G W B hmatch hB⟩
