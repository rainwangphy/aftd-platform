import AFTD.Prelude
import AFTD.Kb.Tcs.MatchableAnticompleteIntersectionEven

/-!
# matchable_subset_even_on_forced_bridge_sides

Topic: graphs   Node: 5ff0b961e482

Provenance: helper lemma. OP-1957 uniform bridge-shore assembly.

A matchable subset of two bridge shores that avoids one bridge endpoint meets each shore in even cardinality.
-/

theorem matchable_subset_even_on_forced_bridge_sides {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B W : Finset V) (u v : V)
    (hdisj : Disjoint A B) (hcover : W ⊆ A ∪ B)
    (hu : u ∈ A) (hv : v ∈ B)
    (hcut : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∧ b = v)
    (havoid : u ∉ W ∨ v ∉ W)
    (hmatch : ∃ P : (G.induce {a | a ∈ W}).Subgraph, P.IsPerfectMatching) :
    Even (W ∩ A).card ∧ Even (W ∩ B).card := by
  classical
  have hA : ∀ a ∈ W, a ∈ A → ∀ b ∈ W, b ∉ A → ¬ G.Adj a b := by
    intro a ha haA b hb hbA hab
    have hbB : b ∈ B := by
      have hbU : b ∈ A ∪ B := hcover hb
      exact (Finset.mem_union.mp hbU).resolve_left hbA
    obtain ⟨hau,hbv⟩ := hcut a haA b hbB hab
    rcases havoid with hn | hn
    · exact hn (hau ▸ ha)
    · exact hn (hbv ▸ hb)
  have hB : ∀ b ∈ W, b ∈ B → ∀ a ∈ W, a ∉ B → ¬ G.Adj b a := by
    intro b hb hbB a ha haB hba
    have haA : a ∈ A := by
      have haU : a ∈ A ∪ B := hcover ha
      exact (Finset.mem_union.mp haU).resolve_right haB
    obtain ⟨hau,hbv⟩ := hcut a haA b hbB hba.symm
    rcases havoid with hn | hn
    · exact hn (hau ▸ ha)
    · exact hn (hbv ▸ hb)
  exact ⟨matchable_anticomplete_intersection_even G W A hmatch hA,
    matchable_anticomplete_intersection_even G W B hmatch hB⟩
