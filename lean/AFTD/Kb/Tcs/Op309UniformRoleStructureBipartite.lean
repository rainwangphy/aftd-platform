import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# op309_uniform_role_structure_bipartite

Topic: graphs   Node: 5a0d70abfc24

Provenance: helper lemma. OP-309 analysis of uniform P3 hosts and their nonbipartite obstruction, experiments 42483–42485.

If adjacent vertices have different roles 0, 1, 2 and every role-zero vertex has a uniform neighbor role, then the graph is bipartite.
-/

theorem op309_uniform_role_structure_bipartite
    {V : Type*} (G : SimpleGraph V) (d : V → ℕ)
    (hbound : ∀ v, d v ≤ 2)
    (hdiff : ∀ u v, G.Adj u v → d u ≠ d v)
    (hhom : ∀ u v w, d u = 0 → G.Adj u v → G.Adj u w → d v = d w) :
    G.IsBipartite := by
  classical
  let S : Set V := {v | d v = 2 ∨ (d v = 0 ∧ ∃ w, G.Adj v w ∧ d w = 1)}
  have center_in {v : V} (hv : d v = 2) : v ∈ S := by
    change d v = 2 ∨ (d v = 0 ∧ ∃ w, G.Adj v w ∧ d w = 1)
    exact Or.inl hv
  have leaf_out {v : V} (hv : d v = 1) : v ∉ S := by
    change ¬ (d v = 2 ∨ (d v = 0 ∧ ∃ w, G.Adj v w ∧ d w = 1))
    simp [hv]
  have empty_in {v w : V} (hv : d v = 0) (hvw : G.Adj v w)
      (hw : d w = 1) : v ∈ S := by
    change d v = 2 ∨ (d v = 0 ∧ ∃ w, G.Adj v w ∧ d w = 1)
    exact Or.inr ⟨hv, w, hvw, hw⟩
  have empty_out {v w : V} (hv : d v = 0) (hvw : G.Adj v w)
      (hw : d w = 2) : v ∉ S := by
    change ¬ (d v = 2 ∨ (d v = 0 ∧ ∃ w, G.Adj v w ∧ d w = 1))
    rintro (h | ⟨_, z, hvz, hz⟩)
    · omega
    · have heq := hhom v z w hv hvz hvw
      omega
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := S) (t := Sᶜ)
  constructor
  · exact disjoint_compl_right
  · intro v w hvw
    have hv := hbound v
    have hw := hbound w
    have hne := hdiff v w hvw
    have hc : (d v = 0 ∧ d w = 1) ∨ (d v = 0 ∧ d w = 2) ∨
        (d v = 1 ∧ d w = 0) ∨ (d v = 1 ∧ d w = 2) ∨
        (d v = 2 ∧ d w = 0) ∨ (d v = 2 ∧ d w = 1) := by omega
    rcases hc with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inl ⟨empty_in a hvw b, leaf_out b⟩
    · exact Or.inr ⟨empty_out a hvw b, center_in b⟩
    · exact Or.inr ⟨leaf_out a, empty_in b hvw.symm a⟩
    · exact Or.inr ⟨leaf_out a, center_in b⟩
    · exact Or.inl ⟨center_in a, empty_out b hvw.symm a⟩
    · exact Or.inl ⟨center_in a, leaf_out b⟩
