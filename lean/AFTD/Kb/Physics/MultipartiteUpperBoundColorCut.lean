import AFTD.Prelude
import AFTD.Kb.Physics.MultipartiteUpperBoundSplitParts

/-!
# multipartite_upper_bound_color_cut

Topic: quantum_mechanics   Node: 8be047f6efa0

Provenance: helper lemma. step towards multipartite_graph_state_tripartite_info_upper_bound

The exact value of the cut rank of the complete multipartite graph at the colour class indexed by X, expressed purely in terms of the part colour sets T: the number of split parts, plus one if some part is contained in X and some part is disjoint from X, and minus the parity of the number of split parts in the remaining case (when every part splits).
-/

/-- The exact GF(2) cut rank of the cut at a colour class, as a function of the part colour sets. -/
noncomputable def multipartite_upper_bound_color_cut {ι : Type*} [Fintype ι]
    (T : ι → Finset (Fin 4)) (X : Finset (Fin 4)) : ℤ := by
  classical
  exact ((multipartite_upper_bound_split_parts T X).card : ℤ) +
    (if (∃ i, T i ⊆ X) ∧ (∃ i, T i ∩ X = ∅) then 1
     else if (∃ i, T i ⊆ X) ∨ (∃ i, T i ∩ X = ∅) then 0
     else -(((multipartite_upper_bound_split_parts T X).card % 2 : ℕ) : ℤ))
