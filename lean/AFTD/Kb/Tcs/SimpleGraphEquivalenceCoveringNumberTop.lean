import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber

/-!
# simple_graph_equivalence_covering_number_top

Topic: combinatorics   Node: 20e89e8d0c82

Provenance: helper lemma. Sanity lemma for eq(G), arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs) (Theorem 1.2 uses eq(K_n) = 1).

Sanity check: a complete graph with at least two vertices has equivalence covering number 1.
-/

theorem simple_graph_equivalence_covering_number_top {V : Type*} [Nontrivial V] :
    simple_graph_equivalence_covering_number (⊤ : SimpleGraph V) = 1 := by
  have h1 : simple_graph_has_equivalence_cover (⊤ : SimpleGraph V) 1 := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact ⟨fun _ _ => x, fun _ _ _ huv _ => huv, fun _ _ _ => ⟨0, rfl⟩⟩
  apply le_antisymm
  · exact Nat.sInf_le h1
  · refine le_csInf ⟨1, h1⟩ fun t ht => ?_
    obtain ⟨c, -, hcov⟩ := ht
    obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    obtain ⟨s, -⟩ := hcov x y hxy
    exact Nat.one_le_iff_ne_zero.mpr fun h => by subst h; exact s.elim0
