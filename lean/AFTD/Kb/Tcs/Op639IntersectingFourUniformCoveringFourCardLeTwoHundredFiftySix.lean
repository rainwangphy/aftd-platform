import AFTD.Prelude
import AFTD.Kb.Tcs.IntersectingUniformHypergraphCardLePow

/-!
# op_639_intersecting_four_uniform_covering_four_card_le_two_hundred_fifty_six

Topic: combinatorics   Node: 6a6bd9a70672

Provenance: helper lemma. arXiv:2610.37315, Theorem 1.1 (Erdos-Lovasz)

Let V be a finite type with decidable equality, and let F be a family of 4-element subsets of V. If F is pairwise intersecting, has no transversal of size strictly less than 4 (every subset of size less than 4 is disjoint from some edge of F), and admits a transversal of size 4, then F has cardinality at most 256.
-/

/-- Erdos-Lovasz bound specialized to k = 4: every intersecting 4-uniform hypergraph on a finite vertex set with covering number 4 has at most 256 edges. -/
theorem op_639_intersecting_four_uniform_covering_four_card_le_two_hundred_fifty_six
    {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (Finset V))
    (hunif : ∀ e ∈ F, e.card = 4)
    (hinter : (F : Set (Finset V)).Intersecting)
    (htau_ge : ∀ T : Finset V, T.card < 4 → ∃ e ∈ F, Disjoint e T)
    (htau_ex : ∃ T : Finset V, T.card = 4 ∧ ∀ e ∈ F, ¬Disjoint e T) :
    F.card ≤ 256 := by
  have _ := htau_ex
  have h_le := intersecting_uniform_hypergraph_card_le_pow 4 (by norm_num) F hunif
    (fun F1 h1 F2 h2 => by
      rw [← Finset.not_disjoint_iff_nonempty_inter]
      exact hinter (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2))
    (fun A hA => by
      rcases htau_ge A hA with ⟨e, he, hdisj⟩
      exact ⟨e, he, hdisj.symm⟩)
  exact h_le
