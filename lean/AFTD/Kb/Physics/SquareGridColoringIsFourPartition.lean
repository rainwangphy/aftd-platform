import AFTD.Prelude
import AFTD.Kb.Physics.IsFourPartition

/-!
# square_grid_coloring_is_four_partition

Topic: quantum_mechanics   Node: 53e9b35387bc

Provenance: helper lemma. arXiv:2511.19585 ("Monogamy of Mutual Information in Graph States")

For any natural number n and any four-coloring c : Fin n × Fin n → Fin 4, the four color classes of c are pairwise disjoint and their union is the universal finset, so they satisfy is_four_partition.
-/

/-- The four color classes of any four-coloring on Fin n × Fin n form a valid four-partition. -/
theorem square_grid_coloring_is_four_partition (n : ℕ) (c : Fin n × Fin n → Fin 4) :
    is_four_partition
      (Finset.univ.filter (fun v => c v = 0))
      (Finset.univ.filter (fun v => c v = 1))
      (Finset.univ.filter (fun v => c v = 2))
      (Finset.univ.filter (fun v => c v = 3)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 6
    rw [Finset.disjoint_filter]
    intro x _ hx hy
    omega
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have : c x = 0 ∨ c x = 1 ∨ c x = 2 ∨ c x = 3 := by omega
  tauto
