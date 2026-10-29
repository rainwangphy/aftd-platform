import AFTD.Prelude
import AFTD.Kb.Tcs.MultisetSumApply
import AFTD.Kb.Tcs.RigidSequenceTensorProductMemCoord
import AFTD.Kb.Tcs.RigidSequenceTensorProduct

/-!
# rigid_sequence_projection_is_zero_sum

Topic: combinatorics   Node: 14c8ccf49100

Provenance: helper lemma. arXiv:2610.35819 Proof of Theorem 4.3

Let n, m, and t be natural numbers, and for each i in Fin t let S(i) be a sequence in Multiset (G(i)) where each G(i) is an additive commutative group. If W is an n-term zero-sum subsequence of the rigid sequence tensor product of S with parameters n and m, then for each coordinate j in Fin t, the projection of W to coordinate j has cardinality n, sum 0, and support contained in S(j).
-/

/-- Coordinate projections of an n-term zero-sum subsequence of the tensor product are n-term zero-sums on the factors. -/
lemma rigid_sequence_projection_is_zero_sum {n m t : ℕ} {G : Fin t → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, DecidableEq (G i)]
    (S : (i : Fin t) → Multiset (G i))
    (W : Multiset ((i : Fin t) → G i))
    (hW_le : W ≤ rigid_sequence_tensor_product n m S)
    (hW_card : W.card = n) (hW_sum : W.sum = 0) (j : Fin t) :
    (W.map (fun x => x j)).card = n ∧
    (W.map (fun x => x j)).sum = 0 ∧
    (∀ y ∈ W.map (fun x => x j), y ∈ S j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Multiset.card_map, hW_card]
  · rw [multiset_sum_apply, hW_sum, Pi.zero_apply]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    have hx_le : x ∈ rigid_sequence_tensor_product n m S := Multiset.mem_of_le hW_le hx
    exact rigid_sequence_tensor_product_mem_coord S x hx_le j
