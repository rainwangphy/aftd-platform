import AFTD.Prelude
import AFTD.Kb.Tcs.RigidSequenceTensorProduct

/-!
# rigid_sequence_tensor_product_mem_coord

Topic: combinatorics   Node: 23d744fdafc1

Provenance: helper lemma. arXiv:2610.35819 Definition 4.2

Let n and m be natural numbers, t a natural number, and for each i in Fin t let S(i) be a sequence in Multiset (G(i)). If x is an element of the rigid sequence tensor product of S with parameters n and m, then for every coordinate j in Fin t, x(j) belongs to the sequence S(j).
-/

/-- Every coordinate of a tuple in the tensor product belongs to the corresponding factor sequence. -/
lemma rigid_sequence_tensor_product_mem_coord {n m t : ℕ} {G : Fin t → Type*}
    [∀ i, DecidableEq (G i)] (S : (i : Fin t) → Multiset (G i))
    (x : (i : Fin t) → G i) (hx : x ∈ rigid_sequence_tensor_product n m S)
    (j : Fin t) : x j ∈ S j := by
  unfold rigid_sequence_tensor_product at hx
  rcases Multiset.mem_sum.mp hx with ⟨s, hs, hx_in⟩
  have hx_eq : x = s := Multiset.eq_of_mem_replicate hx_in
  subst hx_eq
  rw [Fintype.mem_piFinset] at hs
  exact Multiset.mem_toFinset.mp (hs j)
