import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicParityReprOrtho
import AFTD.Kb.Tcs.CyclicCubicSyndrome
import AFTD.Kb.Tcs.IsParityRepr

/-!
# cyclic_cubic_parity_repr_pair_sum

Topic: quantum   Node: 383208bfd099

Provenance: helper lemma. step towards cyclic_cubic_parity_repr_eval_zero

For n ≥ 6 and any distinct pair p ≠ q, the sum ∑_j c_j * s({j, p, q}) vanishes for any affine evaluation on a parity representation.
-/

/-- For n ≥ 6 and any distinct pair p ≠ q, summing c_j * cyclic_cubic_syndrome n {j, p, q} over j gives 0. -/
theorem cyclic_cubic_parity_repr_pair_sum (n : ℕ) (hn : 6 ≤ n) (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (cyclic_cubic_syndrome n)) (c : Fin n → ZMod 2) (b : ZMod 2) (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b) (p q : Fin n) (hpq : p ≠ q) : ∑ j : Fin n, c j * cyclic_cubic_syndrome n {j, p, q} = 0 := by
  have h_zero : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j ∈ y, c j) = 0 := by
    have h1 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j ∈ y, c j) =
        ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), b := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [Finset.mem_filter] at hy
      exact h y hy.1
    rw [h1, Finset.sum_const, nsmul_eq_mul]
    have hpq_card : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair hpq
    have hcard1 : 1 ≤ ({p, q} : Finset (Fin n)).card := by omega
    have hcard2 : ({p, q} : Finset (Fin n)).card ≤ 2 := by omega
    have hz := cyclic_cubic_parity_repr_ortho_card_le_two n hn S hS {p, q} hcard1 hcard2
    rw [hz, zero_mul]
  have h_swap : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j ∈ y, c j) =
      ∑ j : Fin n, c j * cyclic_cubic_syndrome n {j, p, q} := by
    have h1 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j ∈ y, c j) =
        ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j : Fin n, if j ∈ y then c j else 0 := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      exact (Finset.sum_ite_mem_eq y c).symm
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h2 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), if j ∈ y then c j else 0) =
        c j * ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), if j ∈ y then (1 : ZMod 2) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs <;> ring
    rw [h2]
    congr 1
    rw [Finset.sum_boole]
    have h_filt : {y ∈ S.filter (fun y => {p, q} ⊆ y) | j ∈ y} =
        S.filter (fun y => {j, p, q} ⊆ y) := by
      ext y
      simp only [Finset.mem_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      tauto
    rw [h_filt]
    have hcard1 : 1 ≤ ({j, p, q} : Finset (Fin n)).card := by
      have : ({j, p, q} : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_insert_self j _⟩
      exact Finset.Nonempty.card_pos this
    have hcard2 : ({j, p, q} : Finset (Fin n)).card ≤ 3 := by
      have h1 := Finset.card_insert_le j {p, q}
      have h2 := Finset.card_insert_le p {q}
      rw [Finset.card_singleton] at h2
      omega
    have h_repr := hS.2 {j, p, q} ⟨hcard1, hcard2⟩
    exact h_repr
  rw [← h_swap, h_zero]
