import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.LineSyndrome

/-!
# line_cubic_parity_repr_ortho

Topic: quantum   Node: c2b9050166bf

Provenance: helper lemma. step towards line_cubic_t_count_lower_bound

Every parity representation S of line_syndrome n satisfies ∑_{y ∈ S} (∑_{j ∈ y} c_j)(∑_{k ∈ y} d_k) = 0 and ∑_{y ∈ S} ∑_{j ∈ y} c_j = 0, because singletons and pairs have syndrome 0.
-/

lemma line_cubic_parity_repr_ortho_card_le_two (n : ℕ)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (A : Finset (Fin n)) (hA1 : 1 ≤ A.card) (hA2 : A.card ≤ 2) :
    ((S.filter (fun y => A ⊆ y)).card : ZMod 2) = 0 := by
  have hA3 : A.card ≤ 3 := by omega
  have hrepr := hS.2 A ⟨hA1, hA3⟩
  rw [hrepr]
  unfold line_syndrome
  split_ifs with h
  · rcases h with ⟨i, hi⟩
    have hc : ({⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩, ⟨i.val + 2, by omega⟩} : Finset (Fin n)).card = 3 := by
      let a : Fin n := ⟨i.val, by omega⟩
      let b : Fin n := ⟨i.val + 1, by omega⟩
      let c : Fin n := ⟨i.val + 2, by omega⟩
      change ({a, b, c} : Finset (Fin n)).card = 3
      have hab : a ≠ b := by intro h; injection h with h; omega
      have hac : a ≠ c := by intro h; injection h with h; omega
      have hbc : b ≠ c := by intro h; injection h with h; omega
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton] at h; exact hbc h
      · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (h | h)
        · exact hab h
        · exact hac h
    have h_card_eq := congr_arg Finset.card hi
    omega
  · rfl

/-- Every parity representation of the line cubic syndrome satisfies bilinear self-orthogonality and linear orthogonality to the all-ones vector. -/
theorem line_cubic_parity_repr_ortho (n : ℕ)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c d : Fin n → ZMod 2) :
    (∑ y ∈ S, (∑ j ∈ y, c j) * (∑ k ∈ y, d k) = 0) ∧
    (∑ y ∈ S, (∑ j ∈ y, c j) = 0) := by
  constructor
  · have h1 : (∑ y ∈ S, (∑ j ∈ y, c j) * (∑ k ∈ y, d k)) =
        ∑ y ∈ S, ∑ j : Fin n, ∑ k : Fin n, (if j ∈ y then c j else 0) * (if k ∈ y then d k else 0) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_ite_mem_eq y c, ← Finset.sum_ite_mem_eq y d]
      rw [Finset.sum_mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have h_split : (∑ y ∈ S, (if j ∈ y then c j else 0) * (if k ∈ y then d k else 0)) =
        (c j * d k) * ∑ y ∈ S, (if j ∈ y ∧ k ∈ y then (1 : ZMod 2) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hj : j ∈ y <;> by_cases hk : k ∈ y <;> simp [hj, hk]
    rw [h_split, Finset.sum_boole]
    have h_filt : {x ∈ S | j ∈ x ∧ k ∈ x} = S.filter (fun y => {j, k} ⊆ y) := by
      ext y
      simp only [Finset.mem_filter, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    rw [h_filt]
    have hne : ({j, k} : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_insert_self j _⟩
    have hcard1 : 1 ≤ ({j, k} : Finset (Fin n)).card := Finset.Nonempty.card_pos hne
    have hcard2 : ({j, k} : Finset (Fin n)).card ≤ 2 := by
      have := Finset.card_insert_le j {k}
      rw [Finset.card_singleton] at this
      omega
    have h_zero := line_cubic_parity_repr_ortho_card_le_two n S hS {j, k} hcard1 hcard2
    rw [h_zero, mul_zero]
  · have h1 : (∑ y ∈ S, ∑ j ∈ y, c j) = ∑ y ∈ S, ∑ j : Fin n, if j ∈ y then c j else 0 := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      exact (Finset.sum_ite_mem_eq y c).symm
    rw [h1, Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have h_split : (∑ y ∈ S, if j ∈ y then c j else 0) =
        c j * ∑ y ∈ S, (if j ∈ y then (1 : ZMod 2) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      split_ifs <;> ring
    rw [h_split, Finset.sum_boole]
    have h_filt : {x ∈ S | j ∈ x} = S.filter (fun y => {j} ⊆ y) := by
      ext y
      simp only [Finset.mem_filter, Finset.singleton_subset_iff]
    rw [h_filt]
    have hcard1 : 1 ≤ ({j} : Finset (Fin n)).card := by rw [Finset.card_singleton]
    have hcard2 : ({j} : Finset (Fin n)).card ≤ 2 := by rw [Finset.card_singleton]; omega
    have h_zero := line_cubic_parity_repr_ortho_card_le_two n S hS {j} hcard1 hcard2
    rw [h_zero, mul_zero]
