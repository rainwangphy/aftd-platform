import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CyclicCubicSyndrome

/-!
# cyclic_cubic_parity_repr_ortho

Topic: quantum   Node: 4ddbb3051cb8

Provenance: helper lemma. step towards cyclic_cubic_t_count_isotropy_lower_bound

Every parity representation S of cyclic_cubic_syndrome n satisfies ∑_{y ∈ S} (∑_{j ∈ y} c_j)(∑_{k ∈ y} d_k) = 0 and ∑_{y ∈ S} ∑_{j ∈ y} c_j = 0, because singletons and pairs have cyclic cubic syndrome 0.
-/

lemma cyclic_cubic_parity_repr_ortho_syndrome_card_le_two (n : ℕ) (hn : 6 ≤ n) (A : Finset (Fin n)) (hA : A.card ≤ 2) :
    cyclic_cubic_syndrome n A = 0 := by
  have h_triple_card : ∀ j : Fin n,
    ({j, ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩, ⟨(j.val + 2) % n, Nat.mod_lt _ (by omega)⟩} : Finset (Fin n)).card = 3 := by
    intro j
    let j0 : Fin n := j
    let j1 : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    let j2 : Fin n := ⟨(j.val + 2) % n, Nat.mod_lt _ (by omega)⟩
    have hj := j.isLt
    have h_n_add_one : (n + 1) % n = 1 := by
      rw [add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h01 : j0 ≠ j1 := by
      intro h
      have hval := congr_arg Fin.val h
      dsimp [j0, j1] at hval
      by_cases hj1 : j.val + 1 < n
      · rw [Nat.mod_eq_of_lt hj1] at hval; omega
      · have hj2 : j.val + 1 = n := by omega
        rw [hj2, Nat.mod_self] at hval; omega
    have h02 : j0 ≠ j2 := by
      intro h
      have hval := congr_arg Fin.val h
      dsimp [j0, j2] at hval
      by_cases hj1 : j.val + 2 < n
      · rw [Nat.mod_eq_of_lt hj1] at hval; omega
      · have hj2 : j.val + 2 = n ∨ j.val + 2 = n + 1 := by omega
        rcases hj2 with h2 | h2
        · rw [h2, Nat.mod_self] at hval; omega
        · rw [h2, h_n_add_one] at hval; omega
    have h12 : j1 ≠ j2 := by
      intro h
      have hval := congr_arg Fin.val h
      dsimp [j1, j2] at hval
      by_cases hj2 : j.val + 2 < n
      · have hj1 : j.val + 1 < n := by omega
        rw [Nat.mod_eq_of_lt hj1, Nat.mod_eq_of_lt hj2] at hval; omega
      · have hjcase : j.val + 2 = n ∨ j.val + 2 = n + 1 := by omega
        rcases hjcase with h2 | h2
        · have hj1 : j.val + 1 < n := by omega
          rw [Nat.mod_eq_of_lt hj1, h2, Nat.mod_self] at hval; omega
        · have hj1 : j.val + 1 = n := by omega
          rw [hj1, Nat.mod_self, h2, h_n_add_one] at hval; omega
    change ({j0, j1, j2} : Finset (Fin n)).card = 3
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h; simp only [Finset.mem_singleton] at h; exact h12 h
    · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (h | h)
      · exact h01 h
      · exact h02 h
  unfold cyclic_cubic_syndrome
  split_ifs with h
  · rcases h with ⟨j, rfl⟩
    have hc := h_triple_card j
    omega
  · rfl

lemma cyclic_cubic_parity_repr_ortho_card_le_two (n : ℕ) (hn : 6 ≤ n)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (cyclic_cubic_syndrome n))
    (A : Finset (Fin n)) (hA1 : 1 ≤ A.card) (hA2 : A.card ≤ 2) :
    ((S.filter (fun y => A ⊆ y)).card : ZMod 2) = 0 := by
  have hr := hS.2 A ⟨hA1, by omega⟩
  rw [hr, cyclic_cubic_parity_repr_ortho_syndrome_card_le_two n hn A hA2]

/-- Every parity representation S of cyclic_cubic_syndrome n satisfies ∑_{y ∈ S} (∑_{j ∈ y} c_j)(∑_{k ∈ y} d_k) = 0 and ∑_{y ∈ S} ∑_{j ∈ y} c_j = 0, because singletons and pairs have cyclic cubic syndrome 0. -/
theorem cyclic_cubic_parity_repr_ortho (n : ℕ) (hn : 6 ≤ n) (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (cyclic_cubic_syndrome n)) (c d : Fin n → ZMod 2) : (∑ y ∈ S, (∑ j ∈ y, c j) * (∑ k ∈ y, d k) = 0) ∧ (∑ y ∈ S, (∑ j ∈ y, c j) = 0) := by
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
    have h_zero := cyclic_cubic_parity_repr_ortho_card_le_two n hn S hS {j, k} hcard1 hcard2
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
    have h_zero := cyclic_cubic_parity_repr_ortho_card_le_two n hn S hS {j} hcard1 hcard2
    rw [h_zero, mul_zero]
