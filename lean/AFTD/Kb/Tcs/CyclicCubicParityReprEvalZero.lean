import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CyclicCubicSyndrome
import AFTD.Kb.Tcs.CyclicCubicDistinctNeighbors
import AFTD.Kb.Tcs.CyclicCubicParityReprPairSum
import AFTD.Kb.Tcs.CyclicCubicSyndromeIsolated

/-!
# cyclic_cubic_parity_repr_eval_zero

Topic: quantum   Node: cd3e4bb3da02

Provenance: helper lemma. step towards cyclic_cubic_t_count_isotropy_lower_bound

For n ≥ 6, any affine evaluation (∑_{j ∈ y} c_j = b) on all parities y ∈ S of a parity representation S of cyclic_cubic_syndrome n forces c = 0.
-/

private theorem cyclic_cubic_parity_repr_eval_zero_syndrome_one (n : ℕ) (hn : 6 ≤ n) (x : Fin n) :
    cyclic_cubic_syndrome n {x, (⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n), (⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)} = 1 := by
  unfold cyclic_cubic_syndrome
  rw [if_pos]
  refine ⟨⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩, ?_⟩
  have hA : ((⟨(((⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)).val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)) = x := by
    apply Fin.ext
    simp only
    have h1 : ((x.val + n - 1) % n + 1) % n = (x.val + n - 1 + 1) % n := Nat.mod_add_mod _ _ _
    rw [h1]
    have h2 : x.val + n - 1 + 1 = x.val + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  have hB : ((⟨(((⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)).val + 2) % n, Nat.mod_lt _ (by omega)⟩ : Fin n)) = (⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) := by
    apply Fin.ext
    simp only
    have h1 : ((x.val + n - 1) % n + 2) % n = (x.val + n - 1 + 2) % n := Nat.mod_add_mod _ _ _
    rw [h1]
    have h2 : x.val + n - 1 + 2 = (x.val + 1) + n := by omega
    rw [h2, Nat.add_mod_right]
  simp only [hA, hB]
  exact Finset.insert_comm _ _ _

/-- For n ≥ 6, any affine evaluation (∑_{j ∈ y} c_j = b) on all parities y ∈ S of a parity representation S of cyclic_cubic_syndrome n forces c = 0. -/
theorem cyclic_cubic_parity_repr_eval_zero (n : ℕ) (hn : 6 ≤ n) (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (cyclic_cubic_syndrome n)) (c : Fin n → ZMod 2) (b : ZMod 2) (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b) : c = 0 := by
  funext x
  set p : Fin n := ⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩ with hp
  set q : Fin n := ⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩ with hq
  have hpq : p ≠ q := by simpa only [hp, hq] using cyclic_cubic_distinct_neighbors n hn x
  have hsingle : ∑ j : Fin n, c j * cyclic_cubic_syndrome n {j, p, q} = c x * cyclic_cubic_syndrome n {x, p, q} := by
    apply Fintype.sum_eq_single x
    intro j hjx
    rw [show cyclic_cubic_syndrome n {j, p, q} = 0 from by
      simpa only [hp, hq] using cyclic_cubic_syndrome_isolated n hn x j hjx]
    rw [mul_zero]
  have hsum := cyclic_cubic_parity_repr_pair_sum n hn S hS c b h p q hpq
  rw [hsingle] at hsum
  have hsy : cyclic_cubic_syndrome n {x, p, q} = 1 := by
    simpa only [hp, hq] using cyclic_cubic_parity_repr_eval_zero_syndrome_one n hn x
  rw [hsy, mul_one] at hsum
  exact hsum
