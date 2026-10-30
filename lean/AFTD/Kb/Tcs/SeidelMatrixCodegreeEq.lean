import AFTD.Prelude
import AFTD.Kb.Tcs.SeidelMatrix
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# seidel_matrix_codegree_eq

Topic: combinatorics   Node: 953efd2f9f17

Provenance: formalization of a published result. Source: arXiv:2610.36522 Lemma 7

For any simple graph G on a finite vertex set V with Seidel matrix S and any pair of adjacent vertices u and v in G, four times the number of common neighbors of u and v equals |V| - 4 - ∑_k S_{uk} - ∑_k S_{vk} + (S^2)_{uv}.
-/

theorem seidel_matrix_codegree_eq_apply {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    seidel_matrix G i j = if i = j then 0 else if G.Adj i j then -1 else 1 := rfl

theorem seidel_matrix_codegree_eq_symm {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
    seidel_matrix G i j = seidel_matrix G j i := by
  simp only [seidel_matrix_codegree_eq_apply, eq_comm (a := i) (b := j), G.adj_comm i j]

/-- Codegree formula for adjacent vertices in terms of the Seidel matrix. -/
theorem seidel_matrix_codegree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (huv : G.Adj u v) :
    4 * (Fintype.card (G.commonNeighbors u v) : ℤ) =
      (Fintype.card V : ℤ) - 4 - (∑ k : V, seidel_matrix G u k) - (∑ k : V, seidel_matrix G v k) +
        (seidel_matrix G * seidel_matrix G) u v := by
  open Finset in
  have h_term (k : V) :
      (1 - seidel_matrix G u k) * (1 - seidel_matrix G v k) =
        (if k ∈ G.commonNeighbors u v then (4 : ℤ) else 0) +
        (if k = u then (2 : ℤ) else 0) +
        (if k = v then (2 : ℤ) else 0) := by
    have hne : u ≠ v := huv.ne
    simp only [seidel_matrix_codegree_eq_apply, SimpleGraph.commonNeighbors, Set.mem_inter_iff,
      SimpleGraph.mem_neighborSet]
    by_cases hku : k = u
    · subst hku
      have h1 : v ≠ k := hne.symm
      have h2 : G.Adj v k := huv.symm
      simp [h1, h2, eq_comm]
    · by_cases hkv : k = v
      · subst hkv
        have h1 : u ≠ k := hne
        have h2 : G.Adj u k := huv
        simp [h1, h2, eq_comm]
      · have h1 : u ≠ k := fun h => hku h.symm
        have h2 : v ≠ k := fun h => hkv h.symm
        simp [hku, hkv, h1, h2]
        by_cases ha1 : G.Adj u k <;> by_cases ha2 : G.Adj v k <;> simp [ha1, ha2]
  have h_sum_rhs :
      (∑ k : V, ((if k ∈ G.commonNeighbors u v then (4 : ℤ) else 0) +
        (if k = u then (2 : ℤ) else 0) + (if k = v then (2 : ℤ) else 0))) =
      4 * (Fintype.card (G.commonNeighbors u v) : ℤ) + 4 := by
    simp only [Finset.sum_add_distrib]
    have hu : (∑ k : V, (if k = u then (2 : ℤ) else 0)) = 2 := by simp
    have hv : (∑ k : V, (if k = v then (2 : ℤ) else 0)) = 2 := by simp
    have hc : (∑ k : V, (if k ∈ G.commonNeighbors u v then (4 : ℤ) else 0)) =
        4 * (Fintype.card (G.commonNeighbors u v) : ℤ) := by
      have h : (∑ k : V, (if k ∈ G.commonNeighbors u v then (4 : ℤ) else 0)) =
          4 * ∑ k : V, (if k ∈ G.commonNeighbors u v then (1 : ℤ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> ring
      rw [h]
      congr 1
      rw [← Set.toFinset_card]
      rw [Finset.sum_boole (· ∈ G.commonNeighbors u v) Finset.univ]
      apply congrArg
      apply congrArg
      ext x
      simp
    linarith
  have h_sum_lhs :
      (∑ k : V, (1 - seidel_matrix G u k) * (1 - seidel_matrix G v k)) =
      (Fintype.card V : ℤ) - (∑ k : V, seidel_matrix G u k) - (∑ k : V, seidel_matrix G v k) +
        (seidel_matrix G * seidel_matrix G) u v := by
    have h_alg (k : V) :
        (1 - seidel_matrix G u k) * (1 - seidel_matrix G v k) =
        1 - seidel_matrix G u k - seidel_matrix G v k +
          seidel_matrix G u k * seidel_matrix G v k := by ring
    simp_rw [h_alg]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ]
    have h_mul : (∑ k : V, seidel_matrix G u k * seidel_matrix G v k) =
        (seidel_matrix G * seidel_matrix G) u v := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [seidel_matrix_codegree_eq_symm G v k]
    rw [h_mul]
  have h_sum_eq :
      (∑ k : V, (1 - seidel_matrix G u k) * (1 - seidel_matrix G v k)) =
      ∑ k : V, ((if k ∈ G.commonNeighbors u v then (4 : ℤ) else 0) +
        (if k = u then (2 : ℤ) else 0) + (if k = v then (2 : ℤ) else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    exact h_term k
  linarith
