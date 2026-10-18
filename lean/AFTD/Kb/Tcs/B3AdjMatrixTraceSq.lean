import AFTD.Prelude
import AFTD.Kb.Tcs.B3Graph
import AFTD.Kb.Tcs.B3QuotientMatrix
import AFTD.Kb.Tcs.B3QuotientTraceSq
import AFTD.Kb.Tcs.B3GraphAdj

/-!
# b3_adjMatrix_trace_sq

Topic: graphs   Node: f6a3f3ba4e70

Provenance: helper lemma. arXiv:2610.21388 (Stronger spectral bound for clique number), Theorems 2.3 and 2.6 (the eigenvalue -1 of multiplicity n - 3 from the cliques); links the trace form of Theorem 3.1 to the adjacency spectrum

For B_3(n_0,n_1,n_2) with adjacency matrix A: tr(A^2) = tr(M^2) + (n - 3). Since tr(A^2) is the sum of the squares of all adjacency eigenvalues and -1 has multiplicity n - 3, this identifies tr(M^2) with the sum of the squares of the eigenvalues other than -1.
-/

open Classical in
theorem b3_adjMatrix_trace_sq (n : Fin 3 → ℕ) :
    (((b3_graph n).adjMatrix ℝ) ^ 2).trace
      = (b3_quotient_matrix n ^ 2).trace + ((∑ i, (n i : ℝ)) - 3) := by
  classical
  have htrace : (((b3_graph n).adjMatrix ℝ) ^ 2).trace
      = ∑ x : Sigma (fun i : Fin 3 => Fin (n i)), ((b3_graph n).degree x : ℝ) := by
    rw [pow_two, Matrix.trace]
    exact Finset.sum_congr rfl (fun x _ => SimpleGraph.adjMatrix_mul_self_apply_self (b3_graph n) x)
  have deg0 : ∀ v : Fin (n 0), (b3_graph n).degree ⟨(0 : Fin 3), v⟩ = n 0 - 1 + n 2 := by
    intro v
    have heq :
        (b3_graph n).neighborFinset ⟨(0 : Fin 3), v⟩
          = ((Finset.univ : Finset (Fin (n 0))).erase v).image (fun w => (⟨(0:Fin 3), w⟩ : Sigma (fun i => Fin (n i))))
            ∪ (Finset.univ : Finset (Fin (n 2))).image (fun w => (⟨(2:Fin 3), w⟩ : Sigma (fun i => Fin (n i)))) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset, b3_graph_adj]
      obtain ⟨i, w⟩ := x
      fin_cases i
      · simp [Sigma.mk.injEq, eq_comm]
      · simp [Sigma.mk.injEq]
      · simp [Sigma.mk.injEq]
    have hdisj : Disjoint (((Finset.univ : Finset (Fin (n 0))).erase v).image (fun w => (⟨(0:Fin 3), w⟩ : Sigma (fun i => Fin (n i)))))
        ((Finset.univ : Finset (Fin (n 2))).image (fun w => (⟨(2:Fin 3), w⟩ : Sigma (fun i => Fin (n i))))) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, hb⟩ := hy
      simp [Sigma.mk.injEq] at hb
    rw [SimpleGraph.degree, heq, Finset.card_union_of_disjoint hdisj]
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fin]
  have deg1 : ∀ v : Fin (n 1), (b3_graph n).degree ⟨(1 : Fin 3), v⟩ = n 1 - 1 + n 2 := by
    intro v
    have heq :
        (b3_graph n).neighborFinset ⟨(1 : Fin 3), v⟩
          = ((Finset.univ : Finset (Fin (n 1))).erase v).image (fun w => (⟨(1:Fin 3), w⟩ : Sigma (fun i => Fin (n i))))
            ∪ (Finset.univ : Finset (Fin (n 2))).image (fun w => (⟨(2:Fin 3), w⟩ : Sigma (fun i => Fin (n i)))) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset, b3_graph_adj]
      obtain ⟨i, w⟩ := x
      fin_cases i
      · simp [Sigma.mk.injEq, eq_comm]
      · simp [Sigma.mk.injEq, eq_comm]
      · simp [Sigma.mk.injEq, eq_comm]
    have hdisj : Disjoint (((Finset.univ : Finset (Fin (n 1))).erase v).image (fun w => (⟨(1:Fin 3), w⟩ : Sigma (fun i => Fin (n i)))))
        ((Finset.univ : Finset (Fin (n 2))).image (fun w => (⟨(2:Fin 3), w⟩ : Sigma (fun i => Fin (n i))))) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, hb⟩ := hy
      simp [Sigma.mk.injEq] at hb
    rw [SimpleGraph.degree, heq, Finset.card_union_of_disjoint hdisj]
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h),
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Finset.card_univ,
        Fintype.card_fin, Fintype.card_fin]
  have deg2 : ∀ v : Fin (n 2), (b3_graph n).degree ⟨(2 : Fin 3), v⟩ = n 0 + n 1 + n 2 - 1 := by
    intro v
    have heq :
        (b3_graph n).neighborFinset ⟨(2 : Fin 3), v⟩
          = (Finset.univ : Finset (Sigma (fun i : Fin 3 => Fin (n i)))).erase ⟨(2:Fin 3), v⟩ := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, SimpleGraph.mem_neighborFinset, b3_graph_adj]
      tauto
    rw [SimpleGraph.degree, heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_sigma]
    simp [Fin.sum_univ_three]
  have h0 : (∑ v : Fin (n 0), ((b3_graph n).degree ⟨(0:Fin 3), v⟩ : ℝ))
      = (n 0 : ℝ) * ((n 0 : ℝ) - 1 + (n 2 : ℝ)) := by
    have key : ∀ v : Fin (n 0), ((b3_graph n).degree ⟨(0:Fin 3), v⟩ : ℝ) = ((n 0 : ℝ) - 1 + (n 2 : ℝ)) := by
      intro v
      rw [deg0 v]
      have hv : 1 ≤ n 0 := by have := v.isLt; omega
      rw [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one]
    calc (∑ v : Fin (n 0), ((b3_graph n).degree ⟨(0:Fin 3), v⟩ : ℝ))
        = ∑ v : Fin (n 0), ((n 0 : ℝ) - 1 + (n 2 : ℝ)) := Finset.sum_congr rfl (fun v _ => key v)
      _ = (n 0 : ℝ) * ((n 0 : ℝ) - 1 + (n 2 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : (∑ v : Fin (n 1), ((b3_graph n).degree ⟨(1:Fin 3), v⟩ : ℝ))
      = (n 1 : ℝ) * ((n 1 : ℝ) - 1 + (n 2 : ℝ)) := by
    have key : ∀ v : Fin (n 1), ((b3_graph n).degree ⟨(1:Fin 3), v⟩ : ℝ) = ((n 1 : ℝ) - 1 + (n 2 : ℝ)) := by
      intro v
      rw [deg1 v]
      have hv : 1 ≤ n 1 := by have := v.isLt; omega
      rw [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one]
    calc (∑ v : Fin (n 1), ((b3_graph n).degree ⟨(1:Fin 3), v⟩ : ℝ))
        = ∑ v : Fin (n 1), ((n 1 : ℝ) - 1 + (n 2 : ℝ)) := Finset.sum_congr rfl (fun v _ => key v)
      _ = (n 1 : ℝ) * ((n 1 : ℝ) - 1 + (n 2 : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (∑ v : Fin (n 2), ((b3_graph n).degree ⟨(2:Fin 3), v⟩ : ℝ))
      = (n 2 : ℝ) * ((n 0 : ℝ) + (n 1 : ℝ) + (n 2 : ℝ) - 1) := by
    have key : ∀ v : Fin (n 2), ((b3_graph n).degree ⟨(2:Fin 3), v⟩ : ℝ) = ((n 0 : ℝ) + (n 1 : ℝ) + (n 2 : ℝ) - 1) := by
      intro v
      rw [deg2 v]
      have hv : 1 ≤ n 0 + n 1 + n 2 := by have := v.isLt; omega
      rw [Nat.cast_sub hv, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    calc (∑ v : Fin (n 2), ((b3_graph n).degree ⟨(2:Fin 3), v⟩ : ℝ))
        = ∑ v : Fin (n 2), ((n 0 : ℝ) + (n 1 : ℝ) + (n 2 : ℝ) - 1) := Finset.sum_congr rfl (fun v _ => key v)
      _ = (n 2 : ℝ) * ((n 0 : ℝ) + (n 1 : ℝ) + (n 2 : ℝ) - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [htrace, Fintype.sum_sigma, Fin.sum_univ_three, h0, h1, h2]
  rw [b3_quotient_trace_sq]
  rw [Fin.sum_univ_three]
  ring
