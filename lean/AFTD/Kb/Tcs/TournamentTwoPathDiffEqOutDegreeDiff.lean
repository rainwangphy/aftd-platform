import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTwoPathCount
import AFTD.Kb.Tcs.DigraphOutDegree
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_two_path_diff_eq_out_degree_diff

Topic: graphs   Node: 9e4a8c53a932

Provenance: formalization of a published result. Source: arXiv:2610.39702 Lemma 2.3 -- Quantum Query Complexity of Tournament Solutions

In any finite tournament T, if there is an arc from u to v, then the difference between the number of directed two-paths from v to u and from u to v equals the out-degree of v minus the out-degree of u plus 1: p(v, u) - p(u, v) = d⁺(v) - d⁺(u) + 1.
-/

/-- In a tournament, if u → v then p(v, u) - p(u, v) = d⁺(v) - d⁺(u) + 1. -/
theorem tournament_two_path_diff_eq_out_degree_diff {V : Type*} [Fintype V] (T : Digraph V) [DecidableRel T.Adj] (hT : digraph_is_tournament T) {u v : V} (huv : T.Adj u v) : (digraph_two_path_count T v u : ℤ) - (digraph_two_path_count T u v : ℤ) = (digraph_out_degree T v : ℤ) - (digraph_out_degree T u : ℤ) + 1 := by
  classical
  obtain ⟨hirr, htour⟩ := hT
  have huv_ne : u ≠ v := by rintro rfl; exact hirr u huv
  have hvu : ¬ T.Adj v u := (htour u v huv_ne).mp huv
  set P : Finset V := Finset.univ.filter (fun w => T.Adj v w ∧ T.Adj w u) with hP
  set Q : Finset V := Finset.univ.filter (fun w => T.Adj u w ∧ T.Adj w v) with hQ
  set C : Finset V := Finset.univ.filter (fun w => T.Adj u w ∧ T.Adj v w) with hC
  have hdisjPC : Disjoint P C := by
    rw [hP, hC, Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    obtain ⟨-, hwu⟩ := hw
    obtain ⟨huw, -⟩ := hw'
    by_cases h : w = u
    · exact hirr u (h ▸ hwu)
    · exact (htour w u h).mp hwu huw
  have hdisjQC : Disjoint Q C := by
    rw [hQ, hC, Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    obtain ⟨-, hwv⟩ := hw
    obtain ⟨-, hvw⟩ := hw'
    by_cases h : w = v
    · exact hirr v (h ▸ hwv)
    · exact (htour w v h).mp hwv hvw
  have hA : (Finset.univ.filter (T.Adj v)) = P ∪ C := by
    rw [hP, hC]
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hvw
      have hwu : w ≠ u := by rintro rfl; exact hvu hvw
      by_cases h : T.Adj w u
      · exact Or.inl ⟨hvw, h⟩
      · exact Or.inr ⟨(htour u w hwu.symm).mpr h, hvw⟩
    · rintro (⟨hvw, -⟩ | ⟨-, hvw⟩)
      · exact hvw
      · exact hvw
  have hB : (Finset.univ.filter (T.Adj u)) = insert v (Q ∪ C) := by
    rw [hQ, hC]
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]
    constructor
    · intro huw
      by_cases hwv : w = v
      · exact Or.inl hwv
      · by_cases h : T.Adj w v
        · exact Or.inr (Or.inl ⟨huw, h⟩)
        · exact Or.inr (Or.inr ⟨huw, (htour v w (Ne.symm hwv)).mpr h⟩)
    · rintro (rfl | ⟨huw, -⟩ | ⟨huw, -⟩)
      · exact huv
      · exact huw
      · exact huw
  have hvnot : v ∉ Q ∪ C := by
    rw [hQ, hC]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    exact ⟨fun h => hirr v h.2, fun h => hirr v h.2⟩
  have h1 : digraph_out_degree T v = digraph_two_path_count T v u + C.card := by
    rw [digraph_out_degree, digraph_two_path_count, ← hP]
    rw [hA, Finset.card_union_of_disjoint hdisjPC]
  have h2 : digraph_out_degree T u = digraph_two_path_count T u v + C.card + 1 := by
    rw [digraph_out_degree, digraph_two_path_count, ← hQ]
    rw [hB, Finset.card_insert_of_notMem hvnot, Finset.card_union_of_disjoint hdisjQC]
  omega
