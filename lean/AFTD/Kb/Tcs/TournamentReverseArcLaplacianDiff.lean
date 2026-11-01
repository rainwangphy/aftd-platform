import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverseArc
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutLaplacian
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_reverse_arc_laplacian_diff

Topic: graphs   Node: 2f690a8c5189

Provenance: helper lemma. step towards tournament_reverse_arc_arborescence_count_lt

Reversing an arc u → v of a tournament updates the out-degree Laplacian by an explicit rank-one matrix (e_u + e_v)(e_v - e_u)^T.
-/

/-- Reversing an arc u → v of a tournament updates the out-degree Laplacian by the explicit rank-one matrix (e_u + e_v)(e_v - e_u)^T. -/
theorem tournament_reverse_arc_laplacian_diff {n : ℕ} (T : Digraph (Fin n)) [DecidableRel T.Adj]
    (hT : digraph_is_tournament T) (u v : Fin n) (huv : T.Adj u v) :
    digraph_out_laplacian (digraph_reverse_arc T u v) - digraph_out_laplacian T =
      Matrix.of (fun i j =>
        (if i = u ∨ i = v then (1 : ℝ) else 0) *
        (if j = v then (1 : ℝ) else if j = u then -1 else 0)) := by
  ext i j
  rw [Matrix.of_apply]
  have unev : u ≠ v := by
    rintro rfl
    exact hT.1 u huv
  have unev' : v ≠ u := unev.symm
  have hvu : ¬ T.Adj v u := by
    intro h
    exact (hT.2 u v unev).mp huv h
  have out_u : (digraph_out_count (digraph_reverse_arc T u v) u : ℝ) = (digraph_out_count T u : ℝ) - 1 := by
    have h_filter : Finset.filter (fun w => (digraph_reverse_arc T u v).Adj u w) Finset.univ =
        (Finset.filter (fun w => T.Adj u w) Finset.univ).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hw : w = v
      · subst hw; simp [unev, hvu]
      · simp [hw, unev]
    unfold digraph_out_count
    rw [h_filter]
    have hmem : v ∈ Finset.filter (fun w => T.Adj u w) Finset.univ := by simp [huv]
    rw [Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (Finset.filter (fun w => T.Adj u w) Finset.univ).card :=
      Finset.card_pos.mpr ⟨v, hmem⟩
    push_cast [hpos]
    rfl
  have out_v : (digraph_out_count (digraph_reverse_arc T u v) v : ℝ) = (digraph_out_count T v : ℝ) + 1 := by
    have h_filter : Finset.filter (fun w => (digraph_reverse_arc T u v).Adj v w) Finset.univ =
        insert u (Finset.filter (fun w => T.Adj v w) Finset.univ) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hw : w = u
      · subst hw; simp [unev', huv]
      · simp [hw, unev']
    unfold digraph_out_count
    rw [h_filter]
    have hnmem : u ∉ Finset.filter (fun w => T.Adj v w) Finset.univ := by simp [hvu]
    rw [Finset.card_insert_of_notMem hnmem]
    push_cast
    rfl
  have out_other : ∀ k, k ≠ u → k ≠ v →
      (digraph_out_count (digraph_reverse_arc T u v) k : ℝ) = (digraph_out_count T k : ℝ) := by
    intro k hku hkv
    have h : digraph_out_count (digraph_reverse_arc T u v) k = digraph_out_count T k := by
      unfold digraph_out_count
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : ¬ (k = u ∧ w = v) := fun h => hku h.1
      have h2 : ¬ (k = v ∧ w = u) := fun h => hkv h.1
      show (if (k = u ∧ w = v) ∨ (k = v ∧ w = u) then T.Adj w k else T.Adj k w) ↔ T.Adj k w
      simp [h1, h2]
    rw [h]
  rw [Matrix.sub_apply]
  unfold digraph_out_laplacian
  simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  have hTloop : ∀ x, ¬ T.Adj x x := hT.1
  by_cases hiu : i = u
  · subst i
    rw [out_u]
    by_cases hjv : j = v
    · subst j
      simp [unev, unev', huv, hvu]
    · by_cases hju : j = u
      · subst j
        simp [unev, hTloop u]
      · simp [unev, hjv, hju, Ne.symm hju]
  · by_cases hiv : i = v
    · subst i
      rw [out_v]
      by_cases hjv : j = v
      · subst j
        simp [unev', hTloop v]
      · by_cases hju : j = u
        · subst j
          simp [unev, unev', huv, hvu]
        · simp [unev', hjv, Ne.symm hjv, hju]
    · rw [out_other i hiu hiv]
      simp [hiu, hiv]
