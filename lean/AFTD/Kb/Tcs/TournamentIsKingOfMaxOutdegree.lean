import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_is_king_of_max_outdegree

Topic: graphs   Node: f1fac9c5b248

Provenance: formalization of a published result. Source: arXiv:2610.40521 Equation 2

In every tournament on n vertices, every vertex of maximum outdegree is a king: every other vertex is reachable from it by a directed path of length at most two.
-/

open Classical in
/-- In any tournament on Fin n, every vertex of maximum outdegree is a king. -/
theorem tournament_is_king_of_max_outdegree {n : ℕ} (T : Digraph (Fin n))
    (hT : digraph_is_tournament T) (v : Fin n)
    (hmax : ∀ u : Fin n, digraph_out_count T u ≤ digraph_out_count T v) :
    ∀ u, u ≠ v → T.Adj v u ∨ ∃ w, T.Adj v w ∧ T.Adj w u := by
  intro u huv
  by_contra h
  push Not at h
  obtain ⟨hv_ne_u, hcover⟩ := h
  obtain ⟨hirr, htour⟩ := hT
  have huv_arc : T.Adj u v := (htour u v huv).mpr hv_ne_u
  have hcovx : ∀ x, T.Adj v x → T.Adj u x := by
    intro x hvx
    have hxu : x ≠ u := by
      intro hx; subst hx; exact hv_ne_u hvx
    exact (htour u x hxu.symm).mpr (hcover x hvx)
  have hsub : (insert v (Finset.univ.filter (fun w => T.Adj v w))) ⊆
      (Finset.univ.filter (fun w => T.Adj u w)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | hvx
    · exact huv_arc
    · exact hcovx x hvx
  have hnotmem : v ∉ Finset.univ.filter (fun w => T.Adj v w) := by
    simp [hirr v]
  have hcard : (Finset.univ.filter (fun w => T.Adj v w)).card + 1 ≤
      (Finset.univ.filter (fun w => T.Adj u w)).card := by
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotmem] at this
    exact this
  have hle := hmax u
  simp only [digraph_out_count] at hle
  omega
