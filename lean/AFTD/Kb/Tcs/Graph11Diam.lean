import AFTD.Prelude
import AFTD.Kb.Tcs.Graph11

/-!
# graph_11_diam

Topic: graphs   Node: 52073a34c3ee

Provenance: formalization of a published result. Source: arXiv:2610.39430 Lemma 3.3

The simple graph G_11 has diameter 2.
-/

def graph_11_diam_b (u v : Fin 11) : Bool :=
  (u == 0 && v == 1) ||
  (u == 1 && v == 2) ||
  (u == 2 && v == 3) ||
  (u == 3 && v == 0) ||
  (u == 4 && (v == 0 || v == 1)) ||
  (u == 5 && (v == 1 || v == 2)) ||
  (u == 6 && (v == 2 || v == 3)) ||
  (u == 7 && (v == 3 || v == 0)) ||
  (u == 8 && (v == 4 || v == 6)) ||
  (u == 9 && (v == 5 || v == 7)) ||
  (u == 10 && (v == 4 || v == 5 || v == 6 || v == 7 || v == 8 || v == 9))

def graph_11_diam_adj_b (u v : Fin 11) : Bool :=
  (u != v) && (graph_11_diam_b u v || graph_11_diam_b v u)

lemma graph_11_diam_adj_b_iff (u v : Fin 11) : graph_11_diam_adj_b u v = true ↔ graph_11.Adj u v := by
  dsimp [graph_11_diam_adj_b, graph_11_diam_b, graph_11, SimpleGraph.fromRel]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, or_assoc]

instance graph_11_diam_decidableAdj : DecidableRel graph_11.Adj := fun u v =>
  decidable_of_iff (graph_11_diam_adj_b u v = true) (graph_11_diam_adj_b_iff u v)

lemma graph_11_diam_common_neighbor :
    ∀ u v : Fin 11, u ≠ v → ¬ graph_11.Adj u v → ∃ w, graph_11.Adj u w ∧ graph_11.Adj w v := by
  decide

lemma graph_11_diam_edist_le_two (u v : Fin 11) : graph_11.edist u v ≤ 2 := by
  by_cases huv : u = v
  · rw [huv, SimpleGraph.edist_self]
    exact bot_le
  · by_cases hadj : graph_11.Adj u v
    · rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
      exact one_le_two
    · obtain ⟨w, hw1, hw2⟩ := graph_11_diam_common_neighbor u v huv hadj
      have ht := graph_11.edist_triangle (u := u) (v := w) (w := v)
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr hw1, SimpleGraph.edist_eq_one_iff_adj.mpr hw2] at ht
      exact ht

lemma graph_11_diam_enat_two_le_of_not_le_one {x : ℕ∞} (h : ¬ (x ≤ 1)) : 2 ≤ x := by
  rw [not_le] at h
  cases x with
  | top => exact le_top
  | coe n => exact Nat.cast_le.mpr (Nat.succ_le_of_lt (Nat.cast_lt.mp h))

lemma graph_11_diam_edist_0_2_ge_two : 2 ≤ graph_11.edist 0 2 := by
  apply graph_11_diam_enat_two_le_of_not_le_one
  intro h
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq] at h
  rcases h with h | h
  · revert h; decide
  · revert h; decide

/-- The simple graph G_11 has diameter 2. -/
theorem graph_11_diam : graph_11.diam = 2 := by
  have hediam : graph_11.ediam = 2 := by
    apply le_antisymm
    · exact SimpleGraph.ediam_le_of_edist_le graph_11_diam_edist_le_two
    · exact le_trans graph_11_diam_edist_0_2_ge_two SimpleGraph.edist_le_ediam
  rw [SimpleGraph.diam, hediam]
  rfl
