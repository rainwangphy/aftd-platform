import AFTD.Prelude
import AFTD.Kb.Tcs.Op309K33WitnessMinDegree

/-!
# op309_rook_rich_three_star_impossible

Topic: graphs   Node: ad7f027bed3c

Provenance: helper lemma. OP-309 six-vertex and cubic bipartite-block obstruction, experiment 40722.

In the three-by-three rook model, the three edges in one row cannot all be rich in a proper five-edge-coloring.
-/

theorem op309_rook_rich_three_star_impossible
    (i k : Fin 3) (hik : i ≠ k) (c : Fin 3 × Fin 3 → Fin 5)
    (hproper : ∀ e f, op309_rook_adj e f → c e ≠ c f)
    (hrich : ∀ j : Fin 3, ∀ f g, op309_rook_adj (i,j) f →
      op309_rook_adj (i,j) g → f ≠ g → c f ≠ c g) : False := by
  have hab : c (i,0) ≠ c (i,1) := hproper _ _ (by simp [op309_rook_adj])
  have hac : c (i,0) ≠ c (i,2) := hproper _ _ (by simp [op309_rook_adj])
  have hbc : c (i,1) ≠ c (i,2) := hproper _ _ (by simp [op309_rook_adj])
  have hxy : c (k,0) ≠ c (k,1) := hproper _ _ (by simp [op309_rook_adj])
  have hxz : c (k,0) ≠ c (k,2) := hproper _ _ (by simp [op309_rook_adj])
  have hyz : c (k,1) ≠ c (k,2) := hproper _ _ (by simp [op309_rook_adj])
  have hxa : c (k,0) ≠ c (i,0) := hproper _ _ (by simp [op309_rook_adj, hik, Ne.symm hik])
  have hyb : c (k,1) ≠ c (i,1) := hproper _ _ (by simp [op309_rook_adj, hik, Ne.symm hik])
  have hzc : c (k,2) ≠ c (i,2) := hproper _ _ (by simp [op309_rook_adj, hik, Ne.symm hik])
  have hxb : c (k,0) ≠ c (i,1) := hrich 0 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have hxc : c (k,0) ≠ c (i,2) := hrich 0 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have hya : c (k,1) ≠ c (i,0) := hrich 1 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have hyc : c (k,1) ≠ c (i,2) := hrich 1 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have hza : c (k,2) ≠ c (i,0) := hrich 2 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have hzb : c (k,2) ≠ c (i,1) := hrich 2 _ _ (by simp [op309_rook_adj, hik, Ne.symm hik]) (by simp [op309_rook_adj]) (by simp [hik, Ne.symm hik])
  have h6 : ([c (i,0),c (i,1),c (i,2),c (k,0),c (k,1),c (k,2)] : List (Fin 5)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at *
    aesop
  have hh := h6.length_le_card
  norm_num at hh
