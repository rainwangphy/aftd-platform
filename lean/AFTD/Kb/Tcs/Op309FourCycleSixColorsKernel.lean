import AFTD.Prelude

/-!
# op309_four_cycle_six_colors_kernel

Topic: graphs   Node: ae80e0221595

Provenance: helper lemma. OP-309 cubic four-cycle obstruction, experiment 40796.

A sixth color cannot avoid five distinct colors in a five-color palette.
-/

theorem op309_four_cycle_six_colors_kernel (a b c p s d : Fin 5)
  (hfive : ([a,b,c,p,s] : List (Fin 5)).Nodup)
  (hd : d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ d ≠ p ∧ d ≠ s) : False := by
  have h6 : ([a,b,c,p,s,d] : List (Fin 5)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at *
    aesop
  have hh := h6.length_le_card
  norm_num at hh
