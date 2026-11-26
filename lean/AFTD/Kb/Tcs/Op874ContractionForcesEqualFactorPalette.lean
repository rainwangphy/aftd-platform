import AFTD.Prelude

/-!
# op874_contraction_forces_equal_factor_palette

Topic: graphs   Node: 0213fcfae671

Provenance: helper lemma. Disjoint matching-palette obstruction for OP-874; https://arxiv.org/abs/2610.41950.

Four pairwise distinct colors exhaust the four-color palette, so any fifth color distinct from three of them equals the fourth.
-/

theorem op874_contraction_forces_equal_factor_palette
    (a b c d e : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hea : e ≠ a) (hec : e ≠ c) (hed : e ≠ d) : e = b := by
  have hcard : ({a,b,c,d} : Finset (Fin 4)).card = 4 := by
    simp [hab,hac,had,hbc,hbd,hcd]
  have hall : ({a,b,c,d} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  have he : e ∈ ({a,b,c,d} : Finset (Fin 4)) := by
    rw [hall]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h | h
  · exact (hea h).elim
  · exact h
  · exact (hec h).elim
  · exact (hed h).elim
