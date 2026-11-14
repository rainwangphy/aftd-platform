import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMap
import AFTD.Kb.Tcs.IsBraidSolution

/-!
# poset_sorting_map_idempotent_braid

Topic: combinatorics   Node: e013246a62fa

Provenance: helper lemma. Step of arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2)

For every partially ordered set P, the sorting map R_P (swapping (x,y) to (y,x) when y<x, fixing it otherwise) satisfies the braid equation and is idempotent: R_P ∘ R_P = R_P.
-/

open Classical in
private lemma psm_apply_ib {P : Type*} [PartialOrder P] (p : P × P) :
    poset_sorting_map P p = if p.2 < p.1 then (p.2, p.1) else p := by
  rfl

theorem poset_sorting_map_idempotent_braid (P : Type*) [PartialOrder P] :
    is_braid_solution (poset_sorting_map P) ∧
      poset_sorting_map P ∘ poset_sorting_map P = poset_sorting_map P := by
  constructor
  · dsimp only [is_braid_solution]
    funext ⟨x, y, z⟩
    simp only [Function.comp_apply, psm_apply_ib]
    by_cases h1 : y < x <;> by_cases h2 : z < y <;> by_cases h3 : z < x <;>
      by_cases h4 : x < y <;> by_cases h5 : y < z <;> by_cases h6 : x < z <;>
      simp only [h1, h2, h3, h4, h5, h6, if_true, if_false] <;>
      first
        | rfl
        | exact absurd h4 (lt_asymm h1)
        | exact absurd h5 (lt_asymm h2)
        | exact absurd h6 (lt_asymm h3)
        | exact absurd (lt_trans h2 h1) h3
        | exact absurd (lt_trans h4 h5) h6
        | exact absurd (lt_trans h1 h6) h5
        | exact absurd (lt_trans h3 h4) h2
        | exact absurd (lt_trans h6 h2) h4
        | exact absurd (lt_trans h5 h3) h1
  · funext ⟨x, y⟩
    simp only [Function.comp_apply, psm_apply_ib]
    by_cases h : y < x
    · simp [h, lt_asymm h]
    · simp [h]
