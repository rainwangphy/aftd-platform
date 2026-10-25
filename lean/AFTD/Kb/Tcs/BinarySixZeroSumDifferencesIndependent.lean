import AFTD.Prelude

/-!
# binary_six_zero_sum_differences_independent

Topic: quantum   Node: 9cb42f7d3f6c

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

For six distinct binary vectors with zero sum, the differences of vectors 1 through 4 from vector 0 are linearly independent.
-/

theorem binary_six_zero_sum_differences_independent {n : ℕ}
    (v : Fin 6 → (Fin n → ZMod 2))
    (hinj : Function.Injective v) (hsum : ∑ j, v j = 0) :
    LinearIndependent (ZMod 2)
      (fun i : Fin 4 => v ⟨i.val + 1, by omega⟩ + v 0) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 (g 0) with h0 | h0 <;>
    rcases h01 (g 1) with h1 | h1 <;>
    rcases h01 (g 2) with h2 | h2 <;>
    rcases h01 (g 3) with h3 | h3
  · intro i; fin_cases i <;> assumption
  · exfalso
    apply (show (4 : Fin 6) ≠ 0 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (3 : Fin 6) ≠ 0 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (3 : Fin 6) ≠ 4 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (2 : Fin 6) ≠ 0 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (2 : Fin 6) ≠ 4 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (2 : Fin 6) ≠ 3 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (1 : Fin 6) ≠ 5 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    have hs := congrFun hsum x
    simp [Fin.sum_univ_succ] at hs
    linear_combination (norm := ring_nf) hx + hs <;> reduce_mod_char
  · exfalso
    apply (show (1 : Fin 6) ≠ 0 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (1 : Fin 6) ≠ 4 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (1 : Fin 6) ≠ 3 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (2 : Fin 6) ≠ 5 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    have hs := congrFun hsum x
    simp [Fin.sum_univ_succ] at hs
    linear_combination (norm := ring_nf) hx + hs <;> reduce_mod_char
  · exfalso
    apply (show (1 : Fin 6) ≠ 2 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    linear_combination (norm := ring_nf) hx <;> reduce_mod_char
  · exfalso
    apply (show (3 : Fin 6) ≠ 5 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    have hs := congrFun hsum x
    simp [Fin.sum_univ_succ] at hs
    linear_combination (norm := ring_nf) hx + hs <;> reduce_mod_char
  · exfalso
    apply (show (4 : Fin 6) ≠ 5 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    have hs := congrFun hsum x
    simp [Fin.sum_univ_succ] at hs
    linear_combination (norm := ring_nf) hx + hs <;> reduce_mod_char
  · exfalso
    apply (show (5 : Fin 6) ≠ 0 by decide) (hinj ?_)
    funext x
    have hx := congrFun hg x
    simp [Fin.sum_univ_succ, h0, h1, h2, h3] at hx
    have hs := congrFun hsum x
    simp [Fin.sum_univ_succ] at hs
    linear_combination (norm := ring_nf) hx + hs <;> reduce_mod_char
