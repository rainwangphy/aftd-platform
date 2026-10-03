import AFTD.Prelude

/-!
# proper_score_of_exposure

Topic: mechanism_design   Node: e1d96984518d

The score of forecast x on outcome j for the proper scoring rule with expected reward G and exposure g: G(x) + <g(x), e_j - x>.
-/

noncomputable def proper_score_of_exposure {n : ℕ} (G : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  G x + ∑ k, g x k * ((if k = j then 1 else 0) - x k)
