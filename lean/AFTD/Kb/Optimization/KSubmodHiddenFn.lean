import AFTD.Prelude

/-!
# k_submod_hidden_fn

Topic: submodular   Node: 503c576b890e

Provenance: formalization of a published result. Source: arXiv:2610.26677, Eq. (6)

For implicit n and k, a bivariate function H : ℝ → ℝ → ℝ, a hidden assignment σ : Fin n → Fin k, and a partial assignment x : Fin n → Option (Fin k), k_submod_hidden_fn H σ x is defined as H (c / n) ((m - c) / n) / H 1 0, where c is the number of elements e with x e = some (σ e) and m is the number of elements e with x e ≠ none.
-/

/-- The normalized hidden-label kernel function f_σ on assignments. -/
noncomputable def k_submod_hidden_fn {n k : ℕ} (H : ℝ → ℝ → ℝ) (σ : Fin n → Fin k)
    (x : Fin n → Option (Fin k)) : ℝ :=
  let c := (Finset.univ.filter (fun e => x e = some (σ e))).card
  let m := (Finset.univ.filter (fun e => x e ≠ none)).card
  H ((c : ℝ) / n) (((m : ℝ) - (c : ℝ)) / n) / H 1 0
