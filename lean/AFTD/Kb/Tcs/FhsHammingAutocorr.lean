import AFTD.Prelude

/-!
# fhs_hamming_autocorr

Topic: information   Node: e6e3af9de002

Provenance: formalization of a published result. Source: arXiv:2611.11747, Section 1

For a frequency hopping sequence X : Fin v → Fin s and a shift τ : Fin v, the periodic Hamming autocorrelation at shift τ is the number of indices j ∈ Fin v such that X(j) = X(j + τ).
-/

/-- Periodic Hamming autocorrelation of a frequency hopping sequence at shift τ -/
def fhs_hamming_autocorr {v s : ℕ} (X : Fin v → Fin s) (τ : Fin v) : ℕ := (Finset.univ.filter (fun j => X j = X (j + τ))).card
