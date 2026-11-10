import AFTD.Prelude
import AFTD.Kb.Tcs.FhsHammingAutocorr

/-!
# fhs_autocorr_le

Topic: information   Node: 7433abeb63ff

Provenance: formalization of a published result. Source: arXiv:2611.11747, Section 1

A frequency hopping sequence X : Fin v → Fin s has periodic Hamming autocorrelation bounded by b if for all nonzero shifts τ, the Hamming autocorrelation at τ is at most b.
-/

/-- A frequency hopping sequence has out-of-phase Hamming autocorrelation bounded by b -/
def fhs_autocorr_le {v s : ℕ} [NeZero v] (X : Fin v → Fin s) (b : ℕ) : Prop := ∀ τ : Fin v, τ ≠ 0 → fhs_hamming_autocorr X τ ≤ b
