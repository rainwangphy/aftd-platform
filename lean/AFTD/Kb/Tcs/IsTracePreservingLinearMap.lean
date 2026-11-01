import AFTD.Prelude

/-!
# is_trace_preserving_linear_map

Topic: quantum   Node: 62b5b70a91ca

Provenance: formalization of a published result. Source: arXiv:2610.37187 Def. 3

A linear map Φ on d × d complex matrices is trace-preserving if the trace of Φ(X) equals the trace of X for all d × d complex matrices X.
-/

/-- A linear map on d × d complex matrices is trace-preserving if the matrix trace of Φ(X) equals the matrix trace of X for all X. -/
def is_trace_preserving_linear_map (d : ℕ) (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop := ∀ (X : Matrix (Fin d) (Fin d) ℂ), Matrix.trace (Φ X) = Matrix.trace X
