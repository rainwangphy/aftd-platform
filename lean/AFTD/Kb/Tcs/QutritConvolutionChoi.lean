import AFTD.Prelude

/-!
# qutrit_convolution_choi

Topic: quantum   Node: a3605b22dd06

Provenance: formalization of a published result. Source: OP-2299 (proposed here; it builds on the qutrit convolution channels with a magic environment and on the PPT symmetric-extension hierarchy for separability, arXiv:quant-ph/0308032). The Choi matrix of the convolution channel is given here by its explicit entries; qutrit_convolution_choi_eq_channel_choi proves that these are the entries of (id ⊗ N_σ)(|Φ_3⟩⟨Φ_3|) computed from the unitary U|x,y⟩ = |x+y, x+2y⟩.

Takes a complex 3×3 matrix σ : Matrix (Fin 3) (Fin 3) ℂ (no hypothesis on σ) and returns the complex matrix indexed by Fin 3 × Fin 3 (type Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) whose entry at row (a, b) and column (a', b') equals σ(b − a, b' − a') / 3 if a + b = a' + b' and equals 0 otherwise, where the additions and subtractions are those of Fin 3 (arithmetic modulo 3). This is the Choi matrix J_σ = (id ⊗ N_σ)(|Φ_3⟩⟨Φ_3|) of the qutrit convolution channel N_σ(ρ) = Tr_2[U (ρ ⊗ σ) U†] with U|x,y⟩ = |x+y, x+2y⟩ over F_3 and |Φ_3⟩ = Σ_j |j,j⟩/√3, the first index being the reference system A and the second the output B.
-/

/-- The Choi matrix of the qutrit convolution channel with environment `σ`, by its explicit entries. -/
noncomputable def qutrit_convolution_choi (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun p q => if p.1 + p.2 = q.1 + q.2 then σ (p.2 - p.1) (q.2 - q.1) / 3 else 0
