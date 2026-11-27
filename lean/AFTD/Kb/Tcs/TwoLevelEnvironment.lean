import AFTD.Prelude

/-!
# two_level_environment

Topic: quantum   Node: f2a502b907ef

Provenance: formalization of a published result. Source: OP-2466 (proposed here; it builds on the qutrit convolution channels of arXiv:2609.16200, whose Theorem 8 gives the exact PPT and entanglement-breaking threshold 2/5 on a balanced two-level qutrit slice, and on arXiv:2611.09594, which shows PPT and entanglement breaking differ for another convolution environment). The noisy two-level environment σ_{p,t} of the entry.

With d : ℕ and real numbers p, t, returns the complex d×d matrix (1 − t)·I/d + t·|ψ⟩⟨ψ|, where ψ : Fin d → ℝ has ψ j = √p when the natural-number value of j is 0, ψ j = √(1 − p) when it is 1, and ψ j = 0 otherwise; that is, entry (j, l) is (1 − t)/d if j = l and 0 otherwise, plus t·ψ j·ψ l. For p, t in [0, 1] and d ≥ 2 it is the state σ_{p,t} = (1 − t) I_d/d + t|ψ_p⟩⟨ψ_p| with |ψ_p⟩ = √p|0⟩ + √(1 − p)|1⟩.
-/

/-- The environment `(1 - t) I/d + t |ψ_p⟩⟨ψ_p|` with `ψ_p = √p |0⟩ + √(1-p) |1⟩`. -/
noncomputable def two_level_environment (d : ℕ) (p t : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j l =>
    ((if j = l then (1 - t) / d else 0 : ℝ) : ℂ) +
      (t : ℂ) * ((if (j : ℕ) = 0 then Real.sqrt p else if (j : ℕ) = 1 then Real.sqrt (1 - p) else 0 : ℝ) : ℂ) *
        ((if (l : ℕ) = 0 then Real.sqrt p else if (l : ℕ) = 1 then Real.sqrt (1 - p) else 0 : ℝ) : ℂ)
