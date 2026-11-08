import AFTD.Prelude

/-!
# swap_witness_w0

Topic: quantum   Node: b53c2e066d2e

Provenance: formalization of a published result. Source: arXiv:2610.34972 eq. (3)

For finite types dA and dR, the swap-based witness W_0 is the complex matrix on (dA × (dA × dR)) defined by (card dA : ℂ) • 1 - S_R, where S_R has entry 1 if a₁ = a'₂ ∧ a'₁ = a₂ ∧ r₁ = r₂ and 0 otherwise, representing (d 1_{AA'} - S_{AA'}) ⊗ 1_R.
-/

/-- The swap-based witness W_0 = (d • 1 - S) ⊗ 1 on (dA × (dA × dR)). -/
def swap_witness_w0 (dA dR : Type*) [Fintype dA] [DecidableEq dA] [Fintype dR] [DecidableEq dR] :
    Matrix (dA × (dA × dR)) (dA × (dA × dR)) ℂ := (Fintype.card dA : ℂ) • 1 -
    Matrix.of (fun (a1, (a'1, r1)) (a2, (a'2, r2)) =>
      if a1 = a'2 ∧ a'1 = a2 ∧ r1 = r2 then (1 : ℂ) else 0)
