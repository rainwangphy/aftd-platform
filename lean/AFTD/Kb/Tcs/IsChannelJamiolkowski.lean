import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceRight
import AFTD.Kb.Tcs.MatrixPosSemidefTraceRight

/-!
# is_channel_jamiolkowski

Topic: quantum   Node: b59620db8239

Provenance: formalization of a published result. Source: arXiv:2610.34972 Section 1.3, equation (7)

A matrix J on H_A tensor H_B is the Jamiołkowski matrix of a quantum channel if its partial transpose on the input space is positive semidefinite and has partial trace over the output space equal to the identity matrix on the input space.
-/

/-- A matrix J is the Jamiolkowski matrix of a quantum channel if its partial transpose is positive semidefinite and has trace over the output space equal to 1. -/
def is_channel_jamiolkowski {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (J : Matrix (dA × dB) (dA × dB) ℂ) : Prop := letI : PartialOrder ℂ := Complex.partialOrder
  (Matrix.of (fun (a1, b1) (a2, b2) => J (a2, b1) (a1, b2)) : Matrix (dA × dB) (dA × dB) ℂ).PosSemidef ∧
    Matrix.traceRight (Matrix.of (fun (a1, b1) (a2, b2) => J (a2, b1) (a1, b2))) = 1
