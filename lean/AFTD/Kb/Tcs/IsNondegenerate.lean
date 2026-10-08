import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.CodeProj
import AFTD.Kb.Tcs.PauliOpAdjoint
import AFTD.Kb.Tcs.KnillLaflamme
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliOp

/-!
# IsNondegenerate

Topic: quantum   Node: 7854e0d2f6a4

Provenance: formalization of a published result. Source: TCSlib, `IsNondegenerate`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

A code is \emph{non-degenerate} if it satisfies the Knill--Laflamme condition
and additionally $P_C E^\dagger F P_C = 0$ whenever $E \neq F$.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
/-- A code is non-degenerate if it satisfies the Knill–Laflamme condition with all off-diagonal terms zero: for distinct errors `E ≠ F` of weight ≤ t, `Π_C ∘ E† ∘ F ∘ Π_C = 0`. -/
noncomputable def IsNondegenerate (n : ℕ) (C : Submodule ℂ (Hn n)) (t : ℕ) : Prop :=
  KnillLaflamme n C t ∧
  ∀ E F : PauliString n, weight E ≤ t → weight F ≤ t → E ≠ F →
    (codeProj C).comp ((pauliOpAdjoint E).comp ((pauliOp F).comp (codeProj C))) = 0
