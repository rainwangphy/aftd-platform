import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.CodeProj
import AFTD.Kb.Tcs.PauliOpAdjoint
import AFTD.Kb.Tcs.Weight
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliOp

/-!
# KnillLaflamme

Topic: quantum   Node: 9d4000067173

Provenance: formalization of a published result. Source: TCSlib, `KnillLaflamme`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

A subspace $C \le \mathcal{H}_n$ satisfies the \emph{Knill--Laflamme condition}
for $t$-error correction if for all Pauli strings $E,F$ with $\mathrm{wt}(E),\mathrm{wt}(F) \le t$
there exists $\lambda_{EF}\in\mathbb{C}$ such that
$P_C\,E^\dagger F\,P_C = \lambda_{EF}\,P_C$,
where $P_C$ is the orthogonal projection onto $C$.
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
/-- The Knill–Laflamme quantum error correction condition: for all Pauli errors `E`, `F` of weight ≤ t, the code projection satisfies `Π_C ∘ E† ∘ F ∘ Π_C = α_{E,F} • Π_C` for some scalar. -/
noncomputable def KnillLaflamme (n : ℕ) (C : Submodule ℂ (Hn n)) (t : ℕ) : Prop :=
  ∀ E F : PauliString n, weight E ≤ t → weight F ≤ t →
    ∃ α : ℂ,
      (codeProj C).comp ((pauliOpAdjoint E).comp ((pauliOp F).comp (codeProj C))) =
      α • (codeProj C)
