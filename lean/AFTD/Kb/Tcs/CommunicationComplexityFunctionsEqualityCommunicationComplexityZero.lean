import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexityLeIff
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityEquality

/-!
# CommunicationComplexity.Functions.Equality.communicationComplexity_zero

Topic: communication   Node: ba401db1e645

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Equality.communicationComplexity_zero`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deterministic complexity of equality at $n = 0$. Let $\mathrm{equality}_0 \colon \mathrm{BoolInput}\,0 \times \mathrm{BoolInput}\,0 \to
\mathrm{Bool}$ be the equality function on $0$-bit Boolean inputs, and let
$D(\mathrm{equality}_0)$ denote its deterministic communication complexity, that is, the
infimum over all deterministic two-party protocols computing it of the worst-case number
of bits exchanged, taken in $\bbn_\infty$. Then
\[
  D(\mathrm{equality}_0) = 0.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
/-- When n = 0, equality has communication complexity 0: both inputs are the unique empty function, so the output is always `true`. -/
theorem CommunicationComplexity.Functions.Equality.communicationComplexity_zero :
    Deterministic.communicationComplexity (equality 0) = 0 := by
  apply le_antisymm
  · change Deterministic.communicationComplexity (equality 0) ≤ (0 : ℕ)
    rw [Deterministic.communicationComplexity_le_iff]
    exact ⟨Deterministic.Protocol.output true, by
      ext x y; simp [equality, Deterministic.Protocol.run, Subsingleton.elim x y],
      by simp [Deterministic.Protocol.complexity]⟩
  · exact bot_le
