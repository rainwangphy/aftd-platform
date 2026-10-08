import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocolDerandomizationSamples
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpace
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinNewmanIndexSpaceFintype
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPrivateCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinFiniteMessageProtocol
import AFTD.Kb.Tcs.CommunicationComplexityPublicCoinProtocol

/-!
# CommunicationComplexity.PublicCoin.newmanIndexSpace.nonempty

Topic: communication   Node: e7e16d4e1d20

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.PublicCoin.newmanIndexSpace.nonempty`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Newman.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CommunicationComplexity.PublicCoin.newmanIndexSpace.nonempty
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
noncomputable instance CommunicationComplexity.PublicCoin.newmanIndexSpace.nonempty
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Nonempty (newmanIndexSpace X Y ε c) :=
  ⟨⟨0, by simp [FiniteMessage.Protocol.derandomizationSamples]⟩⟩
