import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityCoinTape

/-!
# CommunicationComplexity.coinTapeMeasure

Topic: communication   Node: 8e5c7f4d8203

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.coinTapeMeasure`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/CoinTape.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The uniform probability measure on `CoinTape n`. Every outcome of `n` independent fair coin flips is equally likely.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- The uniform probability measure on `CoinTape n`. Every outcome of `n` independent fair coin flips is equally likely. -/
noncomputable instance CommunicationComplexity.coinTapeMeasure (n : ℕ) : MeasureSpace (CoinTape n) where
  volume := uniformOn Set.univ
