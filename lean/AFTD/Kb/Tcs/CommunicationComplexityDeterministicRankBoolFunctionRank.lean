import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionMatrix

/-!
# CommunicationComplexity.Deterministic.Rank.boolFunctionRank

Topic: communication   Node: 750844611982

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Rank.boolFunctionRank`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The rank of a Boolean function $f : X \to Y \to \mathrm{Bool}$ is the
$\mathbb{R}$-rank of its $0/1$ matrix $M_f$, i.e.\
$\mathrm{rank}(f) = \mathrm{rank}_{\mathbb{R}}(M_f) \in \mathbb{N}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The rank of a Boolean function `f`, defined as the rank over `ℝ` of its real-valued communication matrix [RY20, Ch. 2] / [Rou16, §4.2.3 Definition (matrix representation)]. -/
noncomputable def CommunicationComplexity.Deterministic.Rank.boolFunctionRank {X Y : Type*} [Fintype Y]
    (f : X → Y → Bool) : ℕ :=
  (boolFunctionMatrix f).rank
