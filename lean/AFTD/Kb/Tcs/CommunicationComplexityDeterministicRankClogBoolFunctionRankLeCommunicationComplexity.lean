import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionRank
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionRankLePowOfCommunicationComplexityLe

/-!
# CommunicationComplexity.Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity

Topic: communication   Node: 43dafdb5d4b9

Provenance: formalization of a published result. Source: Log-rank lower bound on deterministic communication complexity, as formalized in TCSlib (`CommunicationComplexity.Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Log-rank lower bound on deterministic communication complexity. Let $X$ be a finite type and $Y$ a finite type, and let $f : X \to Y \to \mathrm{Bool}$
be a Boolean function with associated $0/1$ matrix $M_f \in \bbr^{X \times Y}$, whose
rank $\mathrm{rank}(f) = \mathrm{rank}_{\bbr}(M_f)$ is the rank of $f$. Then the
deterministic communication complexity $D(f) \in \bbn_\infty$ of $f$ satisfies
\[
  \lceil \log_2 \mathrm{rank}(f) \rceil \;\le\; D(f).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- The log-rank lower bound: the deterministic communication complexity of a Boolean function `f` is at least `⌈log₂ rank(M_f)⌉` [RY20, Thm 2.11] (historically [MS82]). -/
theorem CommunicationComplexity.Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) :
    (Nat.clog 2 (boolFunctionRank f) : ENat) ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast (Nat.clog_le_iff_le_pow (by norm_num)).mpr
      (boolFunctionRank_le_pow_of_communicationComplexity_le f n (le_of_eq h))
