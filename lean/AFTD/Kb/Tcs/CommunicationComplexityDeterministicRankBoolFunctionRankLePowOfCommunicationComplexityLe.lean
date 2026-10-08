import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicMonoPartitionOfCommunicationComplexityLe
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionRank
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionRankLeNcard

/-!
# CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_pow_of_communicationComplexity_le

Topic: communication   Node: 894518810d9a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_pow_of_communicationComplexity_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Rank bound from communication complexity. Let $X$ and $Y$ be finite types and let $f : X \to Y \to \mathrm{Bool}$ be a two-party
Boolean function, whose rank $\mathrm{rank}(f)$ is the $\bbr$-rank of the $0/1$ matrix
$M_f \in \bbr^{X \times Y}$ with $(M_f)_{x,y} = 1$ exactly when $f\,x\,y =
\mathrm{true}$. If the deterministic communication complexity $D(f)$ is at most $n$ for
some $n \in \bbn$, then $\mathrm{rank}(f) \le 2^n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Rectangle in
/-- If the deterministic communication complexity of `f` is at most `n`, then the rank of `f` is at most `2 ^ n` [RY20, Lemma 2.10]: a protocol of complexity `n` induces a monochromatic rectangle partition with at most `2 ^ n` parts [RY20, Thm 1.7]. -/
theorem CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_pow_of_communicationComplexity_le
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) (n : ℕ)
    (h : Deterministic.communicationComplexity f ≤ n) :
    boolFunctionRank f ≤ 2 ^ n := by
  obtain ⟨Part, hPart, hCard⟩ := Deterministic.mono_partition_of_communicationComplexity_le f n h
  exact (boolFunctionRank_le_ncard f Part hPart).trans hCard
