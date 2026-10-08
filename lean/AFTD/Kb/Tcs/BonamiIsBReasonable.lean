import AFTD.Prelude

/-!
# Bonami.IsBReasonable

Topic: combinatorics   Node: ffc0d7c932db

Provenance: formalization of a published result. Source: TCSlib, `Bonami.IsBReasonable`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/MomentBounds.lean (Apache-2.0); 1 verbatim; compiled here.

A real random variable $X$ on a measurable space $\Omega$ with measure $P$ is
\emph{$B$-reasonable} when its fourth moment is controlled by its second moment, namely
\[
\E[X^4] \le B \cdot \bigl(\E[X^2]\bigr)^2 .
\]
-/

open MeasureTheory ProbabilityTheory Filter in
/-- A real random variable is `B`-reasonable under a probability measure when `B ≥ 1`, its fourth moment is finite, and its fourth moment is at most `B` times the square of its second moment. **Source:** [OD14, Def. 9.1]. `MemLp X 4 P` explicitly enforces the source's intended finite-moment interpretation: it records almost-everywhere measurability and finite fourth moment. On a probability space it also guarantees finite second moment, so the real-valued moments agree with ordinary expectations rather than totalized nonintegrable integrals. -/
structure Bonami.IsBReasonable {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) (B : ℝ) : Prop where
  /-- The underlying measure is a probability law. -/
  probability : IsProbabilityMeasure P
  /-- The reasonability parameter is at least one. -/
  one_le : 1 ≤ B
  /-- The random variable is almost-everywhere measurable with finite fourth moment. -/
  memLp : MemLp X 4 P
  /-- The fourth moment is bounded by the prescribed multiple of the squared second moment. -/
  moment_le : moment X 4 P ≤ B * (moment X 2 P) ^ 2
