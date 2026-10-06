import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotone

/-!
# mms_threshold_monotone

Topic: fair_division   Node: cce0514acf69

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Sec. 1 (definition of μ(n)); `sSup` convention for the unbounded case n = 1 added

μ(n): the largest m such that every instance with n agents, at most m goods and monotone valuations has an MMS allocation.
-/

/-- The threshold `μ(n)` of arXiv:2610.06125 for monotone valuations over goods: the largest `m` such that every instance with `n` agents and at most `m` goods has an MMS allocation. As an `sSup` in `ℕ` it is `0` when no largest such `m` exists; this happens only for `n = 1` (for `n ≥ 2` the set is bounded by the paper's Theorem 6, and for `n = 0` it is `{0}`). -/
noncomputable def mms_threshold_monotone (n : ℕ) : ℕ :=
  sSup {m | ∀ m' ≤ m, mms_exists_monotone n m'}
