import AFTD.Prelude

/-!
# zero_sum_constant_s_star

Topic: elementary_number_theory   Node: 07d4acca0be6

Provenance: formalization of a published result. Source: scout/2611-14248-the-zero-sum-constant-mathsf-s-p-and-inverse-problem.md:116

The zero-sum constant $\mathsf{s}_p^*$ is defined as the infimum of lengths $l$ such that every multiset $W$ of size $l$ of units in $\mathbb{Z}/p^2\mathbb{Z}$ has a sub-multiset $T \le W$ of cardinality $p$ with `(T.sum : ZMod (p^2)).val % p = 0` and `(T.sum : ZMod (p^2)).val % p^2 ≠ 0`.
-/

/-- The zero-sum constant s_p^*: the infimum of lengths l such that every multiset of l units in ZMod (p^2) has a p-subsequence with sum divisible by p but not p^2. -/
noncomputable def zero_sum_constant_s_star (p : ℕ) : ℕ := sInf {l : ℕ | ∀ W : Multiset (ZMod (p ^ 2)), W.card = l →
    (∀ x ∈ W, IsUnit x) →
    ∃ T ≤ W, T.card = p ∧ T.sum.val % p = 0 ∧ T.sum.val % p ^ 2 ≠ 0}
