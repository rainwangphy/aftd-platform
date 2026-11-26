import AFTD.Prelude

/-!
# op309_local_uncovered_28_arithmetic

Topic: graphs   Node: 09e6bc945d10

Provenance: helper lemma. OP-309 vertexwise local target-link counting; experiments 40592–40594.

The target-leaf charging inequality implies the n/28 uncovered-density bound.
-/

theorem op309_local_uncovered_28_arithmetic
  (n p s u : ℕ) (hn : n = 3*p+4*s+u)
  (hp : p+6*s ≤ 9*u) : n+14*s ≤ 28*u := by omega
