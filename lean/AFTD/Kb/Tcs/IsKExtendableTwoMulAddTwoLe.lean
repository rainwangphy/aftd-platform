import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# is_k_extendable_two_mul_add_two_le

Topic: graphs   Node: e33ebbec0f6a

Provenance: helper lemma. sanity lemma for is_k_extendable (arXiv:2611.22690, Section 2)

A k-extendable graph has at least 2k+2 vertices.
-/

theorem is_k_extendable_two_mul_add_two_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : is_k_extendable G k) : 2 * k + 2 ≤ Fintype.card V := by
  exact h.1
