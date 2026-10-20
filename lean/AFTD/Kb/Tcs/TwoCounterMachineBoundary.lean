import AFTD.Prelude

/-!
# two_counter_machine_boundary

Topic: automata   Node: eecc848f19fd

Provenance: helper lemma. step towards symmetric_two_counter_boundary_reachability_semilinear

A configuration of a 2-counter machine lies on the boundary if at least one of its two counters is zero.
-/

/-- The boundary predicate: at least one counter is zero. Zero tests are enabled exactly at boundary configurations. -/
def two_counter_machine_boundary {Q : Type*} (c : Q × ℕ × ℕ) : Prop := c.2.1 = 0 ∨ c.2.2 = 0
