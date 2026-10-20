import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# IsMulticommodityFlow

Topic: information   Node: 9dd8de687900

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

Given a capacitated network on a finite vertex type V with decidable equality, and unicast sessions indexed by a finite type K with decidable equality, a directed flow function f : K → V → V → ℝ is a valid fractional multicommodity flow supporting common rate r if all flows are non-negative, for each pair u ≠ v the total bidirectional flow across the edge does not exceed the edge capacity, and flow conservation holds at every vertex with net outflow r at the source, net inflow r at the sink, and zero divergence elsewhere.
-/

/-- Predicate asserting that a directed flow tensor is a valid fractional multicommodity flow supporting common rate r. -/
def IsMulticommodityFlow {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) (r : ℝ)
    (f : K → V → V → ℝ) : Prop :=
  (∀ k u v, 0 ≤ f k u v) ∧
  (∀ u v, u ≠ v → (∑ k, (f k u v + f k v u)) ≤ net.cap s(u, v)) ∧
  (∀ k v, (∑ w, f k v w) - (∑ u, f k u v) =
    if v = sess.src k then r else if v = sess.tgt k then -r else 0)
