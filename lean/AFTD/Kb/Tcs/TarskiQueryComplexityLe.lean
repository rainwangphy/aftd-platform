import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# tarski_query_complexity_le

Topic: algorithms   Node: de9c4227d93d

Provenance: formalization of a published result. Source: arXiv:2610.07055 (Tarski fixed points in quasi-FPT queries), Sec. 1 (deterministic query complexity of Tarski(n, k)); the grid is {0, …, n−1}^k instead of {1, …, n}^k

Tarski(n, k) ≤ q: some deterministic query algorithm finds a fixed point of every monotone map f : [n]^k → [n]^k (componentwise order) using at most q queries.
-/

/-- `Tarski(n, k) ≤ q`: some deterministic query algorithm finds a fixed point of every monotone map `f : [n]^k → [n]^k` (componentwise order) with at most `q` queries. -/
def tarski_query_complexity_le (n k q : ℕ) : Prop :=
  ∃ t : TarskiQueryTree n k, ∀ f : (Fin k → Fin n) → (Fin k → Fin n), Monotone f →
    f (t.run f) = t.run f ∧ t.cost f ≤ q
