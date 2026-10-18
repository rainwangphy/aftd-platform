import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tarski_box_query_le

Topic: algorithms   Node: 950fca5b5504

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Box-local Tarski query invariant: for every sub-box [a,b] (a ≤ b) of [n]^k there is a single deterministic query tree — depending only on the box, not on the unknown f — that, against every monotone f with a ≤ f a and f b ≤ b, outputs a fixed point of f lying inside [a,b] using at most q queries.
-/

/-- Box-local Tarski query invariant: one tree, uniform in the oracle f, finds a fixed point inside any sub-box [a,b]. -/
def tarski_box_query_le (n k q : ℕ) : Prop := ∀ a b : Fin k → Fin n, a ≤ b → ∃ t : TarskiQueryTree n k,
    ∀ f : (Fin k → Fin n) → Fin k → Fin n, Monotone f → a ≤ f a → f b ≤ b →
      a ≤ TarskiQueryTree.run f t ∧ TarskiQueryTree.run f t ≤ b ∧
      f (TarskiQueryTree.run f t) = TarskiQueryTree.run f t ∧
      TarskiQueryTree.cost f t ≤ q
