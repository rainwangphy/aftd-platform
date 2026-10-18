import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTreeBind
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryTreeCost

/-!
# tarski_query_tree_bind_spec

Topic: algorithms   Node: b8f7b3a3962d

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Run/cost law for sequential composition: the run of a bind is the run of the continuation g at the output of the first tree, and the cost of a bind is the cost of the first tree plus the cost of the continuation at that output.
-/

/-- Run and cost of a sequential composition. -/
theorem tarski_query_tree_bind_spec {n k : ℕ} (g : (Fin k → Fin n) → TarskiQueryTree n k)
    (f : (Fin k → Fin n) → Fin k → Fin n) (t : TarskiQueryTree n k) :
    TarskiQueryTree.run f (tarski_query_tree_bind g t) =
      TarskiQueryTree.run f (g (TarskiQueryTree.run f t)) ∧
    TarskiQueryTree.cost f (tarski_query_tree_bind g t) =
      TarskiQueryTree.cost f t +
        TarskiQueryTree.cost f (g (TarskiQueryTree.run f t)) := by
  induction t with
  | output x => exact ⟨rfl, (Nat.zero_add _).symm⟩
  | query x k' ih =>
    refine ⟨(ih (f x)).1, ?_⟩
    show TarskiQueryTree.cost f (tarski_query_tree_bind g (k' (f x))) + 1 =
      (TarskiQueryTree.cost f (k' (f x)) + 1) +
        TarskiQueryTree.cost f (g (TarskiQueryTree.run f (k' (f x))))
    rw [(ih (f x)).2]
    omega
