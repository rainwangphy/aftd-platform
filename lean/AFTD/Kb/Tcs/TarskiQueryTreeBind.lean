import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# tarski_query_tree_bind

Topic: algorithms   Node: 468276861c46

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Sequential composition of query trees: run the tree, then feed its output point into the continuation g to obtain the tree that is actually executed.
-/

/-- Sequential composition: run a query tree, then continue with the tree g applied to its output. -/
def tarski_query_tree_bind {n k : ℕ} (g : (Fin k → Fin n) → TarskiQueryTree n k) :
    TarskiQueryTree n k → TarskiQueryTree n k := fun _t => match _t with
  | .output x => g x
  | .query x k' => .query x (fun v => tarski_query_tree_bind g (k' v))
