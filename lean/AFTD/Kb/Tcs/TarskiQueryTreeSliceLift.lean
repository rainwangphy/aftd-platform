import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTree

/-!
# tarski_query_tree_slice_lift

Topic: algorithms   Node: d124904c8166

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Slice lifting of a query tree one dimension up: replace every query y in dimension k by the query (insertNth i c y) in dimension k+1, and every returned answer v by its restriction (removeNth i v) to the other coordinates.
-/

/-- Lift a dimension-k query tree to dimension k+1 by holding coordinate i at c. -/
def tarski_query_tree_slice_lift {n k : ℕ} (i : Fin (k+1)) (c : Fin n) :
    TarskiQueryTree n k → TarskiQueryTree n (k+1) := fun _t => match _t with
  | .output x => .output (Fin.insertNth i c x)
  | .query x k' => .query (Fin.insertNth i c x)
      (fun v => tarski_query_tree_slice_lift i c (k' (Fin.removeNth i v)))
