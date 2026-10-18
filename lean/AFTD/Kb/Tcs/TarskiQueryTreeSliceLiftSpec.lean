import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiQueryTreeSliceLift
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeRun

/-!
# tarski_query_tree_slice_lift_spec

Topic: algorithms   Node: bc1905b853d3

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Run/cost law for the slice lift: in dimension k+1, the lifted tree computes insertNth i c of the slice algorithm's output (run against the sliced map y ↦ f (insertNth i c y) ∘ succAbove i), and it costs exactly what the slice algorithm costs.
-/

/-- Run and cost of a slice lift. -/
theorem tarski_query_tree_slice_lift_spec {n k : ℕ} (i : Fin (k+1)) (c : Fin n)
    (f : (Fin (k+1) → Fin n) → Fin (k+1) → Fin n) (t : TarskiQueryTree n k) :
    TarskiQueryTree.run f (tarski_query_tree_slice_lift i c t) =
      Fin.insertNth i c (TarskiQueryTree.run (fun y j => f (Fin.insertNth i c y) (i.succAbove j)) t) ∧
    TarskiQueryTree.cost f (tarski_query_tree_slice_lift i c t) =
      TarskiQueryTree.cost (fun y j => f (Fin.insertNth i c y) (i.succAbove j)) t := by
  induction t with
  | output x =>
    simp [tarski_query_tree_slice_lift, TarskiQueryTree.run, TarskiQueryTree.cost]
  | query x next ih =>
    simp only [tarski_query_tree_slice_lift, TarskiQueryTree.run, TarskiQueryTree.cost]
    have := ih (fun j => f (i.insertNth c x) (i.succAbove j))
    exact ⟨this.1, congrArg (· + 1) this.2⟩
