import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiBoxQueryLeSmall

/-!
# tarski_box_query_le_zero_dim

Topic: algorithms   Node: 676476e6b050

Provenance: helper lemma. step towards tarski_box_query_le_five_log_sq

Dimension zero is free: in dimension 0 (the one-point box) one query suffices, for every n and every box.
-/

/-- Base of every dimension ladder for the box invariant, stated for all n (no NeZero needed, unlike tarski_box_query_le_small). -/
theorem tarski_box_query_le_zero_dim (n : ℕ) : tarski_box_query_le n 0 1 := by
  intro a b hab
  refine ⟨TarskiQueryTree.output a, ?_⟩
  intro f _ _ _
  exact ⟨le_rfl, hab, Subsingleton.elim _ _, Nat.zero_le 1⟩
