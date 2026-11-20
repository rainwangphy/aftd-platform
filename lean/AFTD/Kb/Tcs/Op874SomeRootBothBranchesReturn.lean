import AFTD.Prelude
import AFTD.Kb.Tcs.Op874ExistsNonarticulationSuccessor
import AFTD.Kb.Tcs.Op874NonarticulationSuccessorReturnsBothBranches

/-!
# op874_some_root_both_branches_return

Topic: graphs   Node: f2bf405f9ac4

Provenance: helper lemma. Non-articulation successor selection and balanced-cut return lemma.

In every nonempty finite strongly connected loopless two-in/two-out directed multigraph, some root has a successor whose two branches can return to the root without that successor. No no-even assumption is needed.
-/

theorem op874_some_root_both_branches_return {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (p q : Equiv.Perm X) (hfixed : ∀ x, p x ≠ x ∧ q x ≠ x) (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v) : ∃ r x : X, (p r = x ∨ q r = x) ∧ Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (p x) r ∧ Relation.ReflTransGen (fun u v => u ≠ x ∧ v ≠ x ∧ (p u = v ∨ q u = v)) (q x) r := by
  obtain ⟨r, x, harc, hweak⟩ := op874_exists_nonarticulation_successor p q hfixed hstrong
  exact ⟨r, x, harc, op874_nonarticulation_successor_returns_both_branches p q hfixed r x harc hweak⟩
