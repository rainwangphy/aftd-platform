import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseSurjective
import AFTD.Kb.GameTheoryEconomics.FseLeftmost
import AFTD.Kb.GameTheoryEconomics.FseLeftmostAttained

/-!
# fse_leftmost_surjective

Topic: mechanism_design   Node: 1bf37cd9a27a

The leftmost mechanism is surjective onto [0,1] (unanimous profiles).
-/

/-- The leftmost mechanism is surjective onto `[0,1]` (unanimous profiles). -/
lemma fse_leftmost_surjective {n : ℕ} [NeZero n] : fse_Surjective (fse_leftmost (n := n)) := by
  intro y hy
  refine ⟨fun _ => y, fun _ => hy, ?_⟩
  obtain ⟨j, hj⟩ := fse_leftmost_attained (fun _ : Fin n => y)
  exact hj
