import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseLeftmost

/-!
# fse_leftmost_le

Topic: mechanism_design   Node: 895733d5ccfc

The leftmost location is at most every agent's location.
-/

open Finset in
/-- The leftmost location is at most every agent's location. -/
lemma fse_leftmost_le {n : ℕ} [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    fse_leftmost x ≤ x i :=
  Finset.inf'_le _ (Finset.mem_univ i)
