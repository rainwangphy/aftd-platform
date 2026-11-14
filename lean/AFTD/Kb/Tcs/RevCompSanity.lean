import AFTD.Prelude
import AFTD.Kb.Tcs.RevComp

/-!
# rev_comp_sanity

Topic: approximation   Node: ec01b382f664

Provenance: helper lemma. Sanity check of rev_comp (arXiv:2611.16573)

The reverse complement of 011 under n ↦ 3 − n is 223.
-/

theorem rev_comp_sanity : rev_comp (fun n : ℕ => 3 - n) [0, 1, 1] = [2, 2, 3] := by decide
