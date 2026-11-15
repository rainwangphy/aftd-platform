import AFTD.Prelude

/-!
# op75_compact_map

Topic: np_completeness   Node: 9c146e38cc4b

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

The compact piecewise-affine map x ↦ min(1, 4x, |4x−3|) used in the one-pass reduction.
-/

def op75_compact_map (x : ℝ) : ℝ := min 1 (min (4*x) |4*x-3|)
