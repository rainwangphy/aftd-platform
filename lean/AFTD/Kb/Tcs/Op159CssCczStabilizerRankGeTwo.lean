import AFTD.Prelude
import AFTD.Kb.Tcs.CssQuasiTransversalCczCode
import AFTD.Kb.Tcs.Op159CssCczNoCodeSZero
import AFTD.Kb.Tcs.Op159CssCczNoCodeSOne

/-!
# op_159_css_ccz_stabilizer_rank_ge_two

Topic: quantum   Node: 878d2f707078

Provenance: original. Related work: arXiv:2610.09341 Prop. 4.3

For any block length n, if a 3 by n logical matrix K and an s by n stabilizer matrix S over ZMod 2 form a CSS quasi-transversal CCZ code, then the stabilizer rank s is at least 2.
-/

/-- Any CSS code of block length n with 3 logical qubits, Z-distance at least 3, and quasi-transversal CCZ must have stabilizer rank s at least 2. -/
theorem op_159_css_ccz_stabilizer_rank_ge_two (n s : ℕ)
    (K : Matrix (Fin 3) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2))
    (h : css_quasi_transversal_ccz_code n s K S) : 2 ≤ s := by
  by_contra hlt
  have hs : s < 2 := by omega
  interval_cases s
  · exact op_159_css_ccz_no_code_s_zero n K S h
  · exact op_159_css_ccz_no_code_s_one n K S h
