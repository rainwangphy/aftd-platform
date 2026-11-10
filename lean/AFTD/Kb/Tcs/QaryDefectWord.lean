import AFTD.Prelude
import AFTD.Kb.Tcs.QaryDefectSeq

/-!
# qary_defect_word

Topic: information   Node: 7234667d2c07

Provenance: formalization of a published result. Source: knowledgebase

For alphabet size q ≥ 2, block spacing B, and length n, qary_defect_word q B n hq is the word of length n over Fin q obtained by restricting the defect sequence qary_defect_seq q B hq to indices less than n.
-/

/-- The deterministic defect word of length n over Fin q with block period B. -/
def qary_defect_word (q B n : ℕ) (hq : 2 ≤ q) : Fin n → Fin q := fun i => qary_defect_seq q B hq i.1
