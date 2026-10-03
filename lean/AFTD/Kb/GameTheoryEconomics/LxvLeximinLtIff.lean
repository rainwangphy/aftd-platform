import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.GameTheoryEconomics.LeximinProfile
import AFTD.Kb.GameTheoryEconomics.LeximinLt
import AFTD.Kb.GameTheoryEconomics.ListLexMapIffOfStrictMono
import AFTD.Kb.GameTheoryEconomics.LxvProfile
import AFTD.Kb.GameTheoryEconomics.LxvInstance
import AFTD.Kb.GameTheoryEconomics.LxvGoodsUtility

/-!
# lxv_leximin_lt_iff

Topic: fair_division   Node: 354cfa209e2e

In the instance, the real leximin comparison is equivalent to the lexicographic comparison of integer profiles.
-/

lemma lxv_leximin_lt_iff (a b : Fin 6 → Fin 4) :
    leximin_lt (goods_utility lxv_instance a) (goods_utility lxv_instance b) ↔
      List.Lex (· < ·) (lxv_profile a) (lxv_profile b) := by
  have hf : StrictMono fun k : ℕ => (k : ℝ) / 20 := fun x y h =>
    div_lt_div_of_pos_right (Nat.cast_lt.2 h) (by norm_num)
  have hprof : ∀ c : Fin 6 → Fin 4, leximin_profile (goods_utility lxv_instance c) =
      (lxv_profile c).map fun k : ℕ => (k : ℝ) / 20 := by
    intro c
    rw [lxv_goods_utility, leximin_profile, lxv_profile,
      List.map_insertionSort (r := (· ≤ ·)) (s := (· ≤ ·))]
    · rw [List.map_ofFn]; rfl
    · intro x _ y _; exact hf.le_iff_le.symm
  rw [leximin_lt, hprof, hprof]
  exact list_lex_map_iff_of_strictMono hf _ _
