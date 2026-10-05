import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxAlphaTEFX
import AFTD.Kb.GameTheoryEconomics.TfxVal
import AFTD.Kb.GameTheoryEconomics.TfxRound1
import AFTD.Kb.GameTheoryEconomics.TfxRound2A
import AFTD.Kb.GameTheoryEconomics.TfxRound2B
import AFTD.Kb.GameTheoryEconomics.TfxRound31
import AFTD.Kb.GameTheoryEconomics.TfxRound32
import AFTD.Kb.GameTheoryEconomics.TfxRound33
import AFTD.Kb.GameTheoryEconomics.TfxRound34

/-!
# tfx_core

Topic: fair_division   Node: 4c44438c089f

Core case analysis: with three rounds of the goods {z, a, b} (values 0, 1, x), no allocation (given by its nine entries) is α-TEFX as soon as α x > 2, 2αx > x + 2 and α(x + 2) > x.
-/

/-- Core case analysis: with three rounds of the goods `{z, a, b}` (values `0, 1, x`), no allocation (given by its nine entries) is `α`-TEFX as soon as `α x > 2`, `2αx > x + 2` and `α(x + 2) > x`. -/
theorem tfx_core (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x)
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Fin 2)
    (h : tfx_alphaTEFX α (tfx_val x) (![![a00, a01, a02], ![a10, a11, a12], ![a20, a21, a22]] : Fin 3 → Fin 3 → Fin 2)) :
    False := by
  have d0 := h 0 (by norm_num)
  have d1 := h 1 (by norm_num)
  have d2 := h 2 (by norm_num)
  rcases tfx_round1 α x hα0 hx0 h1 h2 h3 _ _ _ _ _ _ _ _ _ d0 with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases tfx_round2A α x hα0 hx0 h1 h2 h3 _ _ _ _ _ _ d1 with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact tfx_round3_1 α x hα0 hx0 h1 h2 h3 _ _ _ d2
    · exact tfx_round3_2 α x hα0 hx0 h1 h2 h3 _ _ _ d2
  · rcases tfx_round2B α x hα0 hx0 h1 h2 h3 _ _ _ _ _ _ d1 with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact tfx_round3_3 α x hα0 hx0 h1 h2 h3 _ _ _ d2
    · exact tfx_round3_4 α x hα0 hx0 h1 h2 h3 _ _ _ d2
