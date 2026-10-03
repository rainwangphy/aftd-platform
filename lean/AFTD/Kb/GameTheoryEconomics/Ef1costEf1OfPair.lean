import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costBundleIte
import AFTD.Kb.GameTheoryEconomics.Ef1costFinTwoCases
import AFTD.Kb.GameTheoryEconomics.Ef1costPairOk
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores

/-!
# ef1cost_ef1_of_pair

Topic: fair_division   Node: cd702b47075a

Bridging: an EF1 two-bundle split gives an EF1 allocation in the sense of `is_ef1_chores`.
-/

/-- Bridging: an EF1 two-bundle split gives an EF1 allocation in the sense of `is_ef1_chores`. -/
lemma ef1cost_ef1_of_pair {m : ℕ} (c : Fin 2 → Fin m → ℝ) (p q : Fin 2) (hpq : p ≠ q)
    (Y : Finset (Fin m)) (hp : ef1cost_pair_ok (c p) Y Yᶜ) (hq : ef1cost_pair_ok (c q) Yᶜ Y) :
    is_ef1_chores c (fun j => if j ∈ Y then p else q) := by
  obtain ⟨hbp, hbq⟩ := ef1cost_bundle_ite p q hpq Y
  intro i j
  by_cases hij : i = j
  · subst hij
    left
    exact le_refl _
  rcases ef1cost_fin_two_cases p q hpq i with hi | hi <;>
    rcases ef1cost_fin_two_cases p q hpq j with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · rw [hi, hj, hbp, hbq]; exact hp
  · rw [hi, hj, hbp, hbq]; exact hq
  · exact absurd (hi.trans hj.symm) hij
