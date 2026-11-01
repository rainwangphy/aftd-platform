import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxAnchorFamilyStart

/-!
# efx_anchor_family_perturbation_exists

Topic: fair_division   Node: 29511505127c

Provenance: helper lemma. Nondegenerate arbitrary-size OP-7 Pareto obstruction, binary perturbation and experiment 11514.

There are binary exponent permutations in which each original agent’s own r anchors receive higher exponents than all other anchors.
-/

def efx_anchor_family_perturbation_exists_p (r s : ℕ) (i : Fin 4) (g : ℕ) : ℕ :=
  match i with
  | 0 => if g < 7 then g else if g < 7 + r then 7 + r + r + s + (g - 7) else g - r
  | 1 => if g < 7 + r then g else if g < 7 + r + r then 7 + r + r + s + (g - (7 + r)) else g - r
  | 2 => if g < 7 + r + r then g else if g < 7 + r + r + r then 7 + r + r + s + (g - (7 + r + r)) else g - r
  | 3 => g

lemma efx_anchor_family_perturbation_exists_start_anchor (r s : ℕ) (a : Fin (r+r+r)) :
    efx_anchor_family_start r s (Fin.castAdd s (Fin.natAdd 7 a)) =
      if (a : ℕ) < r then 0 else if (a : ℕ) < r+r then 1 else 2 := by
  dsimp [efx_anchor_family_start]
  rw [Fin.addCases_left, Fin.addCases_right]

theorem efx_anchor_family_perturbation_exists (r s : ℕ) (hr : 0 < r) (hs : 2 ≤ s) :
  ∃ p : Fin 4 → Fin ((7+(r+r+r))+s) → ℕ,
    (∀ i, Function.Injective (p i)) ∧
    (∀ i g, p i g < (7+(r+r+r))+s) ∧
    (∀ (i : Fin 3) (a b : Fin (r+r+r)),
      efx_anchor_family_start r s (Fin.castAdd s (Fin.natAdd 7 a)) = i.castSucc.castSucc →
      efx_anchor_family_start r s (Fin.castAdd s (Fin.natAdd 7 b)) ≠ i.castSucc.castSucc →
      p i.castSucc (Fin.castAdd s (Fin.natAdd 7 b)) < p i.castSucc (Fin.castAdd s (Fin.natAdd 7 a))) := by
  refine ⟨fun i g => efx_anchor_family_perturbation_exists_p r s i g, ?_, ?_, ?_⟩
  · intro i ⟨x, hx⟩ ⟨y, hy⟩ h
    apply Fin.ext
    fin_cases i
    · dsimp [efx_anchor_family_perturbation_exists_p] at h ⊢; split_ifs at h <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p] at h ⊢; split_ifs at h <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p] at h ⊢; split_ifs at h <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p] at h ⊢; exact h
  · intro i ⟨g, hg⟩
    fin_cases i
    · dsimp [efx_anchor_family_perturbation_exists_p]; split_ifs <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p]; split_ifs <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p]; split_ifs <;> omega
    · dsimp [efx_anchor_family_perturbation_exists_p]; omega
  · intro i a b ha hb
    rw [efx_anchor_family_perturbation_exists_start_anchor] at ha hb
    have h_a_lt := a.isLt
    have h_b_lt := b.isLt
    fin_cases i
    · dsimp at ha hb
      dsimp [efx_anchor_family_perturbation_exists_p]
      split_ifs at ha hb ⊢ <;> omega
    · dsimp at ha hb
      dsimp [efx_anchor_family_perturbation_exists_p]
      split_ifs at ha hb ⊢ <;> omega
    · dsimp at ha hb
      dsimp [efx_anchor_family_perturbation_exists_p]
      split_ifs at ha hb ⊢ <;> omega
