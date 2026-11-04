import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# schur_two_upper_bound

Topic: combinatorics   Node: 8f6233a8262e

Provenance: helper lemma. arXiv:2611.01714 Proposition 3.1

For every integer k ≥ 3, every 2-coloring c : Fin (k^2 + k - 1) → Fin 2 admits a monochromatic solution to (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1.
-/

private lemma schur_two_upper_bound_five_color_lemma (f : Fin 5 → Fin 2) :
    (f 0 = f 1) ∨ (f 1 = f 3) ∨
    (f 0 = f 2 ∧ f 2 = f 3) ∨
    (f 3 = f 0 ∧ f 0 = f 4) ∨
    (f 1 = f 2 ∧ f 2 = f 4) := by
  revert f
  decide

/-- For every integer k ≥ 3, every 2-coloring of Fin (k^2 + k - 1) admits a monochromatic solution to (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1. -/
theorem schur_two_upper_bound (k : ℕ) (hk : 3 ≤ k) (c : Fin (k^2 + k - 1) → Fin 2) :
    ∃ x y z : Fin (k^2 + k - 1), c x = c y ∧ c y = c z ∧
      (x.val + 1) + (k - 1) * (y.val + 1) = z.val + 1 := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hsqpos : 0 < k ^ 2 := pow_pos hkpos 2
  have hsqge : k ≤ k ^ 2 := le_self_pow hk1 (by norm_num : (2:ℕ) ≠ 0)
  let p0 : Fin (k ^ 2 + k - 1) := ⟨0, by omega⟩
  let p1 : Fin (k ^ 2 + k - 1) := ⟨k - 1, by omega⟩
  let p2 : Fin (k ^ 2 + k - 1) := ⟨k, by omega⟩
  let p3 : Fin (k ^ 2 + k - 1) := ⟨k ^ 2 - 1, by omega⟩
  let p4 : Fin (k ^ 2 + k - 1) := ⟨k ^ 2 + k - 2, by omega⟩
  have h1 : k - 1 + 1 = k := by omega
  have hsq1 : k ^ 2 - 1 + 1 = k ^ 2 := by omega
  have hlast : k ^ 2 + k - 2 + 1 = k ^ 2 + k - 1 := by omega
  have e1 : (p0.val + 1) + (k - 1) * (p0.val + 1) = p1.val + 1 := by
    simp [p0, p1]
    omega
  have e2 : (p1.val + 1) + (k - 1) * (p1.val + 1) = p3.val + 1 := by
    simp [p1, p3]
    rw [h1, hsq1]
    nlinarith [hk]
  have e3 : (p0.val + 1) + (k - 1) * (p2.val + 1) = p3.val + 1 := by
    simp [p0, p2, p3]
    rw [hsq1]
    nlinarith [hk]
  have e4 : (p3.val + 1) + (k - 1) * (p0.val + 1) = p4.val + 1 := by
    simp [p0, p3, p4]
    rw [hsq1, hlast]
    omega
  have e5 : (p1.val + 1) + (k - 1) * (p2.val + 1) = p4.val + 1 := by
    simp [p1, p2, p4]
    rw [h1, hlast]
    nlinarith [hk]
  have hfive : (c p0 = c p1) ∨ (c p1 = c p3) ∨
      (c p0 = c p2 ∧ c p2 = c p3) ∨
      (c p3 = c p0 ∧ c p0 = c p4) ∨
      (c p1 = c p2 ∧ c p2 = c p4) := by
    have h := schur_two_upper_bound_five_color_lemma
      (fun i : Fin 5 => c (![p0, p1, p2, p3, p4] i))
    simpa using h
  rcases hfive with h | h | h | h | h
  · exact ⟨p0, p0, p1, rfl, h, e1⟩
  · exact ⟨p1, p1, p3, rfl, h, e2⟩
  · exact ⟨p0, p2, p3, h.1, h.2, e3⟩
  · exact ⟨p3, p0, p4, h.1, h.2, e4⟩
  · exact ⟨p1, p2, p4, h.1, h.2, e5⟩
