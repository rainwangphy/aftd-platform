import AFTD.Prelude

/-!
# cycle_power_class_overlap_two_steps

Topic: combinatorics   Node: 8bf614e5f842

Provenance: helper lemma. Uniform local base case for the endpoint-overlap route of OP-205 / RT-1, arXiv:2610.15635. This is an elementary consequence of the tight-model conditions, not a research advance.

At every radius at least four, an old class containing its first neighbour intersects the class two starts later, at the new root or at the old endpoint, provided the distance-D-2 exact balance and distance-D-3 coverage hold.
-/

theorem cycle_power_class_overlap_two_steps
    (D : ℕ) (hD : 4 ≤ D) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (x v (D - 2)).toNat + (x (v - 1) 1).toNat = 1)
    (hcover : ∀ v : ℤ, ∃ a : ℕ, a < 3 ∧ x (v - (a : ℤ)) a = true ∧
      x (v - (a : ℤ)) (a + D - 3) = true) :
    ∀ p : ℤ, x p 1 = true → x p 2 = true ∨ x (p + 2) (D - 3) = true := by
  intro p hp
  rcases hcover (p + 2) with ⟨a, ha, h1, h2⟩
  interval_cases a
  · right
    have : (p + 2 - (0 : ℤ)) = p + 2 := by ring
    have hD' : 0 + D - 3 = D - 3 := by omega
    change x (p + 2 - 0) (0 + D - 3) = true at h2
    rw [this, hD'] at h2
    exact h2
  · exfalso
    have hidx : p + 2 - (1 : ℤ) = p + 1 := by ring
    have hD' : 1 + D - 3 = D - 2 := by omega
    change x (p + 2 - 1) (1 + D - 3) = true at h2
    rw [hidx, hD'] at h2
    have hex := hexact (p + 1)
    have hidx2 : p + 1 - 1 = p := by ring
    rw [hidx2, hp, h2] at hex
    revert hex
    decide
  · left
    have : p + 2 - (2 : ℤ) = p := by ring
    change x (p + 2 - 2) 2 = true at h1
    rw [this] at h1
    exact h1
