import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicRotateLeft

/-!
# cyclic_rotate_left_bijective

Topic: information   Node: 352db8ed496f

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any positive natural number k and any type α, cyclic_rotate_left k is a bijection on Fin k → α.
-/

/-- cyclic_rotate_left is a bijection on Fin k → α for positive k. -/
theorem cyclic_rotate_left_bijective (k : ℕ) (hk : 0 < k) (α : Type*) :
    Function.Bijective (cyclic_rotate_left (α := α) k) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun w j => w ⟨(j.val + k - 1) % k, Nat.mod_lt _ (pos_of_gt j.isLt)⟩, ?_, ?_⟩
  · intro w
    funext j
    dsimp [cyclic_rotate_left]
    congr 1
    ext
    dsimp
    have hj := j.isLt
    rcases Nat.eq_zero_or_pos j.val with hj0 | hj_pos
    · rw [hj0]
      simp only [Nat.zero_add]
      have : k - 1 < k := by omega
      rw [Nat.mod_eq_of_lt this]
      have : k - 1 + 1 = k := by omega
      rw [this, Nat.mod_self]
    · have h1 : j.val + k - 1 = (j.val - 1) + k := by omega
      rw [h1, Nat.add_mod_right]
      have h2 : j.val - 1 < k := by omega
      rw [Nat.mod_eq_of_lt h2]
      have h3 : j.val - 1 + 1 = j.val := by omega
      rw [h3, Nat.mod_eq_of_lt hj]
  · intro w
    funext j
    dsimp [cyclic_rotate_left]
    congr 1
    ext
    dsimp
    have hj := j.isLt
    rcases lt_or_ge (j.val + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]
      have : j.val + 1 + k - 1 = j.val + k := by omega
      rw [this]
      have : (j.val + k) % k = j.val % k := Nat.add_mod_right j.val k
      rw [this, Nat.mod_eq_of_lt hj]
    · have : j.val + 1 = k := by omega
      rw [this, Nat.mod_self, Nat.zero_add]
      have : k - 1 < k := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
