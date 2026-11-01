import AFTD.Prelude

/-!
# cyclic_cubic_distinct_neighbors

Topic: quantum   Node: 4ce364646fb6

Provenance: helper lemma. step towards cyclic_cubic_parity_repr_eval_zero

For n ≥ 6 and any x : Fin n, the cyclic neighbors (x - 1) % n and (x + 1) % n are distinct.
-/

/-- For n ≥ 6 and any x : Fin n, the cyclic neighbors (x - 1) % n and (x + 1) % n are distinct. -/
theorem cyclic_cubic_distinct_neighbors (n : ℕ) (hn : 6 ≤ n) (x : Fin n) : (⟨(x.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) ≠ ⟨(x.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
  intro h
  have hval := Fin.mk.inj h
  rcases x with ⟨x, hx⟩
  dsimp at hval
  rcases x with _ | x
  · have h1 : (0 + n - 1) % n = n - 1 := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have h2 : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  · have h1 : (x + 1 + n - 1) % n = x % n := by
      have : x + 1 + n - 1 = x + n := by omega
      rw [this, Nat.add_mod_right]
    have h2 : x % n = x := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2] at hval
    by_cases hlt : x + 1 + 1 < n
    · have h3 : (x + 1 + 1) % n = x + 2 := Nat.mod_eq_of_lt hlt
      omega
    · have h3 : x + 1 + 1 = n := by omega
      have h4 : (x + 1 + 1) % n = 0 := by rw [h3, Nat.mod_self]
      omega
