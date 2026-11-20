import AFTD.Prelude

/-!
# op874_distance_parity_succ_ne

Topic: graphs   Node: 44a48b53516d

Provenance: helper lemma. Parity alternates between consecutive natural distances.

Consecutive natural numbers have opposite parity.
-/

theorem op874_distance_parity_succ_ne (n : ℕ) : decide ((n+1)%2=0) ≠ decide (n%2=0) := by
  by_cases h : n % 2 = 0
  · have h' : (n+1)%2 ≠ 0 := by omega
    simp [h, h']
  · have h' : (n+1)%2 = 0 := by omega
    simp [h, h']
