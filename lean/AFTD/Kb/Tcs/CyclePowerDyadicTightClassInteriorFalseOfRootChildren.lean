import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_tight_class_interior_false_of_root_children

Topic: combinatorics   Node: bc6f65e2a608

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Reduces the first conclusion of cycle_power_dyadic_regular_continuation_right to the offsets 2^j - 1 and D - 2^j of the class at p0+1.

Tree structure of tight dyadic classes. Let m ≥ 2 and D = 2^m. A class b ⊆ [0, D) of tight dyadic weight (cycle_power_dyadic_class_weight m b = |b|) that contains none of the offsets 2^j - 1 and D - 2^j for 1 ≤ j < m contains no offset strictly between 0 and D - 1. (These offsets are the children of the endpoints in the parent forest of tight classes: every other offset has a parent at strictly smaller distance from the nearer end.)
-/

theorem cycle_power_dyadic_tight_class_interior_false_of_root_children (m : ℕ) (hm : 2 ≤ m)
    (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m b =
      (Finset.range (2^m)).sum (fun a => (b a).toNat))
    (hlow : ∀ j, 1 ≤ j → j < m → b (2^j - 1) = false)
    (hhigh : ∀ j, 1 ≤ j → j < m → b (2^m - 2^j) = false) :
    ∀ a, 0 < a → a < 2^m - 1 → b a = false := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 1 := ⟨m - 1, by omega⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2^s := ⟨_, rfl⟩
  have hD : (2:ℕ)^(s+1) = 2*T := by rw [hT, pow_succ]; ring
  have hlog : ∀ c : ℕ, 0 < c → c < T → ∃ j Q, 1 ≤ j ∧ j < s + 1 ∧ Q = 2^(j-1) ∧
      2^j = 2*Q ∧ Q ≤ c ∧ c < 2*Q := by
    intro c hc0 hcT
    refine ⟨Nat.log 2 c + 1, 2^(Nat.log 2 c), by omega, ?_, by simp, by rw [pow_succ]; ring,
      Nat.pow_log_le_self 2 (by omega), ?_⟩
    · by_contra hcon
      have : 2^s ≤ 2^(Nat.log 2 c) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.pow_log_le_self 2 (show c ≠ 0 by omega)
      omega
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) c
      rw [pow_succ] at this; omega
  have key : ∀ n : ℕ, ∀ a, 0 < a → a < 2^(s+1) - 1 → min a (2^(s+1) - 1 - a) ≤ n → b a = false := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha0 ha1 hmu
      by_contra hne
      have hb : b a = true := by revert hne; generalize b a = w; cases w <;> simp
      rcases lt_or_ge a T with haT | haT
      · obtain ⟨j, Q, hj1, hjm, hQ, hPQ, hQa, haQ⟩ := hlog a ha0 haT
        have hp := (cycle_power_dyadic_tight_class_parent (s+1) j hj1 hjm b htight a
          (by omega)).2 (by rw [← hQ]; omega) hb
        by_cases hroot : a = 2^j - 1
        · rw [hroot, hlow j hj1 hjm] at hb; exact absurd hb (by decide)
        · have hjT : 2^j ≤ 2^(s+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have := ih (min (a + 2^(s+1) - 2^j) (2^(s+1) - 1 - (a + 2^(s+1) - 2^j)))
            (by omega) (a + 2^(s+1) - 2^j) (by omega) (by omega) le_rfl
          rw [hp] at this; exact absurd this (by decide)
      · have hh0 : 0 < 2^(s+1) - 1 - a := by omega
        obtain ⟨j, Q, hj1, hjm, hQ, hPQ, hQa, haQ⟩ := hlog (2^(s+1) - 1 - a) hh0 (by omega)
        have hjT : 2^j ≤ 2^(s+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hp := (cycle_power_dyadic_tight_class_parent (s+1) j hj1 hjm b htight
          (2^j - 1 - (2^(s+1) - 1 - a)) (by omega)).1 (by rw [← hQ]; omega)
        have hidx : 2^j - 1 - (2^(s+1) - 1 - a) + 2^(s+1) - 2^j = a := by omega
        rw [hidx] at hp
        have hb' := hp hb
        by_cases hroot : a = 2^(s+1) - 2^j
        · rw [hroot, hhigh j hj1 hjm] at hb; exact absurd hb (by decide)
        · have := ih (min (2^j - 1 - (2^(s+1) - 1 - a))
              (2^(s+1) - 1 - (2^j - 1 - (2^(s+1) - 1 - a))))
            (by omega) (2^j - 1 - (2^(s+1) - 1 - a)) (by omega) (by omega) le_rfl
          rw [hb'] at this; exact absurd this (by decide)
  intro a ha0 ha1
  exact key _ a ha0 ha1 le_rfl
