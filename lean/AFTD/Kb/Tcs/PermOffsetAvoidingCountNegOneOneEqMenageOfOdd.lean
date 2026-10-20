import AFTD.Prelude
import AFTD.Kb.Tcs.PermOffsetAvoidingCount
import AFTD.Kb.Tcs.PermOffsetAvoidingCountEqOfBoardEquiv
import AFTD.Kb.Tcs.ZmodMulUnitHalfEqZeroIff

/-!
# perm_offset_avoiding_count_neg_one_one_eq_menage_of_odd

Topic: combinatorics   Node: 64fe16449067

Provenance: formalization of a published result. Source: arXiv:2610.23958 (Unranking S-avoiding permutations with two forbidden offsets), Proposition 6.2

For odd n >= 3 the number of permutations avoiding the offsets {-1, 1} mod n equals the menage number U(n).
-/

theorem perm_offset_avoiding_count_neg_one_one_eq_menage_of_odd (n : ℕ) (hn : 3 ≤ n)
    (ho : Odd n) :
    perm_offset_avoiding_count n {-1, 1} = perm_offset_avoiding_count n {-1, 0} := by
  obtain ⟨m, rfl⟩ := ho
  set N := 2 * m + 1 with hN
  have hu : (2 : ZMod N) * ((m : ZMod N) + 1) = 1 := by
    have : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
    rw [hN] at this; push_cast at this
    linear_combination this
  have h2m : (2 : ZMod N) * (m : ZMod N) = -1 := by linear_combination hu
  have hcast : ∀ a b : ℕ, (((a : ZMod N) = b) ↔ a % N = b % N) := fun a b =>
    ZMod.natCast_eq_natCast_iff' a b N
  have inj : ∀ c : ℕ, (∀ a b : ℕ, a < N → b < N →
      ((a : ZMod N) + c) * ((m : ZMod N) + 1) = ((b : ZMod N) + c) * ((m : ZMod N) + 1) → a = b) := by
    intro c a b ha hb hab
    have h1 : ((a : ZMod N) + c - (b + c)) * ((m : ZMod N) + 1) = 0 := by
      rw [sub_mul, hab, sub_self]
    rw [zmod_mul_unit_half_eq_zero_iff hu, sub_eq_zero, add_left_inj] at h1
    rw [hcast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    exact h1
  have hNpos : 0 < N := by omega
  -- σ i = i (m + 1), ρ j = (j + 2m) (m + 1), mod N
  let fσ : Fin N → Fin N := fun i => ⟨(i.val * (m + 1)) % N, Nat.mod_lt _ hNpos⟩
  let fρ : Fin N → Fin N := fun j => ⟨((j.val + 2 * m) * (m + 1)) % N, Nat.mod_lt _ hNpos⟩
  have vσ : ∀ i, (((fσ i : ℕ) : ZMod N)) = ((i : ℕ) : ZMod N) * ((m : ZMod N) + 1) := by
    intro i; simp [fσ, ZMod.natCast_mod]
  have vρ : ∀ j, (((fρ j : ℕ) : ZMod N)) =
      (((j : ℕ) : ZMod N) + 2 * (m : ZMod N)) * ((m : ZMod N) + 1) := by
    intro j; simp [fρ, ZMod.natCast_mod]
  have injσ : Function.Injective fσ := by
    intro a b hab
    have := congrArg (fun x : Fin N => ((x : ℕ) : ZMod N)) hab
    simp only [vσ] at this
    exact Fin.ext (inj 0 a b a.isLt b.isLt (by simpa using this))
  have injρ : Function.Injective fρ := by
    intro a b hab
    have := congrArg (fun x : Fin N => ((x : ℕ) : ZMod N)) hab
    simp only [vρ] at this
    exact Fin.ext (inj (2 * m) a b a.isLt b.isLt (by push_cast; exact this))
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective fσ (Finite.injective_iff_bijective.mp injσ)
  let ρ : Equiv.Perm (Fin N) := Equiv.ofBijective fρ (Finite.injective_iff_bijective.mp injρ)
  apply perm_offset_avoiding_count_eq_of_board_equiv N _ _ σ ρ
  intro i j
  have dv : ∀ x : ℤ, (N : ℤ) ∣ x ↔ (x : ZMod N) = 0 := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x N).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, dv,
    Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_zero]
  simp only [σ, ρ, Equiv.ofBijective_apply]
  rw [vσ, vρ]
  have e1 : ∀ J I : ZMod N, (J + 2 * (m : ZMod N)) * ((m : ZMod N) + 1) - I * ((m : ZMod N) + 1) - -1
      = (J - I + 1) * ((m : ZMod N) + 1) := fun J I => by
    linear_combination ((m : ZMod N) + 1) * h2m - hu
  have e2 : ∀ J I : ZMod N, (J + 2 * (m : ZMod N)) * ((m : ZMod N) + 1) - I * ((m : ZMod N) + 1) - 0
      = (J - I - 1) * ((m : ZMod N) + 1) := fun J I => by
    linear_combination ((m : ZMod N) + 1) * h2m
  rw [e1, e2, zmod_mul_unit_half_eq_zero_iff hu, zmod_mul_unit_half_eq_zero_iff hu]
  constructor
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h
  · rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h
