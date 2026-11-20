import AFTD.Prelude

/-!
# op874_palette_state_cycle_gives_four_windows

Topic: graphs   Node: 323a053855c0

Provenance: helper lemma. State-to-cycle transfer for the OP-874 separated-defect automaton.

If a cyclic sequence of four-color permutations shifts its first three positions consistently and each specified fourth window color is the missing fourth permutation value, then its first positions form a square-proper edge word with those windows using all four colors.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_palette_state_cycle_gives_four_windows
    (n : ℕ) [NeZero n] (hn : 6 ≤ n) (Q : Finset (Fin n))
    (s : Fin n → Equiv.Perm (Fin 4))
    (hadvance : ∀ i, s (i+1) 0 = s i 1 ∧ s (i+1) 1 = s i 2)
    (hforce : ∀ q ∈ Q, s (q+1) 0 = s (q-2) 3) :
    ∃ c : Fin n → Fin 4,
      (∀ i, c i ≠ c (i+1) ∧ c i ≠ c (i+2)) ∧
      (∀ q ∈ Q, [c (q-2), c (q-1), c q, c (q+1)].Nodup) := by
  have hone : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  have htwo : (2 : Fin n).val = 2 := by
    change 2 % n = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    simp only [Fin.val_add, hone, htwo]
    exact Nat.mod_eq_of_lt (by omega)
  let c : Fin n → Fin 4 := fun i => s i 0
  have cnext (i : Fin n) : c (i+1) = s i 1 := (hadvance i).1
  have cnext2 (i : Fin n) : c (i+2) = s i 2 := by
    calc
      c (i+2) = s (i+1) 1 := by
        simpa [add_assoc, hsum] using cnext (i+1)
      _ = s i 2 := (hadvance i).2
  have inj01 (i : Fin n) : s i 0 ≠ s i 1 := by
    intro h
    have hh := (s i).injective h
    have hv := congrArg Fin.val hh
    norm_num at hv
  have inj02 (i : Fin n) : s i 0 ≠ s i 2 := by
    intro h
    have hh := (s i).injective h
    have hv := congrArg Fin.val hh
    norm_num at hv
  refine ⟨c, ?_, ?_⟩
  · intro i
    constructor
    · simpa [c, cnext] using inj01 i
    · simpa [c, cnext2] using inj02 i
  · intro q hq
    have h1 : c (q-1) = s (q-2) 1 := by
      have h := cnext (q-2)
      have he : q-2+1 = q-1 := by
        rw [← hsum]
        abel
      simpa [he] using h
    have h2 : c q = s (q-2) 2 := by
      have h := cnext2 (q-2)
      have he : q-2+2 = q := by abel
      simpa [he] using h
    have h3 : c (q+1) = s (q-2) 3 := hforce q hq
    rw [show c (q-2) = s (q-2) 0 from rfl, h1, h2, h3]
    have hnodup : (([0, 1, 2, 3] : List (Fin 4)).map (s (q-2))).Nodup :=
      List.Nodup.map (s (q-2)).injective (by decide)
    simpa using hnodup
