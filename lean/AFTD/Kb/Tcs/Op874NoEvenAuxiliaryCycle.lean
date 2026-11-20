import AFTD.Prelude
import AFTD.Kb.Tcs.Op874NoPartialMixedClosedSet

/-!
# op874_no_even_auxiliary_cycle

Topic: graphs   Node: 34a260459ef9

Provenance: helper lemma. Mixed-set obstruction excludes alternating even directed cycles.

The no-global-mixed-bits hypothesis excludes every nonempty simple even directed cycle.
-/

theorem op874_no_even_auxiliary_cycle {X : Type*} [Fintype X] [DecidableEq X] (p q : Equiv.Perm X) (hstrong : ∀ u v, ∃ w : List Bool, w.foldl (fun x bit => if bit then p x else q x) u = v) (hno : ∀ b : X → Bool, ∃ x, b x = b (p x) ∧ b x = b (q x)) (n : ℕ) [NeZero n] (heven : Even n) (c : Fin n → X) (hinj : Function.Injective c) (harc : ∀ i, p (c i) = c (i+1) ∨ q (c i) = c (i+1)) : False := by
  classical
  have hn : 2 ≤ n := by
    have hn0 := NeZero.ne n
    rcases heven with ⟨k, hk⟩
    omega
  let S : Finset X := Finset.univ.image c
  let bits : X → Bool := fun v => decide (∃ i : Fin n, c i = v ∧ i.val % 2 = 0)
  have hmem (i : Fin n) : c i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hbits (i : Fin n) : bits (c i) = decide (i.val % 2 = 0) := by
    have heq : (∃ j : Fin n, c j = c i ∧ j.val % 2 = 0) ↔ i.val % 2 = 0 := by
      constructor
      · rintro ⟨j, hj, hpar⟩
        have : j = i := hinj hj
        simpa [this] using hpar
      · intro hpar
        exact ⟨i, rfl, hpar⟩
    simp only [bits, heq]
  have hval (i : Fin n) : (i+1).val = if i.val + 1 < n then i.val + 1 else 0 := by
    rw [Fin.val_add]
    have hone : (1 : Fin n).val = 1 := by simp [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [hone]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have heq : i.val + 1 = n := by have := i.isLt; omega
      simp [heq]
  have hdiff (i : Fin n) : bits (c i) ≠ bits (c (i+1)) := by
    rw [hbits, hbits, hval]
    rcases heven with ⟨k, hk⟩
    split_ifs with h
    · by_cases hi : i.val % 2 = 0
      · have hj : (i.val + 1) % 2 ≠ 0 := by omega
        simp [hi, hj]
      · have hj : (i.val + 1) % 2 = 0 := by omega
        simp [hi, hj]
    · have hi : i.val % 2 ≠ 0 := by have := i.isLt; omega
      simp [hi]
  refine op874_no_partial_mixed_closed_set p q hstrong hno S ⟨c 0, hmem 0⟩ bits ?_
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  rcases harc i with hp | hq
  · left
    exact ⟨hp ▸ hmem (i+1), hp ▸ hdiff i⟩
  · right
    exact ⟨hq ▸ hmem (i+1), hq ▸ hdiff i⟩
