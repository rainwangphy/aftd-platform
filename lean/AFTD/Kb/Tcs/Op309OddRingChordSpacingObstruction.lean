import AFTD.Prelude

/-!
# op309_odd_ring_chord_spacing_obstruction

Topic: graphs   Node: bd2b6d5251a1

Provenance: helper lemma. New parity obstruction to the chord-spacing route from https://arxiv.org/abs/2611.24297, supported by experiments 34618, 34620 and 34623.

In every odd cyclic ring of the displayed ten-position chord pattern, each chord is given one of two colors. Some two cycle edges at cyclic distance two have equally colored endpoint chords. This gives an infinite combinatorial obstruction to imposing the chord-spacing condition on all prescribed Hamiltonian cycles.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

open Fin.NatCast

def op309_ring_block_spacing_ok (f : Fin 5 → Bool) : Prop :=
  ¬ (f 0 = f 1 ∧ f 2 = f 0) ∧
  ¬ (f 1 = f 2 ∧ f 0 = f 3) ∧
  ¬ (f 2 = f 0 ∧ f 3 = f 1) ∧
  ¬ (f 0 = f 3 ∧ f 1 = f 4) ∧
  ¬ (f 3 = f 1 ∧ f 4 = f 2) ∧
  ¬ (f 1 = f 4 ∧ f 2 = f 3) ∧
  ¬ (f 4 = f 2 ∧ f 3 = f 4)

theorem op309_ring_block_spacing_structure : ∀ f : Fin 5 → Bool, op309_ring_block_spacing_ok f →
    f 0 = f 4 ∧ f 2 = f 3 := by
  unfold op309_ring_block_spacing_ok
  decide

theorem op309_ring_odd_boolean_alternation (n : ℕ) [NeZero n] (hodd : n % 2 = 1)
    (x : Fin n → Bool) : ¬ (∀ i, x i ≠ x (i+1)) := by
  intro h
  have hn : 0 < n := by omega
  let y (k : ℕ) : Bool := x (k : Fin n)
  have hstep (k : ℕ) : y (k+1) = !y k := by
    have hk := h (k : Fin n)
    have hk' : y k ≠ y (k+1) := by simpa [y] using hk
    cases hy : y k <;> cases hz : y (k+1) <;> simp_all
  have halt (k : ℕ) : y k = if k % 2 = 0 then y 0 else !y 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [hstep, ih]
        by_cases he : k % 2 = 0
        · have hs : (k+1) % 2 = 1 := by omega
          simp [he, hs]
        · have hs : (k+1) % 2 = 0 := by omega
          simp [he, hs]
  have hperiod : y n = y 0 := by simp [y]
  have hy := halt n
  simp [hodd] at hy
  rw [hperiod] at hy
  cases hzero : y 0 <;> simp [hzero] at hy

theorem op309_ring_odd_block_obstruction
    (n : ℕ) [NeZero n] (hodd : n % 2 = 1) (b : Fin n → Fin 5 → Bool) :
    (∃ i, ¬ op309_ring_block_spacing_ok (b i)) ∨
    (∃ i, b i 2 = b i 3 ∧ b i 4 = b (i+1) 0) := by
  classical
  by_contra h
  push_neg at h
  have he : ∀ i, b i 0 ≠ b (i+1) 0 := by
    intro i hh
    have hs := op309_ring_block_spacing_structure (b i) (h.1 i)
    exact h.2 i hs.2 (hs.1.symm.trans hh)
  exact op309_ring_odd_boolean_alternation n hodd (fun i => b i 0) he

def op309_ring_chord_word : Fin 10 → Fin 5 := ![0,1,2,0,3,1,4,2,3,4]

def op309_ring_bad_cycle_edge {n : ℕ} [NeZero n] (b : Fin n → Fin 5 → Bool) (i : Fin n) (j : Fin 10) : Prop :=
  if j.val = 9 then b i 4 = b (i+1) 0
  else b i (op309_ring_chord_word j) = b i (op309_ring_chord_word (j+1))

theorem op309_odd_ring_chord_spacing_obstruction
    (n : ℕ) [NeZero n] (hodd : n % 2 = 1) (b : Fin n → Fin 5 → Bool) :
    ∃ (i : Fin n) (j : Fin 8),
      op309_ring_bad_cycle_edge b i ⟨j.val, by omega⟩ ∧
      op309_ring_bad_cycle_edge b i ⟨j.val+2, by omega⟩ := by
  classical
  rcases op309_ring_odd_block_obstruction n hodd b with ⟨i,h⟩ | ⟨i,h⟩
  · unfold op309_ring_block_spacing_ok at h
    simp only [not_and_or, not_not] at h
    rcases h with h | h | h | h | h | h | h
    · refine ⟨i, 0, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 1, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 2, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 3, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 4, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 5, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
    · refine ⟨i, 6, ?_⟩; simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
  · refine ⟨i, 7, ?_⟩
    simpa [op309_ring_bad_cycle_edge, op309_ring_chord_word] using h
