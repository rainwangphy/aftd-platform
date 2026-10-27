import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeMem

/-!
# binary_partial_word_cube_odd_sum

Topic: combinatorics   Node: 6a75d4360759

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A rational function which changes sign under flipping a free coordinate of a partial-word cube sums to zero on that cube.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_odd_sum {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (b : V → Bool) (v : V) (hv : v ∉ s)
    (F : (V → Bool) → ℚ)
    (hodd : ∀ f ∈ binary_partial_word_cube s b,
      F (Function.update f v (!f v)) = -F f) :
    ∑ f ∈ binary_partial_word_cube s b, F f = 0 := by
  classical
  let flip : (V → Bool) → (V → Bool) := fun f => Function.update f v (!f v)
  have hflip (f : V → Bool) : flip (flip f) = f := by
    funext w
    by_cases hw : w = v
    · subst w
      simp [flip]
    · simp [flip, hw]
  have hmem (f : V → Bool) (hf : f ∈ binary_partial_word_cube s b) :
      flip f ∈ binary_partial_word_cube s b := by
    rw [binary_partial_word_cube_mem] at hf ⊢
    intro w hw
    have hne : w ≠ v := by rintro rfl; exact hv hw
    simpa [flip, hne] using hf w hw
  refine sum_involution (fun f hf => flip f) ?_ ?_ hmem (fun f hf => hflip f)
  · intro f hf
    change F f + F (Function.update f v (!f v)) = 0
    rw [hodd f hf]
    ring
  · intro f hf hF h
    have he := congrArg (fun g : V → Bool => g v) h
    simp only [flip, Function.update_self] at he
    cases hfv : f v <;> simp [hfv] at he
