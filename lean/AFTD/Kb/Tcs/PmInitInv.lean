import AFTD.Prelude
import AFTD.Kb.Tcs.PMStateInv
import AFTD.Kb.Tcs.PmInit

/-!
# pm_init_inv

Topic: algorithms   Node: 21ee75bcb2bf

The initial adversary state (all elements alive, every element its own component) satisfies the adversary invariant.
-/

open Finset in
theorem pm_init_inv (n : ℕ) : (pmInit n).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf; simp [pmInit] at hf
  · intro f hf; simp [pmInit] at hf
  · intro f hf; simp [pmInit] at hf
  · intro x _; rfl
  · intro x hx; simp [pmInit] at hx
  · intro x y h; exact Fin.ext (by simpa [pmInit] using h)
  · intro x; exact ⟨x, Finset.mem_univ _, rfl⟩
