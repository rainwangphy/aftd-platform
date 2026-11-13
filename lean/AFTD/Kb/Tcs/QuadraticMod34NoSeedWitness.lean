import AFTD.Prelude

/-!
# quadratic_mod34_no_seed_witness

Topic: combinatorics   Node: d60a204c963f

Provenance: helper lemma. Explicit finite counterexample in experiment 25430 for OP-1482.

The set S={0,4,7,14,21,28,31} modulo 34 avoids red triples of second difference 2 and hits every monic quadratic sequence in its first 17 terms, yet contains no pullback of any translate of the four listed modulo-17 seed sets. The pullback of a residue r contains both r and r+17.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

private def S : Finset (ZMod 34) := {0,4,7,14,21,28,31}
private def T : Finset ℕ := {0,4,7,14,21,28,31}

theorem test_mod34_red : ∀ x y z : ZMod 34, x ∈ S → y ∈ S → z ∈ S → x - 2*y + z ≠ 2 := by
  intro x y z hx hy hz
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem test_mod34_blue : ∀ a b : ZMod 34, ∃ k : Fin 17, (k.val : ZMod 34)^2 + a*k.val + b ∈ S := by
  decide

theorem test_mod34_seeds : ∀ t : Fin 17,
    ∀ A ∈ ([{0,3,6}, {0,5,11}, {0,3,10}, {0,4,8,12}] : List (Finset ℕ)),
      ∃ r ∈ A, (t.val+r)%17 ∉ T ∨ (t.val+r)%17+17 ∉ T := by
  decide

theorem quadratic_mod34_no_seed_witness : let S : Finset (ZMod 34) := {0, 4, 7, 14, 21, 28, 31}; let T : Finset ℕ := {0, 4, 7, 14, 21, 28, 31}; (∀ x y z : ZMod 34, x ∈ S → y ∈ S → z ∈ S → x - 2*y + z ≠ 2) ∧ (∀ a b : ZMod 34, ∃ k : Fin 17, (k.val : ZMod 34)^2 + a*k.val + b ∈ S) ∧ (∀ t : Fin 17, ∀ A ∈ ([{0,3,6}, {0,5,11}, {0,3,10}, {0,4,8,12}] : List (Finset ℕ)), ∃ r ∈ A, (t.val+r)%17 ∉ T ∨ (t.val+r)%17+17 ∉ T) := by
  exact ⟨test_mod34_red, test_mod34_blue, test_mod34_seeds⟩
