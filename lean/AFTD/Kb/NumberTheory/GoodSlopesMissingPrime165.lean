import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.GoodSlopesMissingPrimeSquarefree

/-!
# good_slopes_missing_prime165

Topic: elementary_number_theory   Node: d8080ecd6569

Provenance: helper lemma. The prime-residue part of arXiv:2611.01465, Theorem 3.1, specialized to 165.

For a permutation modulo 165 and each prime divisor p, some residue modulo p is not attained by any good slope.
-/

private theorem in962_missing_squarefree165 : Squarefree 165 := by
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have h : Squarefree ((3*5)*11 : ℕ) :=
    (Nat.squarefree_mul (by norm_num)).2
      ⟨(Nat.squarefree_mul (by norm_num)).2 ⟨hp3.squarefree, hp5.squarefree⟩,
       hp11.squarefree⟩
  exact h

theorem good_slopes_missing_prime165 (p : ℕ) [NeZero p] (hp : p = 3 ∨ p = 5 ∨ p = 11) (hd : p ∣ 165) (f : Equiv.Perm (ZMod 165)) : ∃ a : ZMod p, ∀ m ∈ good_slopes 165 f, ZMod.castHom hd (ZMod p) m ≠ a := by
  have hprime : Nat.Prime p := by rcases hp with rfl | rfl | rfl <;> decide
  exact good_slopes_missing_prime_squarefree 165 p in962_missing_squarefree165 hprime hd f
