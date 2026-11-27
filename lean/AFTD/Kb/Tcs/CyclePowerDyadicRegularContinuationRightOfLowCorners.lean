import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicRegularContinuationRightBitOne
import AFTD.Kb.Tcs.CyclePowerDyadicRegularContinuationRightRankPartner
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassInteriorFalseOfRootChildren
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_regular_continuation_right_of_low_corners

Topic: combinatorics   Node: 58950454fcd1

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Reduces the stated cycle_power_dyadic_regular_continuation_right to cycle_power_dyadic_regular_continuation_right_low_corners and cycle_power_dyadic_regular_continuation_right_next_paired, which are not proved here.

Conditional form of the rightward continuation. In a tight, exactly dyadically covered integer Boolean class model at exponent t+1 ≥ 3 with exactly t+2 active classes at every vertex, suppose that for every root r with p0 - 3·2^t ≤ r ≤ p0: if p0 - r is even, the class rooted at r contains offset 1 and its offsets come in consecutive pairs (2i and 2i+1 both in or both out, i < 2^t); if p0 - r is odd, that class consists of its two endpoints only. If moreover the class rooted at p0+1 contains none of the offsets 2^j - 1 for 2 ≤ j ≤ t, and the class rooted at p0+2 has its offsets in consecutive pairs, then the class rooted at p0+1 consists of its two endpoints only and the class rooted at p0+2 contains offset 1 and has its offsets in consecutive pairs (the conclusion of cycle_power_dyadic_regular_continuation_right).
-/

theorem cycle_power_dyadic_regular_continuation_right_of_low_corners (t : ℕ) (ht : 2 ≤ t)
    (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (p0 : ℤ)
    (hreg : ∀ r : ℤ, p0 - 3*2^t ≤ r → r ≤ p0 →
      ((p0 - r) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
      ((p0 - r) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false))
    (hcorner : ∀ j, 2 ≤ j → j ≤ t → x (p0+1) (2^j - 1) = false)
    (hpair : ∀ i < 2^t, x (p0+2) (2*i) = x (p0+2) (2*i+1)) :
    (∀ a, 0 < a → a < 2^(t+1) - 1 → x (p0+1) a = false) ∧
    (x (p0+2) 1 = true ∧ ∀ i < 2^t, x (p0+2) (2*i) = x (p0+2) (2*i+1)) := by
  have hb1 := cycle_power_dyadic_regular_continuation_right_bit_one t ht x htight hexact hcount p0 hreg
  refine ⟨?_, hb1.2, hpair⟩
  refine cycle_power_dyadic_tight_class_interior_false_of_root_children (t+1) (by omega) (x (p0+1))
    (htight (p0+1)) ?_ ?_
  · intro j hj1 hjm
    rcases Nat.lt_or_ge j 2 with hj | hj
    · have : j = 1 := by omega
      subst this
      simpa using hb1.1
    · exact hcorner j hj (by omega)
  · intro j hj1 hjm
    exact cycle_power_dyadic_regular_continuation_right_rank_partner t (by omega) x hexact p0 hreg j
      hj1 (by omega)
