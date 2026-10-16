import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistLeLength
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall'Disjoint
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBallSize
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ErrorCorrectingCodes.Codeword.hamming_bound

Topic: information   Node: 8560c412fb62

Provenance: formalization of a published result. Source: Hamming (sphere-packing) bound, as formalized in TCSlib (`ErrorCorrectingCodes.Codeword.hamming_bound`). Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/HammingBound.lean (Apache-2.0); 1 verbatim; compiled here.

Hamming (sphere-packing) bound. Let $\alpha$ be a finite alphabet with $q = \abs{\alpha} > 1$ symbols, and let $C
\subseteq \alpha^n$ be a code (a finite set of length-$n$ codewords) whose minimum
Hamming distance is $d$, with $d > 0$. Then
\[
\abs{C} \;\le\; \frac{q^{\,n}}{\displaystyle\sum_{i=0}^{\lfloor (d-1)/2 \rfloor}
\binom{n}{i}\,(q-1)^{i}}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ErrorCorrectingCodes ErrorCorrectingCodes.Codeword in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **Hamming bound** (sphere-packing bound): a code `C` of block-length `n` and minimum distance `d` over an alphabet `α` with `|α| > 1` satisfies `|C| ≤ |α|^n / Vol(n, ⌊(d-1)/2⌋)`. -/
theorem ErrorCorrectingCodes.Codeword.hamming_bound (n d : ℕ) (C : Code n α) (h : distance C d) (h'' : Fintype.card α > 1)
    (hd : 0 < d) :
    C.card ≤ Fintype.card α ^ n /
      (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1))
        (λ i => Nat.choose n i * (Fintype.card α - 1)^i)) := by {
  have h1 : 0 < Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i) := by
    apply Finset.sum_pos
    intros i hi
    apply mul_pos
    · apply Nat.choose_pos
      have : (Nat.floor (((d : ℝ)-1)/2)) + 1 ≤ d := by
        suffices (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by exact Nat.add_le_of_le_sub hd this
        suffices (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d - (1 : ℕ) ) : ℝ) by{
          rw[← Nat.cast_sub] at this
          exact Nat.cast_le.1 this
          exact hd
        }
        calc
          (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d : ℝ)-1)/2        := by {
            apply Nat.floor_le
            apply div_nonneg
            simp
            exact hd
            linarith
          }
          _                           ≤ ((d - (1 : ℕ) ) : ℝ) := by {
            simp
            linarith
          }
      calc
        i ≤ ((Nat.floor (((d : ℝ)-1)/2)) + 1)  := by linarith [Finset.mem_range.1 hi]
        _ ≤ d  := by exact this
        _ ≤ n  := by exact dist_le_length C d h
    · apply Nat.pow_pos
      simp
      exact h''
    simp


  suffices C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) ≤ Fintype.card α ^ n by exact (Nat.le_div_iff_mul_le h1).mpr this

  let S : Finset (Codeword n α) := Finset.univ
  have h_Scard: S.card = Fintype.card α ^ n := by simp[S]

  have h_disjoint : (C : Set (Codeword n α)).PairwiseDisjoint (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c)) := by
    intros x hx y hy hxy
    simp at hx hy
    exact hamming_ball'_disjoint C h hd x y ⟨hx, hy, hxy⟩

  let SU : Finset (Codeword n α) := Finset.disjiUnion C (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c)) h_disjoint


  have h_SUcard : SU.card = C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) := by
    rw[Finset.card_disjiUnion]
    apply Finset.sum_eq_card_nsmul
    exact fun a _ => hamming_ball_size n (Nat.floor (((d : ℝ)-1)/2)) a

  calc
    (C.card * Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) fun i => Nat.choose n i * (Fintype.card α - 1) ^ i) = SU.card := by exact h_SUcard.symm
    _                                                                                                            ≤ S.card  := by exact Finset.card_le_univ SU
    _                                                                                                            = Fintype.card α ^ n   := by exact h_Scard


}
