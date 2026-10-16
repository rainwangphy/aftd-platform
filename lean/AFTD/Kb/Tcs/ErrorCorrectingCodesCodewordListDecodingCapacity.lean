import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordLtOneOfLeOneSubInv
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastOneLtOfTwoLe
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastPosOfTwoLe
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordQaryEntropy
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBallSizeAsymptoticUpperBound
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordQaryEntropyPos
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordExistsListDecodableCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordListDecodingCountingIneq
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordListDecodable
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordAdd
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordSub
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ErrorCorrectingCodes.Codeword.list_decoding_capacity

Topic: information   Node: 9f1d887630d8

Provenance: formalization of a published result. Source: List-decoding over a q-ary alphabet, as formalized in TCSlib (`ErrorCorrectingCodes.Codeword.list_decoding_capacity`). Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/ListDecoding.lean (Apache-2.0); 1 verbatim; compiled here.

List-decoding over a q-ary alphabet. Let $\alpha$ be a finite field, write $q = \abs{\alpha}$ for the number of its elements,
and fix a real number $p$ with $0 < p \le 1 - \tfrac{1}{q}$ together with an integer $L
\ge 1$. In this regime one considers block codes over the alphabet $\alpha$ that admit
list decoding from a $p$-fraction of symbol errors with output lists of size at most
$L$, and the associated rate $r$ they can achieve.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ErrorCorrectingCodes ErrorCorrectingCodes.Codeword in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- **List-decoding capacity theorem**: for any `0 < ρ ≤ 1 − 1/q` and `L ≥ 1`, there exist codes of rate `r = 1 − H_q(ρ) − 1/L` that are `(ρ, L)`-list-decodable. In other words, one can list-decode at any rate below the list-decoding capacity `1 − H_q(ρ)` using list size `L`. -/
theorem ErrorCorrectingCodes.Codeword.list_decoding_capacity
  (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α)) (hp : 0 < p ∧ p ≤ 1 - 1/q)
  (L : ℕ) (hL : 1 ≤ L) :
  let r := 1 - (qaryEntropy q p) - 1 / (L : ℝ)
  let M := Nat.floor ((q : ℝ) ^ (r * n))
  ∃ C : Code n α,
    (M ≤ C.card) ∧
      list_decodable p
        (by linarith [hp])
        (by
          linarith [hp,
            one_div_nonneg.2 (show (0 : ℝ) ≤ (q : ℝ) from by exact_mod_cast (Nat.zero_le q))])
        n L hL C := by
  classical
  intro r M

  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_iff.mpr (by simpa using Fintype.one_lt_card)
  have hq_pos : (1 : ℝ) < (q : ℝ) := by
    exact natCast_one_lt_of_two_le hq2
  have hq_ge_0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
  have hq_ge_1 : (1 : ℝ) ≤ (q : ℝ) := by linarith

  have hr : r ≤ 1 := by
    have hH : 0 < qaryEntropy q p := qary_entropy_pos q p hq hp
    have hL0 : 0 ≤ 1 / (L : ℝ) := by
      have : (0 : ℝ) < (L : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hL)
      exact one_div_nonneg.mpr (le_of_lt this)
    dsimp [r]
    linarith

  have exists_code_card_eq
    (hM : M ≤ Fintype.card (Codeword n α)) :
    ∃ C : Code n α, C.card = M := by
    classical
    obtain ⟨S, hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq hM (s := (Finset.univ : Finset (Codeword n α)))
    refine ⟨S, ?_⟩
    simpa using hScard

  by_cases hML : M ≤ L
  · have hM_le_univ : M ≤ Fintype.card (Codeword n α) := by
      have : Fintype.card (Codeword n α) = q^n := by
        simp [Codeword, hq, Fintype.card_pi]
      have hM_le_qn : M ≤ q^n := by
        have h_rn : r * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hr]
        have hpow :
          (q : ℝ) ^ (r * (n : ℝ)) ≤ (q : ℝ) ^ ((n : ℝ)) := by
            exact Real.rpow_le_rpow_of_exponent_le hq_ge_1 h_rn
        have hfloor_le :
          (M : ℝ) ≤ (q : ℝ) ^ (r * (n : ℝ)) := by
          simpa using (Nat.floor_le (Real.rpow_nonneg hq_ge_0 (r * (n : ℝ))))
        have : (M : ℝ) ≤ (q : ℝ) ^ ((n : ℝ)) := le_trans hfloor_le hpow
        have : (M : ℝ) ≤ (q^n : ℝ) := by simpa [Real.rpow_natCast] using this
        exact_mod_cast this
      simpa [this] using hM_le_qn

    rcases exists_code_card_eq hM_le_univ with ⟨C, hCcard⟩
    refine ⟨C, ?_, ?_⟩
    · simp [hCcard]
    · unfold list_decodable
      intro y
      have hleC : (hamming_ball (Nat.floor (p * n)) y ∩ C).card ≤ C.card := by
        exact Finset.card_le_card (Finset.inter_subset_right)
      have : (hamming_ball (Nat.floor (p * n)) y ∩ C).card ≤ L := by
        rw [← hCcard] at hML
        simpa [hCcard] using le_trans hleC hML
      exact this

  · have hL_lt_M : L < M := Nat.lt_of_not_ge hML

    let N : ℕ := q^n
    let V : ℕ := Nat.floor (Real.rpow q ((qaryEntropy q p) * n))

    have hV_def : V = Nat.floor (Real.rpow q ((qaryEntropy q p) * n)) := by rfl

    have hM_le : M ≤ q^n := by
      have h_rn : r * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hr]
      have hpow :
        (q : ℝ) ^ (r * (n : ℝ)) ≤ (q : ℝ) ^ ((n : ℝ)) := by
        exact Real.rpow_le_rpow_of_exponent_le hq_ge_1 h_rn
      have hfloor_le :
        (M : ℝ) ≤ (q : ℝ) ^ (r * (n : ℝ)) := by
        simpa using (Nat.floor_le (Real.rpow_nonneg hq_ge_0 (r * (n : ℝ))))
      have : (M : ℝ) ≤ (q : ℝ) ^ ((n : ℝ)) := le_trans hfloor_le hpow
      have : (M : ℝ) ≤ (q^n : ℝ) := by simpa [Real.rpow_natCast] using this
      exact_mod_cast this

    have hM_pos : 0 < M := by
        linarith

    have hV_ball :
    ∀ y : Codeword n α, (hamming_ball (Nat.floor (p * n)) y).card ≤ V := by
      intro y
      have hball_real :
        (hamming_ball (Nat.floor (p * n)) y).card ≤ Real.rpow q (qaryEntropy q p * n) := by
        have hα : Nontrivial α := inferInstance
        have hradius : Nat.floor (p * n) = ⌊(n : ℝ) * p⌋₊ := by
          simp [mul_comm]
        simpa [hradius] using (hamming_ball_size_asymptotic_upper_bound q n p hq hα hp) y
      have : ((hamming_ball (Nat.floor (p * n)) y).card : ℝ) ≤ Real.rpow q (qaryEntropy q p * n) := by
        exact_mod_cast hball_real
      exact (Nat.le_floor this)

    have hr_def : r = 1 - (qaryEntropy q p) - 1 / (L : ℝ) := rfl
    have hM_def : M = Nat.floor ((q : ℝ) ^ (r * n)) := rfl

    have h_ineq :
      (q : ℝ)^n * (Nat.choose V (L+1)) * (Nat.choose (q^n - (L+1)) (M - (L+1)))
        < Nat.choose (q^n) M := by
      refine listDecoding_counting_ineq q p n L hq2 hL r hr_def M hM_def V hV_def
        (by exact hM_pos)
        hM_le
        hL_lt_M

    have h_ineq_nat :
        (Fintype.card α)^n
            * Nat.choose V (L+1)
            * Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1))
        < Nat.choose ((Fintype.card α)^n) M := by
        have h_ineq_real :
            ((Fintype.card α)^n : ℝ)
            * (Nat.choose V (L+1) : ℝ)
            * (Nat.choose ((Fintype.card α)^n - (L+1)) (M - (L+1)) : ℝ)
            < (Nat.choose ((Fintype.card α)^n) M : ℝ) := by
            simpa [Nat.cast_pow, hq] using h_ineq
        exact_mod_cast h_ineq_real

    have hp1 : 0 ≤ p := le_of_lt hp.1
    have hp2 : p ≤ 1 := by
      exact le_of_lt (lt_one_of_le_one_sub_inv (natCast_pos_of_two_le hq2) hp.2)

    obtain ⟨C, hCcard, hCld⟩ :=
        exists_listDecodable_code (n := n) (L := L) (M := M) (p := p)
            hp1 hp2 hL
            V hV_ball
            h_ineq_nat
            (by simpa [hq] using hM_le)
            hL_lt_M

    refine ⟨C, ?_, hCld⟩
    simp [hCcard]
