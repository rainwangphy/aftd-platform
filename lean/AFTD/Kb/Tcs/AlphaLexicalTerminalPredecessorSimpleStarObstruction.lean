import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalOddCompletionIffRotationMax
import AFTD.Kb.Tcs.AlphaLexicalLtIffInversePrefix
import AFTD.Kb.Tcs.AlphaBinaryCompletionInverse
import AFTD.Kb.Tcs.BrgcInverseRotateTentFormula
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow

/-!
# alpha_lexical_terminal_predecessor_simple_star_obstruction

Topic: combinatorics   Node: a9da9853e682

Provenance: helper lemma. Computed obstruction to a simplified divisor-based route for OP-392, arXiv:2610.24758; lexical order and parity extensions follow arXiv:0810.5205, Section 1.1.

The two displayed lexical sequences are adjacent among sequences of degree 19 and have meet f=(2,1,1). The later sequence has a lexical prefix of length two, its index-two split is nonlexical, and every later even-index elementary operation is nonlexical. With quotient d=4 it is not the proposed simple-star word f_o (f_e)^2 f. The example does not exclude other star factorizations.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def T20 (t : ℕ) : ℕ :=
  if t < 524288 then 2*t+t%2 else 2*(1048575-t)+t%2

private theorem in817_tent5 (q : ℕ) (hl : 439725 ≤ q) (hu : q ≤ 444849) :
  2*q+1 ≤ (T20^[5]) (2*q+1) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp only [T20]
  split_ifs <;> omega

private theorem in817_tent10 (q : ℕ) (hl : 444850 ≤ q) (hu : q ≤ 445004) :
  2*q+1 ≤ (T20^[10]) (2*q+1) := by
  have h1 : T20 (2*q+1) = 2097149 - 4*q := by
    unfold T20
    split_ifs <;> omega
  have h2 : T20 (2097149 - 4*q) = 4194299 - 8*q := by
    unfold T20
    split_ifs <;> omega
  have h3 : T20 (4194299 - 8*q) = 16*q - 6291447 := by
    unfold T20
    split_ifs <;> omega
  have h4 : T20 (16*q - 6291447) = 14680045 - 32*q := by
    unfold T20
    split_ifs <;> omega
  have h5 : T20 (14680045 - 32*q) = 29360091 - 64*q := by
    unfold T20
    split_ifs <;> omega
  have h6 : T20 (29360091 - 64*q) = 128*q - 56623031 := by
    unfold T20
    split_ifs <;> omega
  have h7 : T20 (128*q - 56623031) = 256*q - 113246061 := by
    unfold T20
    split_ifs <;> omega
  have h8 : T20 (256*q - 113246061) = 228589273 - 512*q := by
    unfold T20
    split_ifs <;> omega
  have h9 : T20 (228589273 - 512*q) = 1024*q - 455081395 := by
    unfold T20
    split_ifs <;> omega
  have hlast : 2*q+1 ≤ T20 (1024*q - 455081395) := by
    unfold T20
    split_ifs <;> omega
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9] using hlast


private theorem in817_rank_iter20 (x r : ℕ) (hx0 : 0 < x) (hx1 : x < 2^20 - 1) :
    brgc_inverse 20 ((bitword_rotate 20)^[r] x) = (T20^[r]) (brgc_inverse 20 x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hy := (bitword_is_aperiodic_of_prime_iterate_eq_mod 20 (by norm_num) x hx0 hx1 r).2.2
    have hy' : (bitword_rotate 20)^[r] x < 2^20 := by omega
    have hr : brgc_inverse 20 ((bitword_rotate 20)^[r] x) < 2^20 := brgc_inverse_lt_two_pow hy'
    conv_lhs => rw [← brgc_word_inverse hy']
    rw [brgc_inverse_rotate_tent_formula 20 _ (by norm_num) hr]
    rw [ih]
    norm_num [T20]

private theorem in817_tent_small (q : ℕ) (hl : 439723 ≤ q) (hu : q ≤ 439724) :
  2*q+1 ≤ (T20^[17]) (2*q+1) := by
  interval_cases q <;> norm_num [T20, Function.iterate_succ_apply']


instance (a b : List ℕ) : Decidable (alpha_lexical_lt a b) := by
  unfold alpha_lexical_lt
  infer_instance
instance (a : List ℕ) : Decidable (alpha_is_lexical a) := by
  unfold alpha_is_lexical
  infer_instance

private def in817_low20 : List ℕ := [2,1,1,1,2,1,1,1,2,1,1,1,1,1,1,1]
private def in817_high20 : List ℕ := [2,1,2,2,1,1,1,2,1,2,2,1,1]
private def in817_op20 (a : List ℕ) (i : ℕ) : List ℕ :=
  if 1 < a.getD i 0 then a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)
  else a.take (i-1) ++ [a.getD (i-1) 0 + 1] ++ a.drop (i + 1)

private theorem in817_lowrank20 :
    brgc_inverse 19 (alpha_binary_prefix in817_low20) = 439722 := by decide
private theorem in817_highrank20 :
    brgc_inverse 19 (alpha_binary_prefix in817_high20) = 445005 := by decide
private theorem in817_lowpos20 : ∀ v ∈ in817_low20, 0 < v := by decide
private theorem in817_highpos20 : ∀ v ∈ in817_high20, 0 < v := by decide

private theorem in817_facts20 :
    alpha_is_lexical in817_low20 ∧ alpha_is_lexical in817_high20 ∧
    in817_low20.sum + 1 = 20 ∧ in817_high20.sum + 1 = 20 ∧
    alpha_lexical_lt in817_low20 in817_high20 ∧
    alpha_lexical_meet in817_low20 in817_high20 = [2,1,1] ∧
    alpha_is_lexical (in817_high20.take 2) ∧
    ¬ alpha_is_lexical (in817_op20 in817_high20 2) ∧
    (∀ j : Fin 13, 2 < j.val → j.val % 2 = 0 →
      ¬ alpha_is_lexical (in817_op20 in817_high20 j.val)) ∧
    in817_high20 ≠ [2,1,2,2,1,1,1,2,1,1,1,2,1,1] := by decide

theorem alpha_lexical_terminal_predecessor_simple_star_obstruction :
  let a : List ℕ := [2,1,1,1,2,1,1,1,2,1,1,1,1,1,1,1]
  let b : List ℕ := [2,1,2,2,1,1,1,2,1,2,2,1,1]
  alpha_is_lexical a ∧ alpha_is_lexical b ∧
  a.sum + 1 = 20 ∧ b.sum + 1 = 20 ∧ alpha_lexical_lt a b ∧
  (∀ c : List ℕ, alpha_is_lexical c → c.sum + 1 = 20 →
    ¬ (alpha_lexical_lt a c ∧ alpha_lexical_lt c b)) ∧
  alpha_lexical_meet a b = [2,1,1] ∧ alpha_is_lexical (b.take 2) ∧
  ¬ alpha_is_lexical (b.take 2 ++ [b.getD 2 0 - 1, 1] ++ b.drop 3) ∧
  (∀ j : Fin 13, 2 < j.val → j.val % 2 = 0 → ¬ alpha_is_lexical
    (if 1 < b.getD j.val 0 then
      b.take j.val ++ [b.getD j.val 0 - 1, 1] ++ b.drop (j.val + 1)
     else b.take (j.val - 1) ++ [b.getD (j.val - 1) 0 + 1] ++ b.drop (j.val + 1))) ∧
  b ≠ [2,1,2,2,1,1,1,2,1,1,1,2,1,1] := by
  change alpha_is_lexical in817_low20 ∧ alpha_is_lexical in817_high20 ∧
    in817_low20.sum + 1 = 20 ∧ in817_high20.sum + 1 = 20 ∧
    alpha_lexical_lt in817_low20 in817_high20 ∧
    (∀ c : List ℕ, alpha_is_lexical c → c.sum + 1 = 20 →
      ¬ (alpha_lexical_lt in817_low20 c ∧ alpha_lexical_lt c in817_high20)) ∧
    alpha_lexical_meet in817_low20 in817_high20 = [2,1,1] ∧
    alpha_is_lexical (in817_high20.take 2) ∧
    ¬ alpha_is_lexical (in817_op20 in817_high20 2) ∧
    (∀ j : Fin 13, 2 < j.val → j.val % 2 = 0 →
      ¬ alpha_is_lexical (in817_op20 in817_high20 j.val)) ∧
    in817_high20 ≠ [2,1,2,2,1,1,1,2,1,1,1,2,1,1]
  refine ⟨in817_facts20.1, in817_facts20.2.1, in817_facts20.2.2.1,
    in817_facts20.2.2.2.1, in817_facts20.2.2.2.2.1, ?_,
    in817_facts20.2.2.2.2.2⟩
  intro c hc hsum hcbet
  have hcs : c.sum = 19 := by omega
  have hlo : in817_low20.sum = c.sum := by simp [in817_low20, hcs]
  have hhi : c.sum = in817_high20.sum := by simp [in817_high20, hcs]
  have hrlo := (alpha_lexical_lt_iff_inverse_prefix in817_low20 c
    in817_lowpos20 hc.2.1 hlo).mp hcbet.1
  have hrhi := (alpha_lexical_lt_iff_inverse_prefix c in817_high20
    hc.2.1 in817_highpos20 hhi).mp hcbet.2
  simp only [show in817_low20.sum = 19 by decide,
    show in817_high20.sum = 19 by decide, hcs, in817_lowrank20, in817_highrank20] at hrlo hrhi
  let q := brgc_inverse 19 (alpha_binary_prefix c)
  have hq : 439723 ≤ q ∧ q ≤ 445004 := by dsimp [q]; omega
  let x := 2 * alpha_binary_prefix c + (c.length + 1) % 2
  have hmax := (alpha_lexical_odd_completion_iff_rotation_max 20 (by norm_num)
    c hc.1 hc.2.1 (by omega)).mp hc
  change 0 < x ∧ x < 2^20-1 ∧ ∀ r : ℕ, 0 < r → r < 20 →
    brgc_inverse 20 ((bitword_rotate 20)^[r] x) < brgc_inverse 20 x at hmax
  have hrank : brgc_inverse 20 x = 2*q+1 := by
    have h := (alpha_binary_completion_inverse c hc.2.1).2
    simpa only [hcs] using h
  by_cases hsmall : q ≤ 439724
  · have hh := in817_tent_small q hq.1 hsmall
    have hs := hmax.2.2 17 (by norm_num) (by norm_num)
    rw [in817_rank_iter20 x 17 hmax.1 hmax.2.1, hrank] at hs
    omega
  · by_cases hmid : q ≤ 444849
    · have hh := in817_tent5 q (by omega) hmid
      have hs := hmax.2.2 5 (by norm_num) (by norm_num)
      rw [in817_rank_iter20 x 5 hmax.1 hmax.2.1, hrank] at hs
      omega
    · have hh := in817_tent10 q (by omega) hq.2
      have hs := hmax.2.2 10 (by norm_num) (by norm_num)
      rw [in817_rank_iter20 x 10 hmax.1 hmax.2.1, hrank] at hs
      omega
