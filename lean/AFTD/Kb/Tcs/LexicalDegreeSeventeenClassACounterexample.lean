import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalOddCompletionIffRotationMaxOfPrime
import AFTD.Kb.Tcs.AlphaLexicalLtIffInversePrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixInverseParity
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.AlphaLexicalMeet
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcInverse

/-!
# lexical_degree_seventeen_class_a_counterexample

Topic: combinatorics   Node: 084cb4e5b878

Provenance: erratum. Corrects: Adjacency and Parity Relations of Words in Discrete Dynamical Systems, DOI 10.1006/jcta.2000.3112, Theorem 5.1, class A, equation (5.1). The example concerns the asserted repeated-prefix structural formula, not the parity theorem or the necklace conjecture.

The lexical sequences a = (3,1,1,3,3,2,2,1) and b = (3,1,1,2,1,3,2,2,1) both have degree 16, are adjacent in the source lexical order among lexical sequences of degree 16, and have meet f = (3,1,1,2). However, a does not begin with (3,1,1,3,3,1,1,3), the square of the even extension of f required by the class-A formula with n=17, m=8, d=2, r=1.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def lo : List ℕ := [3, 1, 1, 3, 3, 2, 2, 1]
private def hi : List ℕ := [3, 1, 1, 2, 1, 3, 2, 2, 1]

instance (a b : List ℕ) : Decidable (alpha_lexical_lt a b) := by
  unfold alpha_lexical_lt
  infer_instance
instance (a : List ℕ) : Decidable (alpha_is_lexical a) := by
  unfold alpha_is_lexical
  infer_instance

example : alpha_is_lexical lo ∧ alpha_is_lexical hi ∧
    alpha_lexical_lt lo hi ∧
    alpha_lexical_meet lo hi = [3,1,1,2] := by decide

private theorem finite_cert : ∀ k : Fin 50, ∃ j : Fin 17,
    0 < j.val ∧
    let r := 59623 + k.val
    let x := 2 * brgc_word r + (r + 1) % 2
    brgc_inverse 17 x ≤ brgc_inverse 17 ((bitword_rotate 17)^[j.val] x) := by decide


private theorem lorank : brgc_inverse 16 (alpha_binary_prefix lo) = 59622 := by decide
private theorem hirank : brgc_inverse 16 (alpha_binary_prefix hi) = 59673 := by decide
private theorem lopos : ∀ v ∈ lo, 0 < v := by decide
private theorem hipos : ∀ v ∈ hi, 0 < v := by decide

theorem lexical_degree_seventeen_class_a_counterexample :
    let a : List ℕ := [3, 1, 1, 3, 3, 2, 2, 1]
    let b : List ℕ := [3, 1, 1, 2, 1, 3, 2, 2, 1]
    alpha_is_lexical a ∧ alpha_is_lexical b ∧
    a.sum + 1 = 17 ∧ b.sum + 1 = 17 ∧ alpha_lexical_lt a b ∧
    (∀ c : List ℕ, alpha_is_lexical c → c.sum + 1 = 17 →
      ¬ (alpha_lexical_lt a c ∧ alpha_lexical_lt c b)) ∧
    alpha_lexical_meet a b = [3,1,1,2] ∧
    ¬ ∃ tail : List ℕ, a = [3,1,1,3,3,1,1,3] ++ tail := by
  change alpha_is_lexical lo ∧ alpha_is_lexical hi ∧
    lo.sum + 1 = 17 ∧ hi.sum + 1 = 17 ∧ alpha_lexical_lt lo hi ∧
    (∀ c : List ℕ, alpha_is_lexical c → c.sum + 1 = 17 →
      ¬ (alpha_lexical_lt lo c ∧ alpha_lexical_lt c hi)) ∧
    alpha_lexical_meet lo hi = [3,1,1,2] ∧
    ¬ ∃ tail : List ℕ, lo = [3,1,1,3,3,1,1,3] ++ tail
  have hl : alpha_is_lexical lo ∧ alpha_is_lexical hi ∧
      alpha_lexical_lt lo hi ∧
      alpha_lexical_meet lo hi = [3,1,1,2] := by decide
  refine ⟨hl.1, hl.2.1, by decide, by decide, hl.2.2.1, ?_, hl.2.2.2, ?_⟩
  · intro c hc hsum hcbet
    have hcs : c.sum = 16 := by omega
    have hlo : lo.sum = c.sum := by simp [lo, hcs]
    have hhi : c.sum = hi.sum := by simp [hi, hcs]
    have hrlo := (alpha_lexical_lt_iff_inverse_prefix lo c lopos hc.2.1 hlo).mp hcbet.1
    have hrhi := (alpha_lexical_lt_iff_inverse_prefix c hi hc.2.1 hipos hhi).mp hcbet.2
    simp only [show lo.sum = 16 by decide, show hi.sum = 16 by decide, hcs, lorank, hirank] at hrlo hrhi
    let r := brgc_inverse 16 (alpha_binary_prefix c)
    have hr : 59623 ≤ r ∧ r < 59673 := by dsimp [r]; omega
    let k : Fin 50 := ⟨r - 59623, by omega⟩
    obtain ⟨j, hj0, hj⟩ := finite_cert k
    have hjr : 59623 + k.val = r := by dsimp [k]; omega
    simp only [hjr] at hj
    have hb := (alpha_binary_prefix_bounds c hc.1 hc.2.1).2
    rw [hcs] at hb
    have hword : brgc_word r = alpha_binary_prefix c := brgc_word_inverse hb
    have hpar := alpha_binary_prefix_inverse_parity c hc.2.1
    rw [hcs] at hpar
    have hmod : (r + 1) % 2 = (c.length + 1) % 2 := by dsimp [r]; omega
    rw [hword, hmod] at hj
    have hmax := (alpha_lexical_odd_completion_iff_rotation_max_of_prime 17
      (by norm_num) (by norm_num) c hc.1 hc.2.1 (by omega)).mp hc
    dsimp only at hmax
    have hstrict := hmax.2.2 j.val hj0 j.isLt
    exact (not_le_of_gt hstrict) hj
  · intro h
    obtain ⟨tail, htail⟩ := h
    have := congrArg (List.getD · 5 0) htail
    simp [lo] at this
