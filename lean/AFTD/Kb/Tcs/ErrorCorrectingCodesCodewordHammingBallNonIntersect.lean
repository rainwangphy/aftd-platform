import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance

/-!
# ErrorCorrectingCodes.Codeword.hamming_ball_non_intersect

Topic: information   Node: 6935f034e989

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.hamming_ball_non_intersect`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/HammingBound.lean (Apache-2.0); 1 verbatim; compiled here.

Disjointness of decoding balls around distinct codewords. Let $C$ be a code of length $n$ over a finite alphabet $\alpha$ whose minimum Hamming
distance is $d$, with $d > 0$; that is, some two distinct codewords of $C$ lie at
Hamming distance exactly $d$, and no two distinct codewords lie at distance less than
$d$. Then for any two distinct codewords $c_1, c_2 \in C$, the Hamming balls of radius
$\lfloor (d-1)/2 \rfloor$ centered at $c_1$ and $c_2$ are disjoint: no codeword $c'$
satisfies both $d(c', c_1) \le \lfloor (d-1)/2 \rfloor$ and $d(c', c_2) \le \lfloor
(d-1)/2 \rfloor$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- Hamming balls of radius `⌊(d-1)/2⌋` around distinct codewords of a code with minimum distance `d` are disjoint: no point can lie within that radius of two distinct codewords. -/
lemma ErrorCorrectingCodes.Codeword.hamming_ball_non_intersect {d} (C : Code n α) (h : distance C d) (h' : 0 < d) :
    ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) →
      ∀ c' : Codeword n α,
        c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁) →
        c' ∉  (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂ c' hc'

  dsimp [hamming_ball, hamming_distance] at *

  have h_dist_c₁₂ : hamming_distance c₁ c₂ ≥ d := by exact h.2 c₁ hc₁₂.1 c₂ hc₁₂.2.1 hc₁₂.2.2

  have h_dist_c₁' : (hamming_distance c₁ c') ≤ (Nat.floor (((d : ℝ)-1)/2)) := by
    apply Set.mem_toFinset.1 at hc'
    simp at hc'
    rw[hammingDist_comm c' c₁] at hc'
    exact hc'

  by_contra h_dist_c'₂
  apply Set.mem_toFinset.1 at h_dist_c'₂
  simp at h_dist_c'₂

  have : (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d : ℝ)-1)/2 := by
    apply Nat.floor_le
    apply div_nonneg
    simp
    exact h'
    linarith

  have : (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d - (1 : ℕ) ) : ℝ) := by simp; linarith

  have : ((Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))) < d := by
    suffices (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by {
      exact Nat.lt_of_le_pred h' this
    }
    rw[← Nat.cast_sub] at this
    rw[← Nat.cast_add] at this
    exact Nat.cast_le.1 this
    linarith

  have h_cont : hamming_distance c₁ c₂ < d := by
    simp [hamming_distance] at *
    calc
      hammingDist c₁ c₂ ≤ hammingDist c₁ c' + hammingDist c' c₂ := by exact hammingDist_triangle c₁ c' c₂
      _                 ≤ (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))    := by linarith [h_dist_c₁', h_dist_c'₂]
      _                 < d                                     := by linarith[this]

  linarith
}
