import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBallNonIntersect
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance

/-!
# ErrorCorrectingCodes.Codeword.hamming_ball'_disjoint

Topic: information   Node: f85690638802

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.hamming_ball'_disjoint`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/HammingBound.lean (Apache-2.0); 1 verbatim; compiled here.

Disjointness of Hamming balls at minimum distance. Let $C$ be a code of length $n$ over an alphabet $\alpha$ whose minimum Hamming distance
is $d$, and suppose $d > 0$. Write $t = \left\lfloor \frac{d-1}{2} \right\rfloor$. Then
for any two distinct codewords $c_1, c_2 \in C$, the Hamming balls $B_t(c_1)$ and
$B_t(c_2)$ of radius $t$ centered at $c_1$ and $c_2$ are disjoint.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- Helper: Hamming balls of radius `⌊(d-1)/2⌋` around distinct codewords are pairwise disjoint as `Finset`s. -/
lemma ErrorCorrectingCodes.Codeword.hamming_ball'_disjoint {d} (C : Code n α) (h : distance C d) (h' : 0 < d) :
    ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) →
      Disjoint (hamming_ball (Nat.floor (((d : ℝ) - 1)/2)) c₁)
               (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂
  dsimp [hamming_ball]
  apply Set.disjoint_toFinset.2
  apply Set.disjoint_iff.2
  intros c' hc'
  simp at *
  rcases hc' with ⟨hc'₁, hc'₂⟩
  have : c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁) := by
    dsimp [hamming_ball]
    apply Set.mem_toFinset.2
    simp
    exact hc'₁

  apply hamming_ball_non_intersect C h h' c₁ c₂ hc₁₂ c'
  exact this
  simp
  exact hc'₂
}
