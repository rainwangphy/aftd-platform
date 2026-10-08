import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance

/-!
# ErrorCorrectingCodes.Codeword.dist_le_length

Topic: information   Node: ed8dbeeb0c68

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.dist_le_length`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Minimum distance is at most the block length. Let $C$ be a code of length $n$ over an alphabet $\alpha$ — that is, a finite set of
codewords, each a function $\mathrm{Fin}\,n \to \alpha$ — and let $d$ be a natural
number that is the minimum distance of $C$: there exist two distinct codewords of $C$ at
Hamming distance exactly $d$, and every pair of distinct codewords of $C$ is at Hamming
distance at least $d$. Then $d \le n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The minimum distance of a code is at most the block length. -/
lemma ErrorCorrectingCodes.Codeword.dist_le_length (C : Code n α) (d : ℕ) (h : distance C d) : d ≤ n := by
  rcases h with ⟨h1, _⟩
  rcases h1 with ⟨c₁, ⟨_, ⟨c₂, ⟨_, ⟨_, hdeq⟩⟩⟩⟩⟩
  have hle : hammingDist c₁ c₂ ≤ n :=
    calc
      hammingDist c₁ c₂ ≤ Fintype.card (Fin n) := by exact hammingDist_le_card_fintype
      _                 = n                    := by rel[Fintype.card_fin n]
  dsimp [hamming_distance] at hdeq
  rw [hdeq] at hle
  exact hle
