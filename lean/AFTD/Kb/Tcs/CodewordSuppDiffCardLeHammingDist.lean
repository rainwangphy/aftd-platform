import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# codeword_supp_diff_card_le_hammingDist

Topic: information   Node: 616fd15751eb

Provenance: helper lemma. arXiv:2610.30613, Proof of Lemma 3.3

For any two codewords $x, y : \mathrm{Fin}\, n \to \alpha$, the sum of the cardinalities of the set differences of their supports, $(\mathrm{codeword\_supp}(x) \setminus \mathrm{codeword\_supp}(y)).\mathrm{card} + (\mathrm{codeword\_supp}(y) \setminus \mathrm{codeword\_supp}(x)).\mathrm{card}$, is at most their Hamming distance $\mathrm{hammingDist}(x, y)$.
-/

/-- The sum of the sizes of the coordinate set differences of two codeword supports is at most their Hamming distance. -/
theorem codeword_supp_diff_card_le_hammingDist {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (x y : Fin n → α) :
    (codeword_supp x \ codeword_supp y).card + (codeword_supp y \ codeword_supp x).card ≤ hammingDist x y := by
  have hdisj : Disjoint (codeword_supp x \ codeword_supp y) (codeword_supp y \ codeword_supp x) :=
    disjoint_sdiff_sdiff
  rw [← Finset.card_union_of_disjoint hdisj]
  unfold hammingDist
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_union, Finset.mem_sdiff, codeword_supp, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · intro heq
    rw [heq] at h1
    exact h2 h1
  · intro heq
    rw [heq] at h2
    exact h2 h1
