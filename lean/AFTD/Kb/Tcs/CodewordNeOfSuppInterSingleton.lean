import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# codeword_ne_of_supp_inter_singleton

Topic: information   Node: 704a6a111654

Provenance: helper lemma. arXiv:2610.30613, Lemma 2.1

Let $\alpha$ be an alphabet with decidable equality and zero element $0$. If $x, y : \mathrm{Fin}\, n \to \alpha$ are codewords such that $x$ has support cardinality $(\mathrm{codeword\_supp}(x)).\mathrm{card} = 2$ and the intersection of their supports is a singleton $\mathrm{codeword\_supp}(x) \cap \mathrm{codeword\_supp}(y) = \{i\}$, then $x \ne y$.
-/

/-- Two codewords are distinct if one has weight 2 and their supports intersect in a single coordinate. -/
theorem codeword_ne_of_supp_inter_singleton
    {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (x y : Fin n → α) (i : Fin n)
    (hx_wt : (codeword_supp x).card = 2)
    (h_inter : codeword_supp x ∩ codeword_supp y = {i}) :
    x ≠ y := by
  intro hxy
  subst hxy
  simp only [Finset.inter_self] at h_inter
  rw [h_inter] at hx_wt
  simp at hx_wt
