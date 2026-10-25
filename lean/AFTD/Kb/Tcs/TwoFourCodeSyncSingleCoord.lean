import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp
import AFTD.Kb.Tcs.HammingDistEqOfCodewordSuppInterSingleton
import AFTD.Kb.Tcs.CodewordNeOfSuppInterSingleton

/-!
# two_four_code_sync_single_coord

Topic: information   Node: 8e232d17a89f

Provenance: formalization of a published result. Source: arXiv:2610.30613, Lemma 2.1

Let $\alpha$ be an alphabet with decidable equality and a distinguished element $0$. Let $\mathcal{C} \subseteq (\mathrm{Fin}\, n \to \alpha)$ be a code containing $0$ such that all distinct codewords have Hamming distance in $\{2, 4\}$. If $x \in \mathcal{C}$ has support cardinality $(\mathrm{codeword\_supp}(x)).\mathrm{card} = 2$, $y \in \mathcal{C}$ has support cardinality $(\mathrm{codeword\_supp}(y)).\mathrm{card} = 2$ or $(\mathrm{codeword\_supp}(y)).\mathrm{card} = 4$, and $\mathrm{codeword\_supp}(x) \cap \mathrm{codeword\_supp}(y) = \{i\}$, then $x_i = y_i$.
-/

/-- Single-coordinate synchronization: in a {2,4}-distance code containing 0, codewords of weight 2 and weight in {2,4} intersecting at a single coordinate must agree at that coordinate. -/
theorem two_four_code_sync_single_coord
    {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (C : Set (Fin n → α))
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y = 2 ∨ hammingDist x y = 4)
    (_h0 : 0 ∈ C)
    (x y : Fin n → α)
    (hxC : x ∈ C) (hx_wt : (codeword_supp x).card = 2)
    (hyC : y ∈ C) (hy_wt : (codeword_supp y).card = 2 ∨ (codeword_supp y).card = 4)
    (i : Fin n)
    (h_inter : codeword_supp x ∩ codeword_supp y = {i}) :
    x i = y i := by
  have hne : x ≠ y := codeword_ne_of_supp_inter_singleton x y i hx_wt h_inter
  have hd := hC x hxC y hyC hne
  have heq := hammingDist_eq_of_codeword_supp_inter_singleton x y i h_inter
  rcases hy_wt with hy | hy
  · by_contra hxy
    simp only [hxy, if_false] at heq
    rw [hx_wt, hy] at heq
    omega
  · by_contra hxy
    simp only [hxy, if_false] at heq
    rw [hx_wt, hy] at heq
    omega
