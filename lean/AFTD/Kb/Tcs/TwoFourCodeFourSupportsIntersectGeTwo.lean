import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp
import AFTD.Kb.Tcs.FourSupports
import AFTD.Kb.Tcs.CodewordSuppDiffCardLeHammingDist

/-!
# two_four_code_four_supports_intersect_ge_two

Topic: information   Node: 69216f6fb4c4

Provenance: formalization of a published result. Source: arXiv:2610.30613 Lemma 3.3 -- Asymptotically Sharp Length Thresholds for q-ary Codes with Distances 2 and 4

Let $\alpha$ be an alphabet with decidable equality and a distinguished element $0$. Let $\mathcal{C} \subseteq (\mathrm{Fin}\, n \to \alpha)$ be a code containing the zero codeword $0$ such that any two distinct codewords have Hamming distance in $\{2, 4\}$. Let $\mathcal{H} = \mathrm{four\_supports}(\mathcal{C})$. For any two distinct supports $S, T \in \mathcal{H}$ with $S \ne T$, the cardinality of their intersection is at least 2: $2 \le (S \cap T).\mathrm{card}$.
-/

/-- Any two distinct four-supports in a code with distances in {2, 4} containing the zero word intersect in at least two coordinates. -/
theorem two_four_code_four_supports_intersect_ge_two
    {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (C : Set (Fin n → α))
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y = 2 ∨ hammingDist x y = 4)
    (_h0 : 0 ∈ C)
    (S T : Finset (Fin n))
    (hS : S ∈ four_supports C)
    (hT : T ∈ four_supports C)
    (hne : S ≠ T) :
    2 ≤ (S ∩ T).card := by
  rcases hS with ⟨x, hxC, hxcard, rfl⟩
  rcases hT with ⟨y, hyC, hycard, rfl⟩
  have hne_xy : x ≠ y := by
    rintro rfl
    exact hne rfl
  have hdist : hammingDist x y ≤ 4 := by
    rcases hC x hxC y hyC hne_xy with h2 | h4
    · omega
    · omega
  have hdiff := codeword_supp_diff_card_le_hammingDist x y
  have h1 := Finset.card_sdiff_add_card_inter (codeword_supp x) (codeword_supp y)
  have h2 := Finset.card_sdiff_add_card_inter (codeword_supp y) (codeword_supp x)
  rw [Finset.inter_comm (codeword_supp y)] at h2
  omega
