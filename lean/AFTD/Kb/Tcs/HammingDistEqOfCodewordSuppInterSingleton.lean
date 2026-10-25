import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# hammingDist_eq_of_codeword_supp_inter_singleton

Topic: information   Node: d278c4567cb3

Provenance: helper lemma. arXiv:2610.30613, Lemma 2.1

Let $\alpha$ be an alphabet with decidable equality and zero element $0$. For any two codewords $x, y : \mathrm{Fin}\, n \to \alpha$ whose supports intersect in a singleton $\mathrm{codeword\_supp}(x) \cap \mathrm{codeword\_supp}(y) = \{i\}$, their Hamming distance is $\mathrm{hammingDist}(x, y) = (\mathrm{codeword\_supp}(x)).\mathrm{card} + (\mathrm{codeword\_supp}(y)).\mathrm{card} - 2 + (\mathrm{if}\ x\ i = y\ i\ \mathrm{then}\ 0\ \mathrm{else}\ 1)$.
-/

/-- Hamming distance formula for two codewords whose supports intersect at a single coordinate. -/
theorem hammingDist_eq_of_codeword_supp_inter_singleton
    {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (x y : Fin n → α) (i : Fin n)
    (h_inter : codeword_supp x ∩ codeword_supp y = {i}) :
    hammingDist x y = (codeword_supp x).card + (codeword_supp y).card - 2 +
      (if x i = y i then 0 else 1) := by
  have hset : (Finset.univ.filter (fun j => x j ≠ y j) : Finset (Fin n))
      = (codeword_supp x \ codeword_supp y) ∪ (codeword_supp y \ codeword_supp x)
        ∪ ((codeword_supp x ∩ codeword_supp y).filter (fun j => x j ≠ y j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_inter, codeword_supp, ne_eq, not_not]
    constructor
    · intro h
      by_cases hx : x j = 0
      · by_cases hy : y j = 0
        · exact absurd (by rw [hx, hy]) h
        · exact Or.inl (Or.inr ⟨hy, hx⟩)
      · by_cases hy : y j = 0
        · exact Or.inl (Or.inl ⟨hx, hy⟩)
        · exact Or.inr ⟨⟨hx, hy⟩, h⟩
    · intro hmem
      rcases hmem with (⟨hx, hy⟩ | ⟨hy, hx⟩) | ⟨⟨_, _⟩, h⟩
      · exact fun e => hx (e.trans hy)
      · exact fun e => hy (e.symm.trans hx)
      · exact h
  have hi : i ∈ codeword_supp x ∩ codeword_supp y := by rw [h_inter]; simp
  have hcard_inter : (codeword_supp x ∩ codeword_supp y).card = 1 := by
    rw [h_inter]; simp
  have hAx : 1 ≤ (codeword_supp x).card :=
    Finset.card_pos.2 ⟨i, (Finset.mem_inter.mp hi).1⟩
  have hBy : 1 ≤ (codeword_supp y).card :=
    Finset.card_pos.2 ⟨i, (Finset.mem_inter.mp hi).2⟩
  have h1 : (codeword_supp x \ codeword_supp y).card = (codeword_supp x).card - 1 := by
    rw [Finset.card_sdiff, Finset.inter_comm, hcard_inter]
  have h2 : (codeword_supp y \ codeword_supp x).card = (codeword_supp y).card - 1 := by
    rw [Finset.card_sdiff, hcard_inter]
  have h3 : ((codeword_supp x ∩ codeword_supp y).filter (fun j => x j ≠ y j)).card
      = (if x i = y i then 0 else 1) := by
    rw [h_inter, Finset.filter_singleton]
    by_cases h : x i = y i <;> simp [h]
  have hCsub : ((codeword_supp x ∩ codeword_supp y).filter (fun j => x j ≠ y j))
      ⊆ codeword_supp x ∩ codeword_supp y := Finset.filter_subset _ _
  have hd12 : Disjoint (codeword_supp x \ codeword_supp y)
      (codeword_supp y \ codeword_supp x) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp ha).1
  have hd3 : Disjoint ((codeword_supp x \ codeword_supp y) ∪
      (codeword_supp y \ codeword_supp x))
      ((codeword_supp x ∩ codeword_supp y).filter (fun j => x j ≠ y j)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have hb' := hCsub hb
    rcases Finset.mem_union.mp ha with ha' | ha'
    · exact (Finset.mem_sdiff.mp ha').2 (Finset.mem_inter.mp hb').2
    · exact (Finset.mem_sdiff.mp ha').2 (Finset.mem_inter.mp hb').1
  have hcard : ((codeword_supp x \ codeword_supp y) ∪ (codeword_supp y \ codeword_supp x)
      ∪ ((codeword_supp x ∩ codeword_supp y).filter (fun j => x j ≠ y j))).card
      = (codeword_supp x).card - 1 + ((codeword_supp y).card - 1) +
        (if x i = y i then 0 else 1) := by
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12, h1, h2, h3]
  have hh : hammingDist x y
      = (Finset.univ.filter (fun j => x j ≠ y j) : Finset (Fin n)).card := rfl
  rw [hh, hset, hcard]
  omega
