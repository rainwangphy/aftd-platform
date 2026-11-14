import AFTD.Prelude
import AFTD.Kb.Tcs.Zycle
import AFTD.Kb.Tcs.IsHypergraphHom
import AFTD.Kb.Tcs.PairDigraphAdj
import AFTD.Kb.Tcs.IsThreeUniform

/-!
# zycle_hom_implies_closed_walk

Topic: combinatorics   Node: 29dfa93f1edd

Provenance: formalization of a published result. Source: arXiv:2611.16654 Lemma 2.3

If f : ZMod ℓ × Fin 2 → α is a hypergraph homomorphism is_hypergraph_hom from the zycle Z_ℓ to a 3-uniform hypergraph G : Finset (Finset α), then there exists a closed walk W : ZMod ℓ → Finset α of length ℓ in the pair digraph of G satisfying pair_digraph_adj G (W i) (W (i + 1)) for all i in ZMod ℓ.
-/

private lemma zycle_hom_implies_closed_walk_card_three_ne {α : Type*} [DecidableEq α] {a b c : α}
    (h : ({a,b,c} : Finset α).card = 3) : a ≠ b := by
  intro hab
  have key : ({a,b,c} : Finset α) = {a,c} := by ext x; simp [hab]
  rw [key] at h
  have := Finset.card_le_two (α := α) (a := a) (b := c)
  omega

/-- A homomorphism from Z_ℓ to a 3-uniform hypergraph G implies a closed walk of length ℓ in D(G). -/
theorem zycle_hom_implies_closed_walk {α : Type*} [DecidableEq α]
    (ℓ : ℕ) [NeZero ℓ] (G : Finset (Finset α)) (hG : is_three_uniform G)
    (f : ZMod ℓ × Fin 2 → α) (hf : is_hypergraph_hom (zycle ℓ) G f) :
    ∃ W : ZMod ℓ → Finset α, ∀ i : ZMod ℓ, pair_digraph_adj G (W i) (W (i + 1)) := by
  classical
  have himg1 : ∀ i : ZMod ℓ, Finset.image f ({(i,0),(i,1),(i+1,0)} : Finset (ZMod ℓ × Fin 2))
      = ({f (i,0), f (i,1), f (i+1,0)} : Finset α) := by
    intro i
    ext x; simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a, h1 | h1 | h1, hx⟩
      · subst h1; exact Or.inl hx.symm
      · subst h1; exact Or.inr (Or.inl hx.symm)
      · subst h1; exact Or.inr (Or.inr hx.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨(i,0), Or.inl rfl, rfl⟩
      · exact ⟨(i,1), Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨(i+1,0), Or.inr (Or.inr rfl), rfl⟩
  have himg2 : ∀ i : ZMod ℓ, Finset.image f ({(i,0),(i,1),(i+1,1)} : Finset (ZMod ℓ × Fin 2))
      = ({f (i,0), f (i,1), f (i+1,1)} : Finset α) := by
    intro i
    ext x; simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a, h1 | h1 | h1, hx⟩
      · subst h1; exact Or.inl hx.symm
      · subst h1; exact Or.inr (Or.inl hx.symm)
      · subst h1; exact Or.inr (Or.inr hx.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨(i,0), Or.inl rfl, rfl⟩
      · exact ⟨(i,1), Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨(i+1,1), Or.inr (Or.inr rfl), rfl⟩
  have hmem1 : ∀ i : ZMod ℓ, ({(i,0),(i,1),(i+1,0)} : Finset (ZMod ℓ × Fin 2)) ∈ zycle ℓ := by
    intro i
    simp only [zycle]
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ i, by simp⟩
  have hmem2 : ∀ i : ZMod ℓ, ({(i,0),(i,1),(i+1,1)} : Finset (ZMod ℓ × Fin 2)) ∈ zycle ℓ := by
    intro i
    simp only [zycle]
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ i, by simp⟩
  have hG1 : ∀ i : ZMod ℓ, ({f (i,0), f (i,1), f (i+1,0)} : Finset α) ∈ G := by
    intro i; rw [← himg1 i]; exact hf _ (hmem1 i)
  have hG2 : ∀ i : ZMod ℓ, ({f (i,0), f (i,1), f (i+1,1)} : Finset α) ∈ G := by
    intro i; rw [← himg2 i]; exact hf _ (hmem2 i)
  have hcard1 : ∀ i : ZMod ℓ, ({f (i,0), f (i,1), f (i+1,0)} : Finset α).card = 3 :=
    fun i => hG _ (hG1 i)
  have hcard2 : ∀ i : ZMod ℓ, ({f (i,0), f (i,1), f (i+1,1)} : Finset α).card = 3 :=
    fun i => hG _ (hG2 i)
  refine ⟨fun i => ({f (i,0), f (i,1)} : Finset α), ?_⟩
  intro i
  rw [pair_digraph_adj]
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.card_pair
    exact zycle_hom_implies_closed_walk_card_three_ne (hcard1 i)
  · apply Finset.card_pair
    exact zycle_hom_implies_closed_walk_card_three_ne (hcard1 (i+1))
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · rw [show (({f (i,0), f (i,1)} : Finset α) ∪ {f (i+1,0)}) = {f (i,0), f (i,1), f (i+1,0)} from by ext x; simp]
      exact hG1 i
    · rw [show (({f (i,0), f (i,1)} : Finset α) ∪ {f (i+1,1)}) = {f (i,0), f (i,1), f (i+1,1)} from by ext x; simp]
      exact hG2 i
