import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_one_double_defect_new_edge_unique

Topic: equilibria   Node: cccbe9d27c14

Provenance: helper lemma. Coalitional incidence argument for the one-exception potential, experiment 16419.

Under a strong deviation from a profile with maximum defect two and at most one defect-two vertex, all newly monochromatic edges coincide as an undirected edge.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem maxcut_one_double_defect_new_edge_unique
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hbound : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hunique : ∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    ∀ a b c d : V,
      G.Adj a b → τ a = τ b → σ a ≠ σ b →
      G.Adj c d → τ c = τ d → σ c ≠ σ d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hnorm (a b : V) (hab : G.Adj a b) (ht : τ a = τ b) (hs : σ a ≠ σ b) :
      ∃ u v : V, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
        u ∈ C ∧ G.Adj u v ∧ τ v = τ u ∧
        (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 ∧
        (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card ≤ 1 := by
    have hon (u v : V) (hu : u ∈ C) (huv : G.Adj u v) (htuv : τ v = τ u) :
        (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 ∧
        (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card ≤ 1 := by
      have hpos : 0 < (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card := by
        apply Finset.card_pos.mpr
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv, htuv⟩⟩
      have ho := maxcut_utility_add_monochromatic_card G σ u
      have hn := maxcut_utility_add_monochromatic_card G τ u
      have hg := hdev.2.2 u hu
      have hb := hbound u
      omega
    by_cases ha : a ∈ C
    · obtain ⟨ho, hn⟩ := hon a b ha hab ht.symm
      exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, ha, hab, ht.symm, ho, hn⟩
    · have hb : b ∈ C := by
        by_contra hb
        apply hs
        calc
          σ a = τ a := (hdev.2.1 a ha).symm
          _ = τ b := ht
          _ = σ b := hdev.2.1 b hb
      obtain ⟨ho, hn⟩ := hon b a hb hab.symm ht
      exact ⟨b, a, Or.inr ⟨rfl, rfl⟩, hb, hab.symm, ht, ho, hn⟩
  intro a b c d hab ht hs hcd ht' hs'
  obtain ⟨u,v,huv,huC,hua,hut,huold,hunew⟩ := hnorm a b hab ht hs
  obtain ⟨x,y,hxy,hxC,hxa,hxt,hxold,hxnew⟩ := hnorm c d hcd ht' hs'
  have hux : u = x := hunique u x huold hxold
  subst x
  have hvy : v = y := by
    apply Finset.card_le_one.mp hunew
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hua, hut⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hxa, hxt⟩
  subst y
  rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
