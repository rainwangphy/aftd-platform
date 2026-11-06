import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoDeviationWelfareNondecreasing
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectTwoEqualWelfareDeviationStructure
import AFTD.Kb.GameTheoryEconomics.MaxcutOneDoubleDefectStrictWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutOneDoubleDefectNewEdgeUnique
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_one_double_defect_deviation_decreases

Topic: equilibria   Node: 8b20ed80f975

Provenance: helper lemma. Structural potential argument for the strong-equilibrium existence question OP-85; experiment 16416.

If a coloring has monochromatic degree at most two with at most one vertex of degree two, every strong deviation stays in that class and strictly reduces the number of monochromatic edges.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
private theorem in582_one_double_defect_class_preserved
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hbound : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hunique : ∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    (∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card ≤ 2) ∧
    (∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card = 2 → u = v) := by
  classical
  let M (ρ : V → Fin k) (v : V) : Finset V := Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v
  have hbound' : ∀ v, (M σ v).card ≤ 2 := hbound
  have hunique' : ∀ u v, (M σ u).card = 2 → (M σ v).card = 2 → u = v := hunique
  have hCpost : ∀ v ∈ C, (M τ v).card ≤ 1 := by
    intro v hv
    have ho := maxcut_utility_add_monochromatic_card G σ v
    have hn := maxcut_utility_add_monochromatic_card G τ v
    have hg := hdev.2.2 v hv
    have hb := hbound' v
    change maxcut_utility G σ v + (M σ v).card = G.degree v at ho
    change maxcut_utility G τ v + (M τ v).card = G.degree v at hn
    omega
  by_cases hnew : ∃ a b : V, G.Adj a b ∧ τ a = τ b ∧ σ a ≠ σ b
  · obtain ⟨a,b,hab,ht,hs⟩ := hnew
    have hchange : a ∈ C ∨ b ∈ C := by
      by_contra hh
      have ha : a ∉ C := fun h => hh (Or.inl h)
      have hb : b ∉ C := fun h => hh (Or.inr h)
      apply hs
      calc
        σ a = τ a := (hdev.2.1 a ha).symm
        _ = τ b := ht
        _ = σ b := hdev.2.1 b hb
    have hnorm : ∃ u w : V, u ∈ C ∧ G.Adj u w ∧ τ u = τ w ∧ σ u ≠ σ w := by
      rcases hchange with ha | hb
      · exact ⟨a,b,ha,hab,ht,hs⟩
      · exact ⟨b,a,hb,hab.symm,ht.symm,Ne.symm hs⟩
    obtain ⟨u,w,hu,huadj,hut,huneq⟩ := hnorm
    have huold : (M σ u).card = 2 := by
      have hpos : 0 < (M τ u).card := by
        apply Finset.card_pos.mpr
        exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huadj, hut.symm⟩⟩
      have ho := maxcut_utility_add_monochromatic_card G σ u
      have hn := maxcut_utility_add_monochromatic_card G τ u
      have hg := hdev.2.2 u hu
      have hb := hbound' u
      change maxcut_utility G σ u + (M σ u).card = G.degree u at ho
      change maxcut_utility G τ u + (M τ u).card = G.degree u at hn
      omega
    have houtold : ∀ x, x ∉ C → (M σ x).card ≤ 1 := by
      intro x hx
      have hb := hbound' x
      by_contra hh
      have heq : (M σ x).card = 2 := by omega
      have hxu := hunique' x u heq huold
      subst x
      exact hx hu
    have hnewshape : ∀ x y, x ∉ C → G.Adj x y → τ x = τ y → σ x ≠ σ y → x = w ∧ y = u := by
      intro x y hx hxy htxy hsxy
      have he := maxcut_one_double_defect_new_edge_unique G σ τ C hbound hunique hdev x y u w hxy htxy hsxy huadj hut huneq
      rcases he with ⟨hxu,hyw⟩ | ⟨hxw,hyu⟩
      · subst x
        exact (hx hu).elim
      · exact ⟨hxw,hyu⟩
    have hsmall : ∀ x, x ≠ w → (M τ x).card ≤ 1 := by
      intro x hxw
      by_cases hx : x ∈ C
      · exact hCpost x hx
      · have hsub : M τ x ⊆ M σ x := by
          intro y hy
          have hy' : G.Adj x y ∧ τ y = τ x := (Finset.mem_filter.mp hy).2
          by_cases hsxy : σ x = σ y
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy'.1, hsxy.symm⟩
          · have hh := hnewshape x y hx hy'.1 hy'.2.symm hsxy
            exact (hxw hh.1).elim
        exact le_trans (Finset.card_le_card hsub) (houtold x hx)
    have hall : ∀ x, (M τ x).card ≤ 2 := by
      intro x
      by_cases hxw : x = w
      · subst x
        by_cases hw : w ∈ C
        · have := hCpost w hw
          omega
        · have hsub : M τ w ⊆ insert u (M σ w) := by
            intro y hy
            have hy' : G.Adj w y ∧ τ y = τ w := (Finset.mem_filter.mp hy).2
            by_cases hsame : σ w = σ y
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy'.1, hsame.symm⟩)
            · have hh := hnewshape w y hw hy'.1 hy'.2.symm hsame
              simpa only [hh.2] using (Finset.mem_insert_self u (M σ w))
          have hc := Finset.card_le_card hsub
          have hi := Finset.card_insert_le u (M σ w)
          have ho := houtold w hw
          omega
      · have := hsmall x hxw
        omega
    refine ⟨hall, ?_⟩
    intro x y hx hy
    change (M τ x).card = 2 at hx
    change (M τ y).card = 2 at hy
    have hxw : x = w := by
      by_contra h
      have := hsmall x h
      omega
    have hyw : y = w := by
      by_contra h
      have := hsmall y h
      omega
    exact hxw.trans hyw.symm
  · have hsub : ∀ x, M τ x ⊆ M σ x := by
      intro x y hy
      have hy' : G.Adj x y ∧ τ y = τ x := (Finset.mem_filter.mp hy).2
      have hs : σ x = σ y := by
        by_contra hne
        exact hnew ⟨x,y,hy'.1,hy'.2.symm,hne⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy'.1, hs.symm⟩
    have hall : ∀ x, (M τ x).card ≤ 2 := by
      intro x
      exact le_trans (Finset.card_le_card (hsub x)) (hbound' x)
    refine ⟨hall, ?_⟩
    intro x y hx hy
    change (M τ x).card = 2 at hx
    change (M τ y).card = 2 at hy
    apply hunique' x y
    · have hs := Finset.card_le_card (hsub x)
      have hb := hbound' x
      omega
    · have hs := Finset.card_le_card (hsub y)
      have hb := hbound' y
      omega

theorem maxcut_one_double_defect_deviation_decreases
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hbound : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2)
    (hunique : ∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    (∑ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card) < (∑ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card) ∧
    (∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card ≤ 2) ∧
    (∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ τ w = τ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card = 2 → u = v) := by
  classical
  have hw := maxcut_one_double_defect_strict_welfare G σ τ C hbound hunique hdev
  have hc := in582_one_double_defect_class_preserved G σ τ C hbound hunique hdev
  have hsum (ρ : V → Fin k) :
      maxcut_welfare G ρ + (∑ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v).card) =
        ∑ v : V, G.degree v := by
    unfold maxcut_welfare
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => maxcut_utility_add_monochromatic_card G ρ v)
  have hσ := hsum σ
  have hτ := hsum τ
  exact ⟨by omega, hc.1, hc.2⟩
