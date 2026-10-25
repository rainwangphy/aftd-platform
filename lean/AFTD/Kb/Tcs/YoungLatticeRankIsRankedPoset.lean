import AFTD.Prelude
import AFTD.Kb.Tcs.IsRankedPoset
import AFTD.Kb.Tcs.YoungLattice
import AFTD.Kb.Tcs.YoungLatticeRank
import AFTD.Kb.Tcs.YoungLatticePartialOrder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# young_lattice_rank_is_ranked_poset

Topic: combinatorics   Node: 548d8d9bb78e

Provenance: helper lemma. arXiv:2610.24148, Section 2.7.4

For any m and n, the rank function young_lattice_rank makes L(m, n) into a ranked poset in the sense of is_ranked_poset.
-/

/-- The centered rank function makes the Young lattice L(m, n) into a ranked poset. -/
theorem young_lattice_rank_is_ranked_poset (m n : ℕ) : is_ranked_poset (young_lattice_rank m n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hsub : a.1.cells ⊆ b.1.cells := hab
    have hcard : a.1.cells.card ≤ b.1.cells.card := Finset.card_le_card hsub
    have hcardZ : (a.1.cells.card : ℤ) ≤ (b.1.cells.card : ℤ) := by exact_mod_cast hcard
    simp only [young_lattice_rank]
    linarith
  · intro a b hab
    have hab_le : a ≤ b := hab.1.le
    have hsub : a.1.cells ⊆ b.1.cells := hab_le
    have hnot_sub : ¬ b.1.cells ⊆ a.1.cells := hab.1.2
    have hne : (b.1.cells \ a.1.cells).Nonempty := Finset.sdiff_nonempty.mpr hnot_sub
    obtain ⟨x, hmin⟩ := Finset.exists_minimal hne
    have hx_b : x ∈ b.1.cells := (Finset.mem_sdiff.mp hmin.1).1
    have hx_not_a : x ∉ a.1.cells := (Finset.mem_sdiff.mp hmin.1).2
    let γcells : Finset (ℕ × ℕ) := insert x a.1.cells
    have hγlower : IsLowerSet (↑γcells : Set (ℕ × ℕ)) := by
      intro u v huv hu
      simp only [γcells, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu ⊢
      rcases hu with hu | hu
      · rw [hu] at huv
        by_cases hv : v ∈ a.1.cells
        · exact Or.inr hv
        · have hvb : v ∈ b.1.cells := b.1.isLowerSet huv (by simpa using hx_b)
          have hvd : v ∈ b.1.cells \ a.1.cells := Finset.mem_sdiff.mpr ⟨hvb, hv⟩
          have hxle : x ≤ v := hmin.2 hvd huv
          exact Or.inl (le_antisymm huv hxle)
      · exact Or.inr (a.1.isLowerSet huv hu)
    let γ : YoungDiagram := ⟨γcells, hγlower⟩
    have hγbox : ∀ c ∈ γ, c.1 < m ∧ c.2 < n := by
      intro c hc
      have hc' : c ∈ γcells := (YoungDiagram.mem_cells c).mpr hc
      rw [show γcells = insert x a.1.cells from rfl, Finset.mem_insert] at hc'
      rcases hc' with hcx | hc'
      · rw [hcx]
        exact b.2 x (by simpa using hx_b)
      · exact a.2 c (by simpa using hc')
    let γL : YoungLattice m n := ⟨γ, hγbox⟩
    have hle_aγ : a ≤ γL := by
      change a.1.cells ⊆ γL.1.cells
      intro c hc
      exact Finset.mem_insert_of_mem hc
    have hne_aγ : a ≠ γL := by
      intro h
      have hxmem : x ∈ γL.1.cells := by
        change x ∈ insert x a.1.cells
        exact Finset.mem_insert_self _ _
      rw [← congrArg (fun z : YoungLattice m n => z.1.cells) h] at hxmem
      exact hx_not_a hxmem
    have hlt_aγ : a < γL := lt_of_le_of_ne hle_aγ hne_aγ
    have hle_γb : γL ≤ b := by
      change γL.1.cells ⊆ b.1.cells
      intro c hc
      change c ∈ insert x a.1.cells at hc
      rcases Finset.mem_insert.mp hc with hcx | hc
      · rw [hcx]; exact hx_b
      · exact hsub hc
    have hγb : γL = b := by
      by_contra h
      exact hab.2 hlt_aγ (lt_of_le_of_ne hle_γb h)
    have hcells : b.1.cells = insert x a.1.cells := by
      have hh := congrArg (fun z : YoungLattice m n => z.1.cells) hγb
      simpa [γL, γ, γcells] using hh.symm
    have hcard : b.1.cells.card = a.1.cells.card + 1 := by
      rw [hcells, Finset.card_insert_of_notMem hx_not_a]
    have hcardZ : (b.1.cells.card : ℤ) = (a.1.cells.card : ℤ) + 1 := by exact_mod_cast hcard
    simp only [young_lattice_rank]
    linarith
  · intro a b
    rw [Int.modEq_iff_dvd]
    use ((b.1.cells.card : ℤ) - (a.1.cells.card : ℤ))
    simp only [young_lattice_rank]
    ring
