import AFTD.Prelude
import AFTD.Kb.Tcs.HasFractionalSymmetricChainDecomposition
import AFTD.Kb.Tcs.YoungLattice
import AFTD.Kb.Tcs.YoungLatticeRank
import AFTD.Kb.Tcs.YoungLatticePartialOrder
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# young_lattice_one_fractional_scd

Topic: combinatorics   Node: dcae512c55f7

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7.4

For any positive integer n ≥ 1, the Young lattice L(1, n) admits a fractional symmetric chain decomposition.
-/

open scoped Classical BigOperators in
lemma young_lattice_one_fractional_scd_cells_eq (n : ℕ) (μ : YoungLattice 1 n) :
    μ.val.cells = (Finset.range μ.val.cells.card).image (fun j => (0, j)) := by
  apply Finset.Subset.antisymm
  · intro c hc
    have hc1 : c.1 = 0 := by have h := μ.2 c hc; omega
    have hceq : (0, c.2) = c := by ext <;> simp [hc1]
    have hc' : (0, c.2) ∈ μ.val.cells := by rwa [hceq]
    have hcard : ((Finset.range (c.2+1)).image (fun j => (0, j))).card = c.2 + 1 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b h; simpa using h
    have hsub : (Finset.range (c.2+1)).image (fun j => (0, j)) ⊆ μ.val.cells := by
      intro d hd
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      rw [Finset.mem_range] at hj
      exact μ.val.isLowerSet (a := (0, c.2)) (b := (0, j)) (by simpa using Nat.le_of_lt_succ hj) hc'
    have hle : c.2 + 1 ≤ μ.val.cells.card := by
      have := Finset.card_le_card hsub
      omega
    exact Finset.mem_image.mpr ⟨c.2, Finset.mem_range.mpr (by omega), by ext <;> simp [hc1]⟩
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_range] at hj
    by_contra hnot
    have hsub : μ.val.cells ⊆ (Finset.range j).image (fun i => (0, i)) := by
      intro d hd
      have hd1 : d.1 = 0 := by have h := μ.2 d hd; omega
      have hdeq : (0, d.2) = d := by ext <;> simp [hd1]
      have hd' : (0, d.2) ∈ μ.val.cells := by rwa [hdeq]
      have hd2 : d.2 < j := by
        by_contra hge
        exact hnot (μ.val.isLowerSet (a := (0, d.2)) (b := (0, j)) (by simpa using Nat.le_of_not_gt hge) hd')
      exact Finset.mem_image.mpr ⟨d.2, Finset.mem_range.mpr hd2, by ext <;> simp [hd1]⟩
    have hcard : ((Finset.range j).image (fun i => (0, i))).card = j := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b h; simpa using h
    have := Finset.card_le_card hsub
    omega

lemma young_lattice_one_fractional_scd_card_le (n : ℕ) (μ : YoungLattice 1 n) :
    μ.val.cells.card ≤ n := by
  have h := young_lattice_one_fractional_scd_cells_eq n μ
  have hsub : Finset.range μ.val.cells.card ⊆ Finset.range n := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    have hmem : (0,j) ∈ μ.val.cells := by
      rw [h]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    have := μ.2 (0,j) hmem
    omega
  have := Finset.card_le_card hsub
  simpa using this

lemma young_lattice_one_fractional_scd_rank_formula (n : ℕ) (μ : YoungLattice 1 n) :
    young_lattice_rank 1 n μ = 2 * (μ.val.cells.card : ℤ) - n := by
  simp [young_lattice_rank]

lemma young_lattice_one_fractional_scd_rank_inj (n : ℕ) (x y : YoungLattice 1 n)
    (h : young_lattice_rank 1 n x = young_lattice_rank 1 n y) : x = y := by
  have hx := young_lattice_one_fractional_scd_rank_formula n x
  have hy := young_lattice_one_fractional_scd_rank_formula n y
  have hcard : x.val.cells.card = y.val.cells.card := by omega
  apply Subtype.ext
  apply YoungDiagram.ext
  rw [young_lattice_one_fractional_scd_cells_eq n x,
      young_lattice_one_fractional_scd_cells_eq n y, hcard]

def young_lattice_one_fractional_scd_cells (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range j).image (fun i => (0,i))

lemma young_lattice_one_fractional_scd_cells_isLowerSet (j : ℕ) :
    IsLowerSet (↑(young_lattice_one_fractional_scd_cells j) : Set (ℕ×ℕ)) := by
  intro a b hba ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  rw [Finset.mem_range] at hi
  have hb1 : b.1 = 0 := by have := hba.1; omega
  have hb2 : b.2 < j := by have := hba.2; omega
  exact Finset.mem_image.mpr ⟨b.2, Finset.mem_range.mpr hb2, by ext <;> simp [hb1]⟩

def young_lattice_one_fractional_scd_diagram (j : ℕ) : YoungDiagram :=
  ⟨young_lattice_one_fractional_scd_cells j, young_lattice_one_fractional_scd_cells_isLowerSet j⟩

def young_lattice_one_fractional_scd_elem (n j : ℕ) (hj : j ≤ n) : YoungLattice 1 n :=
  ⟨young_lattice_one_fractional_scd_diagram j, by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_range] at hi
    exact ⟨by omega, by omega⟩⟩

lemma young_lattice_one_fractional_scd_elem_card (n j : ℕ) (hj : j ≤ n) :
    (young_lattice_one_fractional_scd_elem n j hj).val.cells.card = j := by
  show (young_lattice_one_fractional_scd_cells j).card = j
  rw [young_lattice_one_fractional_scd_cells, Finset.card_image_of_injective]
  · simp
  · intro a b h; simpa using h

lemma young_lattice_one_fractional_scd_elem_rank (n j : ℕ) (hj : j ≤ n) :
    young_lattice_rank 1 n (young_lattice_one_fractional_scd_elem n j hj) = -n + 2 * (j : ℤ) := by
  rw [young_lattice_one_fractional_scd_rank_formula, young_lattice_one_fractional_scd_elem_card]
  ring

lemma young_lattice_one_fractional_scd_cover (n : ℕ) (x y : YoungLattice 1 n)
    (h : young_lattice_rank 1 n y = young_lattice_rank 1 n x + 2) : x ⋖ y := by
  have hx := young_lattice_one_fractional_scd_rank_formula n x
  have hy := young_lattice_one_fractional_scd_rank_formula n y
  have hcard : y.val.cells.card = x.val.cells.card + 1 := by omega
  have hsub : x.val.cells ⊆ y.val.cells := by
    rw [young_lattice_one_fractional_scd_cells_eq n x,
        young_lattice_one_fractional_scd_cells_eq n y, hcard]
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_range] at hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  have hle : x ≤ y := hsub
  have hne : x ≠ y := by
    intro heq
    have : x.val.cells.card = y.val.cells.card := by rw [heq]
    omega
  refine ⟨lt_of_le_of_ne hle hne, ?_⟩
  intro z hxz hzy
  have hsub_xz : x.val.cells ⊆ z.val.cells := hxz.1
  have hsub_zy : z.val.cells ⊆ y.val.cells := hzy.1
  have hcx_lt : x.val.cells.card < z.val.cells.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub_xz, ?_⟩
    intro heq
    apply hxz.2
    show z ≤ x
    exact heq.ge
  have hcz_le : z.val.cells.card ≤ y.val.cells.card := Finset.card_le_card hsub_zy
  have hczcard : z.val.cells.card = y.val.cells.card := by omega
  have hzeq : z = y := by
    apply Subtype.ext
    apply YoungDiagram.ext
    rw [young_lattice_one_fractional_scd_cells_eq n z,
        young_lattice_one_fractional_scd_cells_eq n y, hczcard]
  rw [hzeq] at hzy
  exact lt_irrefl y hzy

/-- For any n ≥ 1, the Young lattice L(1, n) admits a fractional symmetric chain decomposition. -/
theorem young_lattice_one_fractional_scd (n : ℕ) (hn : 1 ≤ n) :
    has_fractional_symmetric_chain_decomposition (young_lattice_rank 1 n) := by
  classical
  refine ⟨({Set.univ} : Finset (Set (YoungLattice 1 n))), (fun _ => 1), ?_, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_singleton] at hC
    rw [hC]
    refine ⟨(n : ℤ), ?_, ?_, ?_⟩
    · intro m
      constructor
      · rintro ⟨x, -, hx⟩
        have hcle := young_lattice_one_fractional_scd_card_le n x
        refine ⟨(x.val.cells.card : ℤ), by omega, by omega, ?_⟩
        rw [young_lattice_one_fractional_scd_rank_formula] at hx
        omega
      · rintro ⟨j, hj0, hjn, rfl⟩
        have hk : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
        have hkn : j.toNat ≤ n := by omega
        refine ⟨young_lattice_one_fractional_scd_elem n j.toNat hkn, Set.mem_univ _, ?_⟩
        rw [young_lattice_one_fractional_scd_elem_rank]
        omega
    · intro x _ y _ hxy
      exact young_lattice_one_fractional_scd_rank_inj n x y hxy
    · intro x _ y _ hxy
      exact young_lattice_one_fractional_scd_cover n x y hxy
  · intro C hC
    simp
  · intro x
    have hfilt : ({Set.univ} : Finset (Set (YoungLattice 1 n))).filter (fun C => x ∈ C) = {Set.univ} := by
      ext C
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨h, -⟩; exact h
      · intro h; subst h; exact ⟨rfl, Set.mem_univ x⟩
    rw [hfilt]
    simp
