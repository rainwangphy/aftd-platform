import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesGridRectangle

/-!
# good_slopes_grid_single_slice_rectangle

Topic: elementary_number_theory   Node: 2b3893797954

Provenance: helper lemma. Counting assembly of the 15-, 21- and 35-point fiber bounds for OP-1027.

A nonempty set of at most seven cells whose nonempty first-coordinate slices have at least four cells, whose nonempty columns have at least two, and whose rows have either zero or three cells consists of one slice and a two-by-three rectangle.
-/

theorem good_slopes_grid_single_slice_rectangle
    {R C K : Type*} [DecidableEq R] [DecidableEq C] [DecidableEq K]
    (M : Finset (R × (C × K))) (hne : M.Nonempty) (hcard : M.card ≤ 7)
    (hslice : ∀ r, (M.filter fun p => p.1 = r).card = 0 ∨
      4 ≤ (M.filter fun p => p.1 = r).card)
    (hcols : ∀ k, (M.filter fun p => p.2.2 = k).card = 0 ∨
      2 ≤ (M.filter fun p => p.2.2 = k).card)
    (hrows : ∀ r c, (M.filter fun p => p.1 = r ∧ p.2.1 = c).card = 0 ∨
      (M.filter fun p => p.1 = r ∧ p.2.1 = c).card = 3) :
    ∃ (r : R) (A : Finset C) (T : Finset K),
      A.card = 2 ∧ T.card = 3 ∧ M = {r} ×ˢ (A ×ˢ T) := by
  classical
  let Rset := M.image Prod.fst
  have hsum : M.card = ∑ r ∈ Rset, (M.filter fun p => p.1 = r).card := by
    exact Finset.card_eq_sum_card_image Prod.fst M
  have hlow : ∀ r ∈ Rset, 4 ≤ (M.filter fun p => p.1 = r).card := by
    intro r hr
    obtain ⟨p,hp,hpr⟩ := Finset.mem_image.mp hr
    have hpos : 0 < (M.filter fun p => p.1 = r).card :=
      Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hpr⟩⟩
    rcases hslice r with h | h
    · omega
    · exact h
  have hRlow : 4 * Rset.card ≤ M.card := by
    rw [hsum]
    calc
      4 * Rset.card = ∑ _r ∈ Rset, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ r ∈ Rset, (M.filter fun p => p.1 = r).card := Finset.sum_le_sum hlow
  have hRne : Rset.Nonempty := hne.image Prod.fst
  have hRcard : Rset.card = 1 := by
    have hpos := Finset.card_pos.mpr hRne
    omega
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hRcard
  have hfirst : ∀ p ∈ M, p.1 = r := by
    intro p hp
    have hh : p.1 ∈ Rset := Finset.mem_image_of_mem _ hp
    rw [hr] at hh
    simpa using hh
  let B := M.image Prod.snd
  have hinj : Set.InjOn (fun p : R × (C × K) => p.2) M := by
    intro p hp q hq heq
    exact Prod.ext ((hfirst p hp).trans (hfirst q hq).symm) heq
  have hBC : B.card = M.card := Finset.card_image_of_injOn hinj
  have hBne : B.Nonempty := hne.image Prod.snd
  have hBcard : B.card ≤ 7 := by omega
  have hBcol (k : K) : (B.filter fun p => p.2 = k).card = 0 ∨
      2 ≤ (B.filter fun p => p.2 = k).card := by
    have heq : B.filter (fun p => p.2 = k) =
        (M.filter fun p => p.2.2 = k).image Prod.snd := by
      ext x
      simp only [B, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p,hp,rfl⟩,hx⟩
        exact ⟨p,⟨hp,hx⟩,rfl⟩
      · rintro ⟨p,⟨hp,hk⟩,rfl⟩
        exact ⟨⟨p,hp,rfl⟩,hk⟩
    rw [heq, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    exact hcols k
  have hBrow (c : C) : (B.filter fun p => p.1 = c).card = 0 ∨
      (B.filter fun p => p.1 = c).card = 3 := by
    have heq : B.filter (fun p => p.1 = c) =
        (M.filter fun p => p.1 = r ∧ p.2.1 = c).image Prod.snd := by
      ext x
      simp only [B, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p,hp,rfl⟩,hx⟩
        exact ⟨p,⟨hp,⟨hfirst p hp,hx⟩⟩,rfl⟩
      · rintro ⟨p,⟨hp,_,hc⟩,rfl⟩
        exact ⟨⟨p,hp,rfl⟩,hc⟩
    rw [heq, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    exact hrows r c
  obtain ⟨A,T,hA,hT,hrect⟩ := good_slopes_grid_rectangle B hBne hBcard hBrow hBcol
  refine ⟨r,A,T,hA,hT,?_⟩
  have hdecomp : M = {r} ×ˢ B := by
    ext p
    simp only [Finset.mem_product, Finset.mem_singleton]
    constructor
    · intro hp
      exact ⟨hfirst p hp,Finset.mem_image_of_mem _ hp⟩
    · rintro ⟨hpr,hh⟩
      obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hh
      have hpq : p = q := Prod.ext (hpr.trans (hfirst q hq).symm) hqp.symm
      simpa [hpq] using hq
  simpa [hrect] using hdecomp
