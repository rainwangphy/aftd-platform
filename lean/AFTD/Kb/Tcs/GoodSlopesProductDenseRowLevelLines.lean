import AFTD.Prelude
import AFTD.Kb.Tcs.GoodSlopesFiberProductSaturation

/-!
# good_slopes_product_dense_row_level_lines

Topic: combinatorics   Node: ae52e2c02131

Provenance: helper lemma. Dense-row fiber classification for OP-1027.

For a pq-point subset of the product of two finite-field planes, if at least (q+1)/2 second-coordinate directions are good in a fixed row, the first-coordinate form has p levels of q points and each level projects to a line in the second-coordinate plane, assuming the stated q-point direction classification.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_product_dense_row_level_lines
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    (p q : ℕ) (hp : Fintype.card K = p) (hq : Fintype.card L = q)
    (hdirL : ∀ T : Finset (L × L), T.card = q →
      (∃ G : Finset L, (q+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2 + b*z.1) T) →
      (∃ x : L, ∀ z ∈ T, z.1 = x) ∨ (∃ b t : L, ∀ z ∈ T, z.2 + b*z.1 = t))
    (S : Finset ((K × L) × (K × L))) (hcard : S.card = p*q) (a : K)
    (hdense : (q+1)/2 ≤ ((Finset.univ : Finset L).filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S).card) :
    ∀ t : K, (S.filter fun z => z.2.1 + a*z.1.1 = t).card = q ∧
      ((∃ x : L, ∀ z ∈ S, z.2.1 + a*z.1.1 = t → z.1.2 = x) ∨
       (∃ b v : L, ∀ z ∈ S, z.2.1 + a*z.1.1 = t → z.2.2 + b*z.1.2 = v)) := by
  classical
  let G : Finset L := Finset.univ.filter fun b => b ≠ 0 ∧
      Set.InjOn (fun z : ((K × L) × (K × L)) => (z.2.1 + a*z.1.1, z.2.2 + b*z.1.2)) S
  have hqpos : 1 < q := by rw [← hq]; exact Fintype.one_lt_card
  have hn : 0 < (q+1)/2 := Nat.div_pos (by omega) (by decide)
  have hGpos : 0 < G.card := lt_of_lt_of_le hn hdense
  obtain ⟨b0,hb0⟩ := Finset.card_pos.mp hGpos
  have hb0good := (Finset.mem_filter.mp hb0).2.2
  let F (z : ((K × L) × (K × L))) := z.2.1 + a*z.1.1
  let H (z : ((K × L) × (K × L))) := z.2.2 + b0*z.1.2
  have hS : S.card = Fintype.card K * Fintype.card L := by simpa [hp,hq] using hcard
  have hsat := good_slopes_fiber_product_saturation S F H hS hb0good
  intro t
  let A := S.filter fun z => F z = t
  have hA : A.card = q := by simpa [A,hq] using (hsat t).1
  refine ⟨hA, ?_⟩
  let π (z : ((K × L) × (K × L))) : L × L := (z.1.2,z.2.2)
  have hπ : Set.InjOn π A := by
    intro u hu v hv heq
    have huA := Finset.mem_filter.mp hu
    have hvA := Finset.mem_filter.mp hv
    apply hb0good huA.1 hvA.1
    apply Prod.ext
    · exact huA.2.trans hvA.2.symm
    · have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      dsimp [π] at hx hy
      dsimp [H]
      rw [hx,hy]
  let T : Finset (L × L) := A.image π
  have hT : T.card = q := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hπ, hA]
  have hgood : ∀ b ∈ G, Set.InjOn (fun z : L × L => z.2+b*z.1) T := by
    intro b hb u hu v hv heq
    have hbGood := (Finset.mem_filter.mp hb).2.2
    obtain ⟨u,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v,hv0,rfl⟩ := Finset.mem_image.mp hv
    apply congrArg π
    have huA := Finset.mem_filter.mp hu0
    have hvA := Finset.mem_filter.mp hv0
    apply hbGood huA.1 hvA.1
    apply Prod.ext
    · exact huA.2.trans hvA.2.symm
    · exact heq
  have hh := hdirL T hT ⟨G,hdense,hgood⟩
  rcases hh with ⟨x,hx⟩ | ⟨b,v,hv⟩
  · left
    refine ⟨x, ?_⟩
    intro z hz ht
    have hmem : π z ∈ T := Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,ht⟩,rfl⟩
    exact hx _ hmem
  · right
    refine ⟨b,v, ?_⟩
    intro z hz ht
    have hmem : π z ∈ T := Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,ht⟩,rfl⟩
    exact hv _ hmem
