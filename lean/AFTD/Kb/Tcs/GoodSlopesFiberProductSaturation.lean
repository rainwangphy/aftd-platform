import AFTD.Prelude

/-!
# good_slopes_fiber_product_saturation

Topic: combinatorics   Node: 8c6bdea9382a

Provenance: helper lemma. Product-fiber saturation step for OP-1027.

If a finite set has as many points as a finite product and the pair of coordinate maps is injective, each first-coordinate fiber has the full size of the second coordinate and contains one point with each second coordinate.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_fiber_product_saturation
    {α ι κ : Type*} [DecidableEq α] [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ]
    (S : Finset α) (f : α → ι) (g : α → κ)
    (hcard : S.card = Fintype.card ι * Fintype.card κ)
    (hinj : Set.InjOn (fun z => (f z, g z)) S) :
    ∀ i : ι, (S.filter fun z => f z = i).card = Fintype.card κ ∧
      ∀ k : κ, ∃ z ∈ S, f z = i ∧ g z = k := by
  classical
  have hP : S.image (fun z => (f z,g z)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_prod]
  have hall : ∀ i : ι, ∀ k : κ, ∃ z ∈ S, f z = i ∧ g z = k := by
    intro i k
    have hk : (i,k) ∈ S.image (fun z => (f z,g z)) := by
      rw [hP]; exact Finset.mem_univ _
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hk
    exact ⟨z,hz,congrArg Prod.fst he,congrArg Prod.snd he⟩
  intro i
  let A := S.filter fun z => f z = i
  have hginj : Set.InjOn g A := by
    intro z hz z' hz' heq
    have hza := Finset.mem_filter.mp hz
    have hz'a := Finset.mem_filter.mp hz'
    apply hinj hza.1 hz'a.1
    exact Prod.ext (hza.2.trans hz'a.2.symm) heq
  have hG : A.image g = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro k
    obtain ⟨z,hz,hf,hg⟩ := hall i k
    exact Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hf⟩,hg⟩
  constructor
  · calc
      (S.filter fun z => f z = i).card = (A.image g).card := (Finset.card_image_of_injOn hginj).symm
      _ = Fintype.card κ := by rw [hG, Finset.card_univ]
  · exact hall i
