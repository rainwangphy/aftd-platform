import AFTD.Prelude
import AFTD.Kb.Tcs.LineSyndrome
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.LineCubicNatFamilyExists
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.LineCubicBoundaryExtension

/-!
# open_problem_line_cubic_t_count

Topic: quantum   Node: ec1d7049bf56

Provenance: formalization of a published result. Source: arXiv:2610.01024, Appendix K.2, item 1

For every integer n ≥ 5, there exists a parity representation of the line cubic syndrome of cardinality 2n + 1.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace LineBuild
open Finset

noncomputable def target (n : ℕ) (A : Finset ℕ) : ZMod 2 := by
  classical
  exact if ∃ t, t+2 < n ∧ A = {t,t+1,t+2} then 1 else 0

theorem target_small (n : ℕ) (A : Finset ℕ) (hc : A.card < 3) : target n A = 0 := by
  unfold target
  apply if_neg
  rintro ⟨t,ht,rfl⟩
  have he : ({t,t+1,t+2} : Finset ℕ).card = 3 := by simp <;> omega
  omega

theorem target_three (n i j k : ℕ) (hk : k < n) (hj : j < k) (hi : i < j) :
    target n {i,j,k} = if j=i+1 ∧ k=i+2 then 1 else 0 := by
  unfold target
  have he : (∃ t, t+2 < n ∧ ({i,j,k} : Finset ℕ) = {t,t+1,t+2}) ↔
      j=i+1 ∧ k=i+2 := by
    constructor
    · rintro ⟨t,ht,he⟩
      have h1 : i ∈ ({t,t+1,t+2} : Finset ℕ) := he ▸ (by simp)
      have h2 : j ∈ ({t,t+1,t+2} : Finset ℕ) := he ▸ (by simp)
      have h3 : k ∈ ({t,t+1,t+2} : Finset ℕ) := he ▸ (by simp)
      have h4 : t ∈ ({i,j,k} : Finset ℕ) := he.symm ▸ (by simp)
      have h5 : t+2 ∈ ({i,j,k} : Finset ℕ) := he.symm ▸ (by simp)
      simp only [mem_insert,mem_singleton] at h1 h2 h3 h4 h5
      omega
    · rintro ⟨rfl,rfl⟩
      exact ⟨i,hk,rfl⟩
  simp only [he]

theorem good_moment (n : ℕ) (S : Finset (Finset ℕ)) (h : Good n S)
    (A : Finset ℕ) (hb : ∀ i ∈ A, i < n) (hc : 1 ≤ A.card ∧ A.card ≤ 3) :
    moment S A = target n A := by
  have hcases : A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨i,rfl⟩ := card_eq_one.mp hc
    rw [h.one i (hb i (by simp)), target_small n {i} (by simp)]
  · let f := A.orderEmbOfFin hc
    have he : A = {f 0,f 1} := by
      calc
        A = image f univ := (A.image_orderEmbOfFin_univ hc).symm
        _ = {f 0,f 1} := by
          rw [show (univ : Finset (Fin 2)) = {0,1} by decide]
          simp
    have hlt : f 0 < f 1 := f.strictMono (by decide)
    have hfn : f 1 < n := hb _ (A.orderEmbOfFin_mem hc 1)
    rw [he, h.two (f 1) hfn (f 0) hlt, target_small n {f 0,f 1}]
    simp <;> omega
  · let f := A.orderEmbOfFin hc
    have he : A = {f 0,f 1,f 2} := by
      calc
        A = image f univ := (A.image_orderEmbOfFin_univ hc).symm
        _ = {f 0,f 1,f 2} := by
          rw [show (univ : Finset (Fin 3)) = {0,1,2} by decide]
          simp
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have hfn : f 2 < n := hb _ (A.orderEmbOfFin_mem hc 2)
    rw [he, h.three (f 2) hfn (f 1) h12 (f 0) h01,
      target_three n (f 0) (f 1) (f 2) hfn h12 h01]

def pack (n : ℕ) (y : Finset ℕ) : Finset (Fin n) :=
  univ.filter (fun i => i.val ∈ y)

theorem pack_image (n : ℕ) (y : Finset ℕ) (hb : ∀ i ∈ y, i < n) :
    (pack n y).image Fin.val = y := by
  ext i
  simp only [mem_image, pack, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j,hj,rfl⟩; exact hj
  · intro hi; exact ⟨⟨i,hb i hi⟩,hi,rfl⟩

theorem pack_subset (n : ℕ) (A : Finset (Fin n)) (y : Finset ℕ) :
    A ⊆ pack n y ↔ A.image Fin.val ⊆ y := by
  simp only [subset_iff, pack, mem_filter, mem_univ, true_and]
  constructor
  · rintro h i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact h hj
  · intro h i hi
    exact h (mem_image.mpr ⟨i,hi,rfl⟩)

theorem target_fin (n : ℕ) (A : Finset (Fin n)) :
    target n (A.image Fin.val) = line_syndrome n A := by
  unfold target line_syndrome
  have he : (∃ t, t+2 < n ∧ A.image Fin.val = {t,t+1,t+2}) ↔
      ∃ i : Fin (n-2), A = {⟨i.val,by omega⟩,⟨i.val+1,by omega⟩,⟨i.val+2,by omega⟩} := by
    constructor
    · rintro ⟨t,ht,he⟩
      refine ⟨⟨t,by omega⟩,?_⟩
      apply Finset.image_injective Fin.val_injective
      simpa only [image_insert,image_singleton] using he
    · rintro ⟨i,rfl⟩
      refine ⟨i.val,by omega,?_⟩
      simp only [image_insert,image_singleton]
  simp only [he]

theorem good_repr (n : ℕ) (S : Finset (Finset ℕ)) (h : Good n S) :
    ∃ T : Finset (Finset (Fin n)), is_parity_repr T (line_syndrome n) ∧ T.card = 2*n+1 := by
  classical
  have hinj : Set.InjOn (pack n) (↑S : Set (Finset ℕ)) := by
    intro x hx y hy he
    have hh := congrArg (image Fin.val) he
    simpa only [pack_image n x (h.bounded x hx), pack_image n y (h.bounded y hy)] using hh
  refine ⟨S.image (pack n), ⟨?_,?_⟩,?_⟩
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hy
    obtain ⟨i,hi⟩ := h.nonempty z hz
    exact ⟨⟨i,h.bounded z hz i hi⟩,by simp [pack,hi]⟩
  · intro A hA
    rw [Finset.natCast_card_filter, sum_image hinj]
    have he : (∑ y ∈ S, if A ⊆ pack n y then (1 : ZMod 2) else 0) =
        moment S (A.image Fin.val) := by
      simp only [moment,chi,pack_subset]
    rw [he,good_moment n S h (A.image Fin.val),target_fin]
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact j.isLt
    · simpa only [card_image_of_injective _ Fin.val_injective] using hA
  · rw [card_image_of_injOn hinj, h.size]

end LineBuild

/-- Open Problem 4: whether the line family attains T-count 2n + 1 for every n ≥ 5. -/
theorem open_problem_line_cubic_t_count (n : ℕ) (hn : 5 ≤ n) : ∃ S : Finset (Finset (Fin n)), is_parity_repr S (line_syndrome n) ∧ S.card = 2 * n + 1 := by
  obtain ⟨S,hS⟩ := line_cubic_nat_family_exists n hn
  exact LineBuild.good_repr n S hS
