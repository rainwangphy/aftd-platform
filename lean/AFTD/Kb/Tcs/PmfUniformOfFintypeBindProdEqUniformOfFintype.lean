import AFTD.Prelude
import AFTD.Kb.Tcs.CslibProbabilityPMFUniformOfFintypeMapEquiv

/-!
# pmf_uniformOfFintype_bind_prod_eq_uniformOfFintype

Topic: randomness   Node: ebcb07b9c803

Provenance: helper lemma. folklore

Let α and β be finite nonempty types. Then the sequential monadic bind of the uniform distribution on α with the uniform distribution on β, given by (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (fun b => (a, b))), is equal to the uniform distribution on the product type PMF.uniformOfFintype (α × β).
-/

/-- Sampling independently and uniformly from two finite types yields the uniform distribution on their Cartesian product. -/
theorem pmf_uniformOfFintype_bind_prod_eq_uniformOfFintype {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (fun b => (a, b))) = PMF.uniformOfFintype (α × β) := by
  classical
  ext ⟨x, y⟩
  rw [PMF.bind_apply]
  rw [tsum_eq_single x]
  · rw [PMF.uniformOfFintype_apply, PMF.map_apply]
    rw [tsum_eq_single y]
    · rw [if_pos rfl, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
      rw [Fintype.card_prod]
      push_cast
      rw [ENNReal.mul_inv (by simp) (by simp)]
    · intro b' hb'
      split_ifs with h
      · exfalso
        cases h
        exact hb' rfl
      · rfl
  · intro a ha
    have hzero : ((PMF.uniformOfFintype β).map (fun b => (a, b))) (x, y) = 0 := by
      rw [PMF.map_apply]
      refine (tsum_congr fun b => ?_).trans tsum_zero
      split_ifs with h
      · exfalso
        cases h
        exact ha rfl
      · rfl
    rw [hzero, mul_zero]
