import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.PerfectMatchingOddAnticompleteGroupsBound

/-!
# factorcritical_odd_groups_deleted_vertex_bound

Topic: graphs   Node: c0286a99cac0

Provenance: helper lemma. OP-1957, factor-critical odd-group transfer

In a factor-critical graph, any family of disjoint odd groups anticomplete within L admits distinct matching partners outside L and outside a deleted vertex that is not in any group.
-/

set_option maxHeartbeats 3000000

theorem factorcritical_odd_groups_deleted_vertex_bound
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hcrit : is_k_factor_critical H 1)
    (J : Finset I) (F : I → Finset V) (L : Finset V)
    (hsub : ∀ i ∈ J, F i ⊆ L) (hodd : ∀ i ∈ J, Odd (F i).card)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ H.Adj u v)
    (z : V) (hz : ∀ i ∈ J, z ∉ F i) :
    J.card ≤ (((Finset.univ : Finset V) \ L).erase z).card := by
  classical
  obtain ⟨M, hM⟩ := hcrit {z} (Finset.card_singleton z)
  let W := ↥((({z} : Finset V) : Set V))ᶜ
  let e : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let F' : I → Finset W := fun i => Finset.univ.filter (fun v => v.val ∈ F i)
  let L' : Finset W := Finset.univ.filter (fun v => v.val ∈ L)
  have hfmap : ∀ i ∈ J, (F' i).map e = F i := by
    intro i hi
    ext v
    simp only [Finset.mem_map, F', Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hv
      have hvz : v ≠ z := fun h => hz i hi (h ▸ hv)
      let w : W := ⟨v, by simpa using hvz⟩
      exact ⟨w,hv,rfl⟩
  have hfcard : ∀ i ∈ J, (F' i).card = (F i).card := by
    intro i hi
    rw [← hfmap i hi, Finset.card_map]
  have hlmap : (((Finset.univ : Finset W) \ L').map e) = ((Finset.univ : Finset V) \ L).erase z := by
    ext v
    simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_erase, L', Finset.mem_filter]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨by simpa [e] using w.property, hw⟩
    · rintro ⟨hvz,hvL⟩
      let w : W := ⟨v, by simpa using hvz⟩
      exact ⟨w,hvL,rfl⟩
  have hsub' : ∀ i ∈ J, F' i ⊆ L' := by
    intro i hi v hv
    simp only [F',L',Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    exact hsub i hi hv
  have hodd' : ∀ i ∈ J, Odd (F' i).card := by
    intro i hi
    rw [hfcard i hi]
    exact hodd i hi
  have hdis' : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F' i) (F' j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro v hv1 hv2
    exact Finset.disjoint_left.mp (hdis i hi j hj hij) (Finset.mem_filter.mp hv1).2 (Finset.mem_filter.mp hv2).2
  have hanti' : ∀ i ∈ J, ∀ u ∈ F' i, ∀ v ∈ L', v ∉ F' i → ¬ (H.induce (({z} : Finset V) : Set V)ᶜ).Adj u v := by
    intro i hi u hu v hv hvnot huv
    apply hanti i hi u.val (Finset.mem_filter.mp hu).2 v.val (Finset.mem_filter.mp hv).2
    · intro hvF
      apply hvnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvF⟩
    · exact huv
  have hb := perfect_matching_odd_anticomplete_groups_bound _ M hM J F' L' hsub' hodd' hdis' hanti'
  rw [← Finset.card_map e, hlmap] at hb
  exact hb
