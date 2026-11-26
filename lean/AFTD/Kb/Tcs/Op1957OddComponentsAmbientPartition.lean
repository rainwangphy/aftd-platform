import AFTD.Prelude
import AFTD.Kb.Tcs.OddComponentsGroupIntoExactly

/-!
# op1957_odd_components_ambient_partition

Topic: graphs   Node: 1cd466c543d4

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Odd components ambient partition.
-/

set_option maxHeartbeats 2000000

theorem op1957_odd_components_ambient_partition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (U : Finset V) (s : ℕ)
    (hs : 1 ≤ s) (hodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hpar : U.card % 2 = s % 2) :
    ∃ F : Fin s → Finset V,
      (∀ i, F i ⊆ U ∧ Odd (F i).card) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j) ∧
        (∀ u ∈ F i, ∀ v ∈ F j, ¬ G.Adj u v)) ∧
      (Finset.univ.biUnion F = U) := by
  classical
  let H := G.induce {v | v ∈ U}
  obtain ⟨f,hfodd,hfanti⟩ := odd_components_group_into_exactly H s hs hodd (by simpa using hpar)
  let Q : Fin s → Finset {v // v ∈ U} := fun i => Finset.univ.filter (fun v => f v=i)
  let F : Fin s → Finset V := fun i => (Q i).map (⟨Subtype.val, Subtype.val_injective⟩ : {v // v ∈ U} ↪ V)
  have hQ : ∀ i (v : {v // v ∈ U}), v ∈ Q i ↔ f v=i := by
    intro i v
    simp [Q]
  refine ⟨F,?_,?_,?_⟩
  · intro i
    constructor
    · intro v hv
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hv
      exact u.property
    · simpa [F,Q] using hfodd i
  · intro i j hij
    constructor
    · apply Finset.disjoint_left.mpr
      intro v hvi hvj
      obtain ⟨u,hui,huv⟩ := Finset.mem_map.mp hvi
      obtain ⟨w,hwj,hwv⟩ := Finset.mem_map.mp hvj
      have huw : u=w := Subtype.ext (huv.trans hwv.symm)
      have hfi := (hQ i u).mp hui
      have hfj := (hQ j w).mp hwj
      apply hij
      rw [← hfi,← hfj,huw]
    · intro u hu v hv hadj
      obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨v',hv',rfl⟩ := Finset.mem_map.mp hv
      have hfu := (hQ i u').mp hu'
      have hfv := (hQ j v').mp hv'
      have hne : f u' ≠ f v' := by
        intro h
        apply hij
        rw [← hfu,← hfv,h]
      exact hfanti u' v' hne hadj
  · ext v
    constructor
    · intro hv
      obtain ⟨i,_,hvi⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hvi
      exact u.property
    · intro hv
      let u : {v // v ∈ U} := ⟨v,hv⟩
      refine Finset.mem_biUnion.mpr ⟨f u,Finset.mem_univ _,?_⟩
      exact Finset.mem_map.mpr ⟨u,(hQ (f u) u).mpr rfl,rfl⟩
