import AFTD.Prelude
import AFTD.Kb.Tcs.FactorcriticalAnticompleteOddComponentsBound
import AFTD.Kb.Tcs.GraphIsoOddComponentsCard
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_factorcritical_block_ambient_odd_components_bound

Topic: graphs   Node: 5a591bc902eb

Provenance: helper lemma. OP-1957: saturated-block boundary reduction, arXiv:2611.22690 and arXiv:1011.3384

In a finite factor-critical induced block, odd components of an ambient subset anticomplete to the rest of a containing set are bounded by block vertices outside the containing set, provided it contains another block vertex.
-/

theorem op1957_factorcritical_block_ambient_odd_components_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B U L : Finset V)
    (hcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hUB : U ⊆ B) (hUL : U ⊆ L)
    (z : V) (hzB : z ∈ B) (hzL : z ∈ L) (hzU : z ∉ U)
    (hanti : ∀ u ∈ U, ∀ v ∈ B ∩ L, v ∉ U → ¬ G.Adj u v) :
    (G.induce {v | v ∈ U}).oddComponents.ncard ≤ (B \ L).card := by
  classical
  let H := G.induce {v | v ∈ B}
  let Us : Finset {v // v ∈ B} := U.subtype (· ∈ B)
  let Ls : Finset {v // v ∈ B} := L.subtype (· ∈ B)
  have hUs : Us ⊆ Ls := by
    intro a ha
    have haU : a.val ∈ U := by simpa [Us] using ha
    have haL := hUL haU
    simpa [Ls] using haL
  let z' : {v // v ∈ B} := ⟨z,hzB⟩
  have hzLs : z' ∈ Ls := by simpa [Ls,z'] using hzL
  have hzUs : z' ∉ Us := by simpa [Us,z'] using hzU
  have ha : ∀ u ∈ Us, ∀ v ∈ Ls, v ∉ Us → ¬ H.Adj u v := by
    intro u hu v hv hvU hadj
    have huU : u.val ∈ U := by simpa [Us] using hu
    have hvL : v.val ∈ L := by simpa [Ls] using hv
    have hvU' : v.val ∉ U := by simpa [Us] using hvU
    exact hanti u.val huU v.val (Finset.mem_inter.mpr ⟨v.property,hvL⟩) hvU' hadj
  have hh := factorcritical_anticomplete_odd_components_bound H hcrit Us Ls hUs z' hzLs hzUs ha
  let e : (H.induce {v | v ∈ Us}) ≃g (G.induce {v | v ∈ U}) := {
    toFun := fun a => ⟨a.val.val, by simpa [Us] using a.property⟩
    invFun := fun a => ⟨⟨a.val,hUB a.property⟩, by simpa [Us] using a.property⟩
    left_inv := fun a => by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun a => by apply Subtype.ext; rfl
    map_rel_iff' := by rfl }
  have hiso := graph_iso_odd_components_card _ _ e
  have hset : (Finset.univ : Finset {v // v ∈ B}) \ Ls = (B \ L).subtype (· ∈ B) := by
    ext a
    simp [Ls,a.property]
  rw [hset,Finset.card_subtype] at hh
  have he : (B \ L).filter (· ∈ B) = B \ L := Finset.filter_true_of_mem (by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).1)
  rw [he] at hh
  rw [← hiso]
  exact hh
