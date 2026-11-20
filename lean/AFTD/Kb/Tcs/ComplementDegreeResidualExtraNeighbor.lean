import AFTD.Prelude

/-!
# complement_degree_residual_extra_neighbor

Topic: graphs   Node: 81ff63b69493

Provenance: helper lemma. OP-1957 factor-critical forced-bridge shore construction.

In a residual of size d+3 with complement degree at most d, each endpoint of an edge has another neighbor in the residual.
-/

theorem complement_degree_residual_extra_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) (d : ℕ)
    (hR : R.card = d+3) (x z : V) (hx : x ∈ R) (hz : z ∈ R)
    (hxz : G.Adj x z) (hmax : ((Gᶜ).neighborFinset x).card ≤ d) :
    ∃ a ∈ R, a ≠ x ∧ a ≠ z ∧ G.Adj x a := by
  classical
  by_contra hn
  let T := (R.erase x).erase z
  have hxz_ne : x ≠ z := hxz.ne
  have hz' : z ∈ R.erase x := Finset.mem_erase.mpr ⟨hxz_ne.symm,hz⟩
  have hTcard : T.card = d+1 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hz', Finset.card_erase_of_mem hx]
    omega
  have hsub : T ⊆ (Gᶜ).neighborFinset x := by
    intro a ha
    have haz : a ≠ z := Finset.ne_of_mem_erase ha
    have ha' := Finset.mem_of_mem_erase ha
    have hax : a ≠ x := Finset.ne_of_mem_erase ha'
    have haR : a ∈ R := Finset.mem_of_mem_erase ha'
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨hax.symm, ?_⟩
    intro hadj
    exact hn ⟨a,haR,hax,haz,hadj⟩
  have hle := Finset.card_le_card hsub
  rw [hTcard] at hle
  omega
