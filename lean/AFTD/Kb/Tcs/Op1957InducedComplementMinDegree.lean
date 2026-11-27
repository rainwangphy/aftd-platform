import AFTD.Prelude

/-!
# op1957_induced_complement_min_degree

Topic: graphs   Node: 653d13cb84fa

Provenance: helper lemma. OP-1957 independence-number reduction

Deleting a set I from a finite graph of minimum degree at least d+|I| leaves an induced graph of minimum degree at least d.
-/

set_option maxHeartbeats 1500000

theorem op1957_induced_complement_min_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) (d : ℕ)
    (hdegree : ∀ v, d+I.card ≤ (G.neighborFinset v).card) :
    ∀ v : {v : V | v ∉ I}, d ≤ ((G.induce {v | v ∉ I}).neighborFinset v).card := by
  classical
  intro v
  let S : Set V := {v | v ∉ I}
  have hS : S.toFinset = Finset.univ \ I := by
    ext w
    simp [S]
  have hmap := G.map_neighborFinset_induce (s:=S) v
  have hh := congrArg Finset.card hmap
  simp only [Finset.card_map] at hh
  rw [hS] at hh
  have heq : G.neighborFinset v.val ∩ (Finset.univ \ I) = G.neighborFinset v.val \ I := by
    ext w; simp
  rw [heq] at hh
  have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset v.val) I
  have hcap : (G.neighborFinset v.val ∩ I).card ≤ I.card := Finset.card_le_card Finset.inter_subset_right
  have hd := hdegree v.val
  change d ≤ ((G.induce S).neighborFinset v).card
  omega
