import AFTD.Prelude

/-!
# digraph_second_layer_quasikernel_exchange

Topic: graphs   Node: 16b93e9ae1bc

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; Discrete Mathematics 346 (2023), 113435, Observation 4, with arcs reversed.

An independent second-layer set that reaches the vertices outside a set and its first out-neighborhood can replace the original set members it attacks, producing a quasi-kernel.
-/

theorem digraph_second_layer_quasikernel_exchange
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q K : Finset α)
    (hindQ : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hindK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v)
    (hKQ : Disjoint K Q)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, ¬ D.Adj q k)
    (hcover : ∀ y, y ∉ Q → (¬ ∃ q ∈ Q, D.Adj q y) →
      ∃ k ∈ K, k = y ∨ D.Adj k y ∨ ∃ w, D.Adj k w ∧ D.Adj w y) :
    let R := Q.filter fun q => ¬ ∃ k ∈ K, D.Adj k q
    let P := R ∪ K
    (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) ∧
    (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) := by
  classical
  dsimp only
  constructor
  · intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · exact hindQ u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv
    · exact hQK u (Finset.mem_filter.mp hu).1 v hv
    · exact fun hadj => (Finset.mem_filter.mp hv).2 ⟨u,hu,hadj⟩
    · exact hindK u hu v hv huv
  · intro v
    by_cases hvQ : v ∈ Q
    · by_cases hvR : v ∈ Q.filter (fun q => ¬ ∃ k ∈ K, D.Adj k q)
      · exact ⟨v,Finset.mem_union_left _ hvR,Or.inl rfl⟩
      · have hex : ∃ k ∈ K, D.Adj k v := by
          by_contra hn
          exact hvR (Finset.mem_filter.mpr ⟨hvQ,hn⟩)
        obtain ⟨k,hk,hkv⟩ := hex
        exact ⟨k,Finset.mem_union_right _ hk,Or.inr (Or.inl hkv)⟩
    · by_cases hex : ∃ q ∈ Q, D.Adj q v
      · obtain ⟨q,hq,hqv⟩ := hex
        by_cases hqR : q ∈ Q.filter (fun a => ¬ ∃ k ∈ K, D.Adj k a)
        · exact ⟨q,Finset.mem_union_left _ hqR,Or.inr (Or.inl hqv)⟩
        · have hkq : ∃ k ∈ K, D.Adj k q := by
            by_contra hn
            exact hqR (Finset.mem_filter.mpr ⟨hq,hn⟩)
          obtain ⟨k,hk,hkq'⟩ := hkq
          exact ⟨k,Finset.mem_union_right _ hk,Or.inr (Or.inr ⟨q,hkq',hqv⟩)⟩
      · obtain ⟨k,hk,hd⟩ := hcover v hvQ hex
        exact ⟨k,Finset.mem_union_right _ hk,hd⟩

-- For minimum Q, the second-layer selection cannot attack more members
-- of Q than it contains itself.
