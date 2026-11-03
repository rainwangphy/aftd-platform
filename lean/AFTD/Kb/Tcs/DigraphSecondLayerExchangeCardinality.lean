import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSecondLayerQuasikernelExchange

/-!
# digraph_second_layer_exchange_cardinality

Topic: graphs   Node: aebd674264e0

Provenance: helper lemma. Auxiliary lemma for the OP-337 campaign; Discrete Mathematics 346 (2023), 113435, Observation 4, with arcs reversed.

In the second-layer exchange, if the original quasi-kernel is minimum then the second-layer set attacks at most its own number of original members.
-/

theorem digraph_second_layer_exchange_cardinality
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (Q K : Finset α)
    (hindQ : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v)
    (hindK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v)
    (hKQ : Disjoint K Q)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, ¬ D.Adj q k)
    (hcover : ∀ y, y ∉ Q → (¬ ∃ q ∈ Q, D.Adj q y) →
      ∃ k ∈ K, k = y ∨ D.Adj k y ∨ ∃ w, D.Adj k w ∧ D.Adj w y)
    (hmin : ∀ P : Finset α,
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) →
      (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) →
      Q.card ≤ P.card) :
    (Q.filter fun q => ∃ k ∈ K, D.Adj k q).card ≤ K.card := by
  classical
  let R := Q.filter fun q => ¬ ∃ k ∈ K, D.Adj k q
  have hdisj : Disjoint R K := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxK
    exact (Finset.disjoint_left.mp hKQ) hxK (Finset.mem_filter.mp hxR).1
  have h := digraph_second_layer_quasikernel_exchange D Q K hindQ hindK hKQ hQK hcover
  change (∀ u ∈ R ∪ K, ∀ v ∈ R ∪ K, u ≠ v → ¬ D.Adj u v) ∧
    (∀ v, ∃ u ∈ R ∪ K, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) at h
  have hbound := hmin (R ∪ K) h.1 h.2
  rw [Finset.card_union_of_disjoint hdisj] at hbound
  have hsplit := Finset.card_filter_add_card_filter_not (s := Q) (fun q => ∃ k ∈ K, D.Adj k q)
  change (Q.filter fun q => ∃ k ∈ K, D.Adj k q).card + R.card = Q.card at hsplit
  omega
