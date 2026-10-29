import AFTD.Prelude

/-!
# multiset_sum_apply

Topic: combinatorics   Node: 45771f76d9f1

Provenance: helper lemma. arXiv:2610.35819 Section 4

For any finite family of additive commutative monoids G_i over i in Fin t, any multiset W of dependent functions x : (i : Fin t) -> G_i, and any coordinate j in Fin t, the sum of the projections of the elements of W to coordinate j equals the j-th coordinate of the sum of W.
-/

/-- Pointwise coordinate evaluation commutes with multiset sum of functions. -/
lemma multiset_sum_apply {t : ℕ} {G : Fin t → Type*}
    [∀ i, AddCommMonoid (G i)] (W : Multiset ((i : Fin t) → G i)) (j : Fin t) :
    (W.map (fun x => x j)).sum = W.sum j := (map_multiset_sum (Pi.evalAddMonoidHom G j) W).symm
