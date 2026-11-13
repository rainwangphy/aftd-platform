import AFTD.Prelude

/-!
# forest_symmetric_fiber_equiv

Topic: online_algorithms   Node: 502e0cf05e12

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

Any finite uniform integer law with symmetric value counts admits a permutation that negates every value.
-/

theorem forest_symmetric_fiber_equiv (α : Type) [Fintype α] (X : α → ℤ)
    (hs : ∀ z : ℤ, (Finset.univ.filter (fun a => X a = z)).card =
      (Finset.univ.filter (fun a => X a = -z)).card) :
    ∃ e : α ≃ α, ∀ a, X (e a) = -X a := by
  classical
  let fiber (z : ℤ) : {a // X a = z} ≃ {a // -X a = z} :=
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_subtype, neg_eq_iff_eq_neg] using hs z)
  let e : α ≃ α := Equiv.ofFiberEquiv fiber
  refine ⟨e, ?_⟩
  intro a
  have h : -X (e a) = X a := Equiv.ofFiberEquiv_map fiber a
  omega
