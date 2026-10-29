import AFTD.Prelude

/-!
# finite_partition_permutation_of_fiber_card

Topic: graphs   Node: cb364b59f0b7

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

For two maps p,b from Fin n to Fin q whose corresponding fibers have equal cardinality, there is a permutation sigma of Fin n such that p(sigma v)=b(v) for every vertex.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem finite_partition_permutation_of_fiber_card {n q : ℕ} (p b : Fin n → Fin q)
    (h : ∀ t, ((Finset.univ : Finset (Fin n)).filter (fun v => p v = t)).card =
      ((Finset.univ : Finset (Fin n)).filter (fun v => b v = t)).card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ v, p (σ v) = b v := by
  classical
  let E : ∀ t : Fin q, {v // b v = t} ≃ {v // p v = t} := fun t =>
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using (h t).symm)
  exact ⟨Equiv.ofFiberEquiv E,Equiv.ofFiberEquiv_map E⟩
